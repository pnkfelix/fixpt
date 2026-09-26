//! The heap: a flat word array, a Cheney semispace collector, and the
//! allocation and accessor surface everything else in `fixpt` is built on.
//!
//! # The one invariant that matters
//!
//! **A `Value` stays valid across allocation, and only across allocation.**
//!
//! Allocation never moves an existing object. When the active semispace runs
//! out, the heap *grows* — it reallocates the backing `Vec` and copies the
//! active half to the new base — and because every reference is an offset
//! *relative to the semispace base*, not an absolute index or a pointer, every
//! live `Value` keeps its meaning. Nothing is traced, so no root set is needed.
//!
//! Objects move only in [`Heap::collect`], which the execution engine calls at
//! its own safepoints and hands its complete root set. So the classic embedding
//! hazard — a `Value` sitting in a Rust local going stale because some
//! unrelated allocation triggered a collection — cannot arise: allocation is
//! not a safepoint.
//!
//! `--features gc-stress` makes every `collect` call actually collect (rather
//! than checking a threshold first), so the moving path is exercised on every
//! safepoint in the test suite rather than only when a heap happens to fill up.

use crate::layout;
use crate::value::{
    ObjType, TAG_BLOBLET, TAG_FORWARD, TAG_HEADER, TAG_MASK, TAG_TRAILER, Value, header_bytes, header_is_large,
    header_kind, is_extension, is_header, make_header, make_large_header,
};
use std::collections::HashMap;

/// What a main header says, with a large header's extension read too.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Head {
    pub kind: u8,
    /// `F`, the number of tagged fields.
    pub fields: usize,
    /// `B`, the suffix length in bytes.
    pub bytes: usize,
    /// Words before the main header that belong to the object: 1 for a large
    /// header's extension, else 0.
    pub pre: usize,
    pub fields_frozen: bool,
    pub suffix_frozen: bool,
}

impl Head {
    /// Words after the main header: fields, then the suffix padded to a word.
    #[inline]
    pub fn payload_words(&self) -> usize {
        self.fields + self.bytes.div_ceil(8)
    }
    /// The whole object, extension and header included.
    #[inline]
    pub fn size(&self) -> usize {
        self.pre + 1 + self.payload_words()
    }
}

/// Read the head of the object whose main header is at `at` in `mem`.
#[inline]
fn read_head(mem: &[u64], at: usize) -> Head {
    let h = mem[at];
    debug_assert!(is_header(h) && !is_extension(h), "no main header at {at}");
    let large = header_is_large(h);
    let fields = if large {
        layout::X_FIELDS.get(mem[at - 1]) as usize
    } else {
        layout::H_FIELDS.get(h) as usize
    };
    Head {
        kind: header_kind(h),
        fields,
        bytes: header_bytes(h),
        pre: large as usize,
        fields_frozen: layout::H_FIELDS_FROZEN.get(h) != 0,
        suffix_frozen: layout::H_SUFFIX_FROZEN.get(h) != 0,
    }
}

/// From a bloblet's suffix start `p` in `mem`, the index of its main header:
/// by its trailer if it has one, else by the backward scan the invariants
/// make sound (`docs/object-model.md`). A forwarding pointer at `p - 1`
/// means the collector has been here already, and is returned as `Err` with
/// its target: where the main header went, relative to to-space.
#[inline]
fn find_main(mem: &[u64], p: usize) -> Result<usize, usize> {
    let w = mem[p - 1];
    match w & TAG_MASK {
        TAG_FORWARD => Err(Value(w).index()),
        TAG_TRAILER => Ok(p - 1 - layout::T_DISTANCE.get(w) as usize),
        TAG_HEADER => Ok(p - 1),
        _ => {
            let mut k = p - 1;
            while mem[k] & TAG_MASK != TAG_HEADER {
                k -= 1;
            }
            Ok(k)
        }
    }
}

/// Why a bloblet operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlobletError {
    NoSuchField(usize),
    /// Field −1 of a bloblet with a trailer is the trailer, which only the
    /// runtime writes.
    Trailer,
    FieldsFrozen,
    SuffixFrozen,
    NoSuchByte(usize),
    /// Only a value may be stored in a field: never a trailer, header or
    /// forwarding word.
    NotAValue,
}

impl std::fmt::Display for BlobletError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BlobletError::NoSuchField(k) => write!(f, "the bloblet has no field -{k}"),
            BlobletError::Trailer => f.write_str("field -1 is the bloblet's trailer, which only the runtime writes"),
            BlobletError::FieldsFrozen => f.write_str("the bloblet's fields are frozen"),
            BlobletError::SuffixFrozen => f.write_str("the bloblet's suffix is frozen"),
            BlobletError::NoSuchByte(i) => write!(f, "the bloblet's suffix has no byte {i}"),
            BlobletError::NotAValue => f.write_str("only a value can be stored in a field"),
        }
    }
}

/// Words in each semispace at startup. Grows on demand; never shrinks.
const DEFAULT_SEMI_WORDS: usize = 1 << 16;

/// Collect when the active semispace is at least this full at a safepoint.
const COLLECT_THRESHOLD: f64 = 0.75;

pub struct Heap {
    /// `2 * semi` words: the two semispaces back to back.
    mem: Vec<u64>,
    /// Base of the active semispace within `mem` — `0` or `semi`.
    active: usize,
    semi: usize,
    /// Next free word, *relative to `active`*. Also the live-data size.
    top: usize,

    /// Explicit roots held by native code across a safepoint.
    roots: Vec<Value>,
    /// While positive, [`maybe_collect`](Heap::maybe_collect) does nothing and
    /// the heap grows instead. For native code that holds `Value`s outside any
    /// root set across a call into Scheme — the macro expander, calling a
    /// transformer while its half-built program holds constants. Growing
    /// never moves anything, so those `Value`s stay valid.
    inhibited: u32,
    /// Global variable slots, indexed by a symbol's global-slot field.
    globals: Vec<Value>,
    /// Interned symbols. Position is the symbol's identity; the `Value`s here
    /// are ordinary roots and get forwarded like any other.
    symbols: Vec<Value>,
    /// Rust-side name lookup. Keys are plain `String`s, so a collection cannot
    /// invalidate them.
    symbol_index: HashMap<String, u32>,

    pub gc_count: u64,
    pub words_copied: u64,
}

impl Default for Heap {
    fn default() -> Self {
        Heap::new()
    }
}

impl Heap {
    pub fn new() -> Heap {
        Heap::with_semispace(DEFAULT_SEMI_WORDS)
    }

    pub fn with_semispace(semi: usize) -> Heap {
        let semi = semi.max(1024);
        Heap {
            mem: vec![0; semi * 2],
            active: 0,
            semi,
            top: 0,
            roots: Vec::new(),
            inhibited: 0,
            globals: Vec::new(),
            symbols: Vec::new(),
            symbol_index: HashMap::new(),
            gc_count: 0,
            words_copied: 0,
        }
    }

    // ------------------------------------------------------------------ stats
    /// Live words in the active semispace.
    #[inline]
    pub fn used(&self) -> usize {
        self.top
    }
    #[inline]
    pub fn capacity(&self) -> usize {
        self.semi
    }
    #[inline]
    pub fn symbol_count(&self) -> usize {
        self.symbols.len()
    }
    #[inline]
    pub fn global_count(&self) -> usize {
        self.globals.len()
    }

    // ------------------------------------------------------------ raw word I/O
    #[inline]
    fn word(&self, rel: usize) -> u64 {
        self.mem[self.active + rel]
    }
    #[inline]
    fn set_word(&mut self, rel: usize, w: u64) {
        self.mem[self.active + rel] = w;
    }
    #[inline]
    pub fn slot(&self, rel: usize) -> Value {
        Value(self.word(rel))
    }
    #[inline]
    pub fn set_slot(&mut self, rel: usize, v: Value) {
        self.set_word(rel, v.raw());
    }

    // ------------------------------------------------------------- allocation
    /// Reserve `n` words. Never moves anything; grows the heap if needed.
    fn bump(&mut self, n: usize) -> usize {
        if self.top + n > self.semi {
            self.grow(self.top + n);
        }
        let at = self.top;
        self.top += n;
        at
    }

    /// Grow both semispaces to hold at least `need` words, preserving every
    /// existing `Value` — relative offsets are unchanged by construction.
    fn grow(&mut self, need: usize) {
        let mut semi = self.semi;
        while semi < need {
            semi *= 2;
        }
        let mut fresh = vec![0u64; semi * 2];
        fresh[..self.top].copy_from_slice(&self.mem[self.active..self.active + self.top]);
        self.mem = fresh;
        self.active = 0;
        self.semi = semi;
    }

    /// Allocate an object with `len` payload words, all initialised to `fill`.
    ///
    /// These are the older, header-pointed objects. Each is laid out as a
    /// bloblet, but its pointer (tag `object`) points at the header rather
    /// than the suffix. A traced type's payload is `len` fields, and a raw
    /// type's is `8 * len` suffix bytes. Either way the payload starts one
    /// word after the main header, which is all the accessors below rely on.
    pub fn alloc(&mut self, ty: ObjType, len: usize, fill: Value) -> Value {
        let (fields, bytes) = if ty.payload_is_scanned() { (len, 0) } else { (0, len * 8) };
        assert!(bytes as u64 <= layout::H_BYTES.max(), "an object's suffix is limited to 4 GiB");
        let main = self.put_header(ty as u8, fields, bytes);
        for i in 0..len {
            self.set_word(main + 1 + i, fill.raw());
        }
        Value::object(main)
    }

    /// Reserve an object of `fields` fields and `bytes` suffix bytes and write
    /// its header, with an extension word first if `fields` needs one.
    /// Returns the main header's index. The payload is left as it was.
    fn put_header(&mut self, kind: u8, fields: usize, bytes: usize) -> usize {
        let payload = fields + bytes.div_ceil(8);
        if fields as u64 > layout::H_FIELDS.max() {
            let at = self.bump(payload + 2);
            let (x, h) = make_large_header(kind, fields, bytes);
            self.set_word(at, x);
            self.set_word(at + 1, h);
            at + 1
        } else {
            let at = self.bump(payload + 1);
            self.set_word(at, make_header(kind, fields, bytes));
            at
        }
    }

    pub fn cons(&mut self, car: Value, cdr: Value) -> Value {
        let at = self.bump(2);
        self.set_word(at, car.raw());
        self.set_word(at + 1, cdr.raw());
        Value::pair(at)
    }

    // -------------------------------------------------------------- accessors
    #[inline]
    pub fn car(&self, p: Value) -> Value {
        debug_assert!(p.is_pair());
        self.slot(p.index())
    }
    #[inline]
    pub fn cdr(&self, p: Value) -> Value {
        debug_assert!(p.is_pair());
        self.slot(p.index() + 1)
    }
    #[inline]
    pub fn set_car(&mut self, p: Value, v: Value) {
        debug_assert!(p.is_pair());
        self.set_slot(p.index(), v);
    }
    #[inline]
    pub fn set_cdr(&mut self, p: Value, v: Value) {
        debug_assert!(p.is_pair());
        self.set_slot(p.index() + 1, v);
    }

    #[inline]
    fn header_of(&self, o: Value) -> u64 {
        debug_assert!(o.is_object());
        let h = self.word(o.index());
        debug_assert!(is_header(h), "object {o:?} does not point at a header");
        h
    }
    /// The type of a heap object. `None` for anything that is not an object.
    pub fn obj_type(&self, v: Value) -> Option<ObjType> {
        if !v.is_object() {
            return None;
        }
        ObjType::from_code(header_kind(self.header_of(v)) as u16)
    }
    pub fn is_a(&self, v: Value, ty: ObjType) -> bool {
        self.obj_type(v) == Some(ty)
    }
    /// Payload length in words.
    #[inline]
    pub fn obj_len(&self, o: Value) -> usize {
        debug_assert!(is_header(self.header_of(o)));
        read_head(&self.mem, self.active + o.index()).payload_words()
    }
    #[inline]
    pub fn obj_ref(&self, o: Value, i: usize) -> Value {
        debug_assert!(i < self.obj_len(o), "payload index {i} out of range");
        self.slot(o.index() + 1 + i)
    }
    #[inline]
    pub fn obj_set(&mut self, o: Value, i: usize, v: Value) {
        debug_assert!(i < self.obj_len(o), "payload index {i} out of range");
        self.set_slot(o.index() + 1 + i, v);
    }
    #[inline]
    fn obj_word(&self, o: Value, i: usize) -> u64 {
        self.word(o.index() + 1 + i)
    }
    #[inline]
    fn obj_set_word(&mut self, o: Value, i: usize, w: u64) {
        self.set_word(o.index() + 1 + i, w)
    }

    // ------------------------------------------------------------ constructors
    pub fn make_vector(&mut self, len: usize, fill: Value) -> Value {
        self.alloc(ObjType::Vector, len, fill)
    }

    pub fn vector_from(&mut self, items: &[Value]) -> Value {
        let v = self.alloc(ObjType::Vector, items.len(), Value::UNSPECIFIED);
        for (i, x) in items.iter().enumerate() {
            self.obj_set(v, i, *x);
        }
        v
    }

    pub fn list_from(&mut self, items: &[Value]) -> Value {
        let mut acc = Value::NULL;
        for x in items.iter().rev() {
            acc = self.cons(*x, acc);
        }
        acc
    }

    /// Collect a proper list into a `Vec`. Returns `None` for an improper list.
    pub fn list_to_vec(&self, mut v: Value) -> Option<Vec<Value>> {
        let mut out = Vec::new();
        while v.is_pair() {
            out.push(self.car(v));
            v = self.cdr(v);
        }
        if v.is_null() { Some(out) } else { None }
    }

    pub fn make_flonum(&mut self, x: f64) -> Value {
        let o = self.alloc(ObjType::Flonum, 1, Value::fixnum(0));
        self.obj_set_word(o, 0, x.to_bits());
        o
    }
    pub fn flonum_value(&self, o: Value) -> f64 {
        debug_assert!(self.is_a(o, ObjType::Flonum));
        f64::from_bits(self.obj_word(o, 0))
    }

    /// Strings are UTF-32 internally, two code points per word, so `string-ref`
    /// is O(1). UTF-8 would make the obvious character loop quadratic.
    pub fn make_string(&mut self, s: &str) -> Value {
        let chars: Vec<char> = s.chars().collect();
        self.string_from_chars(&chars)
    }

    pub fn string_from_chars(&mut self, chars: &[char]) -> Value {
        let words = 1 + chars.len().div_ceil(2);
        let o = self.alloc(ObjType::String, words, Value::fixnum(0));
        self.obj_set_word(o, 0, chars.len() as u64);
        for (i, c) in chars.iter().enumerate() {
            self.string_set(o, i, *c);
        }
        o
    }

    #[inline]
    pub fn string_len(&self, o: Value) -> usize {
        debug_assert!(self.is_a(o, ObjType::String));
        self.obj_word(o, 0) as usize
    }
    #[inline]
    pub fn string_ref(&self, o: Value, i: usize) -> char {
        debug_assert!(i < self.string_len(o));
        let w = self.obj_word(o, 1 + i / 2);
        let half = if i.is_multiple_of(2) {
            w & 0xffff_ffff
        } else {
            w >> 32
        };
        char::from_u32(half as u32).expect("string holds valid code points")
    }
    pub fn string_set(&mut self, o: Value, i: usize, c: char) {
        debug_assert!(i < self.string_len(o));
        let wi = 1 + i / 2;
        let w = self.obj_word(o, wi);
        let w = if i.is_multiple_of(2) {
            (w & 0xffff_ffff_0000_0000) | (c as u64)
        } else {
            (w & 0x0000_0000_ffff_ffff) | ((c as u64) << 32)
        };
        self.obj_set_word(o, wi, w);
    }
    pub fn string_to_rust(&self, o: Value) -> String {
        (0..self.string_len(o))
            .map(|i| self.string_ref(o, i))
            .collect()
    }

    pub fn make_bytevector(&mut self, bytes: &[u8]) -> Value {
        let words = 1 + bytes.len().div_ceil(8);
        let o = self.alloc(ObjType::Bytevector, words, Value::fixnum(0));
        self.obj_set_word(o, 0, bytes.len() as u64);
        for (i, b) in bytes.iter().enumerate() {
            self.bytevector_set(o, i, *b);
        }
        o
    }
    #[inline]
    pub fn bytevector_len(&self, o: Value) -> usize {
        debug_assert!(self.is_a(o, ObjType::Bytevector));
        self.obj_word(o, 0) as usize
    }
    #[inline]
    pub fn bytevector_ref(&self, o: Value, i: usize) -> u8 {
        debug_assert!(i < self.bytevector_len(o));
        (self.obj_word(o, 1 + i / 8) >> ((i % 8) * 8)) as u8
    }
    pub fn bytevector_set(&mut self, o: Value, i: usize, b: u8) {
        debug_assert!(i < self.bytevector_len(o));
        let wi = 1 + i / 8;
        let shift = (i % 8) * 8;
        let w = (self.obj_word(o, wi) & !(0xffu64 << shift)) | ((b as u64) << shift);
        self.obj_set_word(o, wi, w);
    }
    /// Read the `i`th 32-bit word. Bytecode is stored in a bytevector, and a
    /// word read is on the VM's hottest path, so it goes straight at the heap
    /// word rather than through four byte reads.
    #[inline]
    pub fn bytevector_u32(&self, o: Value, i: usize) -> u32 {
        debug_assert!(4 * i + 4 <= self.bytevector_len(o));
        (self.obj_word(o, 1 + i / 2) >> ((i % 2) * 32)) as u32
    }

    pub fn bytevector_to_vec(&self, o: Value) -> Vec<u8> {
        (0..self.bytevector_len(o))
            .map(|i| self.bytevector_ref(o, i))
            .collect()
    }

    pub fn make_box(&mut self, v: Value) -> Value {
        self.alloc(ObjType::Box, 1, v)
    }
    #[inline]
    pub fn unbox(&self, b: Value) -> Value {
        debug_assert!(self.is_a(b, ObjType::Box));
        self.obj_ref(b, 0)
    }
    #[inline]
    pub fn set_box(&mut self, b: Value, v: Value) {
        debug_assert!(self.is_a(b, ObjType::Box));
        self.obj_set(b, 0, v);
    }

    // ----------------------------------------------------------------- symbols
    /// Symbol payload: `[name:String, hash, global-slot]`. The global slot is
    /// allocated eagerly so a global reference is one array index, not a lookup.
    pub fn intern(&mut self, name: &str) -> Value {
        if let Some(&i) = self.symbol_index.get(name) {
            return self.symbols[i as usize];
        }
        let s = self.make_string(name);
        let sym = self.alloc(ObjType::Symbol, 3, Value::fixnum(0));
        self.obj_set(sym, 0, s);
        self.obj_set(sym, 1, Value::fixnum(fnv1a(name) as i64 & i64::MAX));
        let slot = self.globals.len();
        self.globals.push(Value::UNBOUND);
        self.obj_set(sym, 2, Value::fixnum(slot as i64));
        let idx = self.symbols.len() as u32;
        self.symbols.push(sym);
        self.symbol_index.insert(name.to_string(), idx);
        sym
    }

    /// A symbol with this name that is `eq?` to no other — not even to the
    /// interned symbol of the same name. It has no global slot: it exists to
    /// carry an identifier's identity into Scheme code (a procedural macro's
    /// input) and back, never to name a variable at run time.
    pub fn make_uninterned_symbol(&mut self, name: &str) -> Value {
        let s = self.make_string(name);
        let sym = self.alloc(ObjType::Symbol, 3, Value::fixnum(0));
        self.obj_set(sym, 0, s);
        self.obj_set(sym, 1, Value::fixnum(fnv1a(name) as i64 & i64::MAX));
        self.obj_set(sym, 2, Value::fixnum(-1));
        sym
    }

    pub fn is_interned_symbol(&self, sym: Value) -> bool {
        self.is_a(sym, ObjType::Symbol) && self.obj_ref(sym, 2).as_fixnum() >= 0
    }

    /// Look up an already-interned symbol without allocating. Useful when a
    /// `&Heap` is all that is available, e.g. after loading an image.
    pub fn intern_existing(&self, name: &str) -> Option<Value> {
        self.symbol_index
            .get(name)
            .map(|&i| self.symbols[i as usize])
    }

    pub fn symbol_name(&self, sym: Value) -> String {
        debug_assert!(self.is_a(sym, ObjType::Symbol));
        self.string_to_rust(self.obj_ref(sym, 0))
    }
    #[inline]
    pub fn symbol_global_slot(&self, sym: Value) -> usize {
        debug_assert!(self.is_a(sym, ObjType::Symbol));
        self.obj_ref(sym, 2).as_fixnum() as usize
    }

    #[inline]
    pub fn global(&self, slot: usize) -> Value {
        self.globals[slot]
    }
    #[inline]
    pub fn set_global(&mut self, slot: usize, v: Value) {
        self.globals[slot] = v;
    }

    /// Hold off collection until the matching [`allow_collection`].
    ///
    /// [`allow_collection`]: Heap::allow_collection
    pub fn inhibit_collection(&mut self) {
        self.inhibited += 1;
    }

    pub fn allow_collection(&mut self) {
        self.inhibited -= 1;
    }

    // ------------------------------------------------------------ native roots
    /// Root `v` for the duration of a native operation that spans a safepoint.
    /// Returns the depth to unwind to.
    pub fn push_root(&mut self, v: Value) -> usize {
        self.roots.push(v);
        self.roots.len() - 1
    }
    pub fn root_at(&self, depth: usize) -> Value {
        self.roots[depth]
    }
    pub fn set_root_at(&mut self, depth: usize, v: Value) {
        self.roots[depth] = v;
    }
    pub fn pop_roots_to(&mut self, depth: usize) {
        self.roots.truncate(depth);
    }

    // -------------------------------------------------------------- collection
    /// Collect if the heap warrants it. Call only at an engine safepoint, with
    /// every live `Value` reachable from `extra_roots` or the heap's own roots.
    pub fn maybe_collect(&mut self, extra_roots: &mut [&mut [Value]]) {
        if self.inhibited > 0 {
            return;
        }
        let full = self.top as f64 >= self.semi as f64 * COLLECT_THRESHOLD;
        if cfg!(feature = "gc-stress") || full {
            self.collect(extra_roots);
        }
    }

    /// Cheney semispace copy. Compacts, which is also what makes a dumped image
    /// contiguous and relocation-free.
    pub fn collect(&mut self, extra_roots: &mut [&mut [Value]]) {
        let from = self.active;
        let to = if self.active == 0 { self.semi } else { 0 };

        // `scan` and `free` are relative to `to`.
        let mut scan = 0usize;
        let mut free = 0usize;

        // Forward every root. Done by hand rather than through a closure so the
        // borrow checker stays out of the way in the hot loop.
        macro_rules! fwd {
            ($v:expr) => {{
                let v = $v;
                if v.is_ref() {
                    Self::copy_out(&mut self.mem, from, to, &mut free, v)
                } else {
                    v
                }
            }};
        }

        for i in 0..self.roots.len() {
            self.roots[i] = fwd!(self.roots[i]);
        }
        for i in 0..self.globals.len() {
            self.globals[i] = fwd!(self.globals[i]);
        }
        for i in 0..self.symbols.len() {
            self.symbols[i] = fwd!(self.symbols[i]);
        }
        for slice in extra_roots.iter_mut() {
            for v in slice.iter_mut() {
                *v = fwd!(*v);
            }
        }

        // Scan to-space linearly. The first word at a boundary is either a
        // header (an object follows) or an ordinary Value (a pair cell follows);
        // see `value.rs` on why tag 110 is reserved to make this unambiguous.
        while scan < free {
            let w = self.mem[to + scan];
            if is_header(w) {
                // The collector needs only `F` and `B`: trace the fields, skip
                // the suffix. It never asks what kind of object this is.
                let main = to + scan + is_extension(w) as usize;
                let head = read_head(&self.mem, main);
                for i in 0..head.fields {
                    let at = main + 1 + i;
                    let v = Value(self.mem[at]);
                    if v.is_ref() {
                        let n = Self::copy_out(&mut self.mem, from, to, &mut free, v);
                        self.mem[at] = n.raw();
                    }
                }
                scan += head.size();
            } else {
                for i in 0..2 {
                    let at = to + scan + i;
                    let v = Value(self.mem[at]);
                    if v.is_ref() {
                        let n = Self::copy_out(&mut self.mem, from, to, &mut free, v);
                        self.mem[at] = n.raw();
                    }
                }
                scan += 2;
            }
        }

        self.active = to;
        self.top = free;
        self.gc_count += 1;
        self.words_copied += free as u64;

        // Keep some headroom, so we are not collecting on every safepoint.
        if self.top as f64 > self.semi as f64 * COLLECT_THRESHOLD {
            self.grow(self.top * 2);
        }
    }

    /// Copy one object from from-space to to-space if it is not already there,
    /// leaving a forwarding pointer behind. Returns the to-space reference.
    ///
    /// A forwarding pointer always records where the object's *main header*
    /// went, relative to `to`, whichever kind of pointer found it.
    fn copy_out(mem: &mut [u64], from: usize, to: usize, free: &mut usize, v: Value) -> Value {
        if v.is_pair() {
            let src = from + v.index();
            let first = Value(mem[src]);
            if first.is_forward() {
                return Value::pair(first.index());
            }
            let dst_rel = *free;
            mem[to + dst_rel] = mem[src];
            mem[to + dst_rel + 1] = mem[src + 1];
            *free += 2;
            mem[src] = Value::forward(dst_rel).raw();
            return Value::pair(dst_rel);
        }
        if v.is_object() {
            return Value::object(Self::copy_object(mem, from + v.index(), to, free));
        }
        // A bloblet pointer, at the start of the suffix. Find the header, by
        // the trailer or the backward scan, and copy as any object. Leave a
        // second forward just before the suffix, so that the next pointer to
        // this bloblet finds it in one step, trailer or not.
        debug_assert!(v.tag() == TAG_BLOBLET);
        let p = from + v.index();
        let new_main = match find_main(mem, p) {
            Err(done) => done,
            Ok(main) => {
                let new_main = Self::copy_object(mem, main, to, free);
                if p - 1 != main {
                    mem[p - 1] = Value::forward(new_main).raw();
                }
                new_main
            }
        };
        let head = read_head(mem, to + new_main);
        Value::bloblet(new_main + 1 + head.fields)
    }

    /// Copy the object whose main header is at `main` (in from-space), unless
    /// it has been already. Returns its main header's new index, relative to
    /// `to`.
    fn copy_object(mem: &mut [u64], main: usize, to: usize, free: &mut usize) -> usize {
        let first = Value(mem[main]);
        if first.is_forward() {
            return first.index();
        }
        let head = read_head(mem, main);
        let start = main - head.pre;
        let words = head.size();
        mem.copy_within(start..start + words, to + *free);
        let new_main = *free + head.pre;
        *free += words;
        mem[main] = Value::forward(new_main).raw();
        new_main
    }

    // ------------------------------------------------------- image support
    /// The live prefix of the active semispace, ready to be written out as-is.
    pub fn live_words(&self) -> &[u64] {
        &self.mem[self.active..self.active + self.top]
    }
    pub fn globals_slice(&self) -> &[Value] {
        &self.globals
    }
    pub fn symbols_slice(&self) -> &[Value] {
        &self.symbols
    }

    /// Rebuild a heap from a dumped image. `words` is the live region; the
    /// references inside it are already base-relative, so nothing is relocated.
    pub fn from_image(
        words: &[u64],
        globals: Vec<Value>,
        symbols: Vec<Value>,
    ) -> Result<Heap, String> {
        let mut semi = DEFAULT_SEMI_WORDS;
        while semi < words.len() {
            semi *= 2;
        }
        let mut heap = Heap::with_semispace(semi);
        heap.mem[..words.len()].copy_from_slice(words);
        heap.top = words.len();
        heap.globals = globals;
        heap.symbols = symbols;
        heap.symbol_index = HashMap::with_capacity(heap.symbols.len());
        for i in 0..heap.symbols.len() {
            let name = heap.symbol_name(heap.symbols[i]);
            heap.symbol_index.insert(name, i as u32);
        }
        Ok(heap)
    }

    /// Walk the whole live region and check it is structurally sound. Used by
    /// `fixpt image verify`, after every collection under `gc-stress`, and in
    /// tests — it is the cheapest way to catch a scan that desynchronised.
    pub fn verify(&self) -> Result<(), String> {
        let mut scan = 0usize;
        while scan < self.top {
            let w = self.word(scan);
            if is_header(w) {
                let main = scan + is_extension(w) as usize;
                if main >= self.top || !is_header(self.word(main)) || is_extension(self.word(main)) {
                    return Err(format!("the extension word at {scan} is not followed by a main header"));
                }
                if is_extension(w) != header_is_large(self.word(main)) {
                    return Err(format!("the header at {main} disagrees with its extension word"));
                }
                let head = read_head(&self.mem, self.active + main);
                if scan + head.size() > self.top {
                    return Err(format!("object at {scan} runs past the end of the heap"));
                }
                for i in 0..head.fields {
                    let v = self.slot(main + 1 + i);
                    if v.tag() == TAG_TRAILER {
                        if i + 1 != head.fields {
                            return Err(format!("a trailer at word {} is not the last field", main + 1 + i));
                        }
                        let dist = layout::T_DISTANCE.get(v.raw()) as usize;
                        if dist != head.fields {
                            return Err(format!("the trailer of the object at {main} says {dist}, not {}", head.fields));
                        }
                    }
                    self.check_ref(v, main)?;
                }
                scan += head.size();
            } else {
                if scan + 2 > self.top {
                    return Err(format!("pair at {scan} runs past the end of the heap"));
                }
                self.check_ref(self.slot(scan), scan)?;
                self.check_ref(self.slot(scan + 1), scan)?;
                scan += 2;
            }
        }
        for (i, g) in self.globals.iter().enumerate() {
            self.check_ref(*g, i)
                .map_err(|e| format!("global {i}: {e}"))?;
        }
        for (i, s) in self.symbols.iter().enumerate() {
            if !self.is_a(*s, ObjType::Symbol) {
                return Err(format!("symbol table entry {i} is not a symbol"));
            }
        }
        Ok(())
    }

    fn check_ref(&self, v: Value, at: usize) -> Result<(), String> {
        if v.is_forward() {
            return Err(format!(
                "forwarding pointer survived a collection, at word {at}"
            ));
        }
        if v.is_ref() {
            if v.index() >= self.top {
                return Err(format!("dangling reference {v:?} at word {at}"));
            }
            if v.is_object() && (!is_header(self.word(v.index())) || is_extension(self.word(v.index()))) {
                return Err(format!(
                    "object reference {v:?} at word {at} misses its header"
                ));
            }
            if v.is_bloblet() {
                let p = self.active + v.index();
                let main = find_main(&self.mem, p)
                    .map_err(|_| format!("bloblet reference {v:?} at word {at} meets a forwarding pointer"))?;
                let head = read_head(&self.mem, main);
                if main + 1 + head.fields != p {
                    return Err(format!(
                        "bloblet reference {v:?} at word {at} is not at the start of its suffix"
                    ));
                }
            }
            if v.is_pair() && is_header(self.word(v.index())) {
                return Err(format!(
                    "pair reference {v:?} at word {at} lands on a header"
                ));
            }
        }
        Ok(())
    }
}

fn fnv1a(s: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in s.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100_0000_01b3);
    }
    h
}
