//! The heap: a flat word array, a Cheney semispace collector, and the
//! allocation and accessor surface everything else in `fixpt` is built on.
//!
//! # The one invariant that matters
//!
//! **A `Value` stays valid across allocation, and only across allocation.**
//!
//! Allocation never moves an existing object. When the active semispace runs
//! out, the heap *grows*, in place: each semispace has address space of its
//! own, reserved when the heap is made (`fixpt_memmgmt::Words`), so every
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
use std::collections::{HashMap, HashSet};

mod code;
mod regions;
mod young;
pub use regions::REGION_SLOTS;

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
/// The next heap's [`serial`](Heap::serial).
static NEXT_SERIAL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

/// What a weak reference to an object that died becomes.
pub const WEAK_DEAD: Value = Value::fixnum(-1);

/// After a collection has copied everything live out of `from` (the
/// nursery, if `minor`): each of `weak` that pointed there moved on to its
/// object's new place, or, if the object was not copied, [`WEAK_DEAD`].
/// Before `from` is reused, while its forwarding pointers are there.
fn update_weak(mem: &[u64], base: usize, weak: &mut [Value], from: usize, minor: bool) {
    for w in weak.iter_mut() {
        if !w.is_ref() {
            continue;
        }
        let i = w.index() - base;
        let moving = young::is_young(i) || (!minor && (from..from + MAX_SEMI_WORDS).contains(&i));
        if !moving {
            continue;
        }
        *w = if w.is_pair() {
            let first = Value(mem[i]);
            if first.is_forward() { Value::pair(first.index() + base) } else { WEAK_DEAD }
        } else {
            match find_main(mem, i) {
                Err(new_main) => Value::bloblet(new_main + 1 + read_head(mem, new_main).fields + base),
                Ok(_) => WEAK_DEAD,
            }
        };
    }
}

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
/// The most words a semispace may grow to: each has this much address space
/// of its own, reserved when the heap is made, so it grows in place.
const MAX_SEMI_WORDS: usize = 1 << 31;
/// Past the two semispaces, the arenas' area (`regions`), as large; and
/// past that, the reaps', as large again.
const ARENA_BASE: usize = 2 * MAX_SEMI_WORDS;
const ARENA_WORDS: usize = 1 << 31;
const REAP_BASE: usize = ARENA_BASE + ARENA_WORDS;
const REAP_WORDS: usize = 1 << 31;
/// Past the reaps' area, the nursery (`young`): where a generational heap
/// allocates everything first.
const NURSERY_BASE: usize = REAP_BASE + REAP_WORDS;
const NURSERY_MAX: usize = 1 << 30;
/// Last, the code area (`code`): bloblets that never move, collected by
/// marking and sweeping. Last, since native code takes a callee whose code
/// is at or past the code area's start to be native code.
const CODE_BASE: usize = NURSERY_BASE + NURSERY_MAX;
const CODE_WORDS: usize = 1 << 27;
/// The whole of the heap's memory, in words.
const MEM_WORDS: usize = CODE_BASE + CODE_WORDS;
/// How many words the nursery takes before a safepoint collects it: 8 MB.
/// Measured on the front end's self-compile (`docs/performance.md`); from
/// 1M words up the times were about the same.
const DEFAULT_NURSERY_WORDS: usize = 1 << 20;

/// Collect when the active semispace is at least this full at a safepoint.
const COLLECT_THRESHOLD: f64 = 0.75;
/// A semispace is kept at least this many times the data live after a
/// collection.
const LIVE_RATIO: usize = 3;

pub struct Heap {
    /// The two semispaces, `MAX_SEMI_WORDS` apart, and the regions' area
    /// after them, at an address that never changes: each semispace grows
    /// in place, up to that (`fixpt_memmgmt::Words`, committed by the
    /// system as it is first written).
    mem: fixpt_memmgmt::Words,
    /// Where `mem` starts, in words: a Value is an address, and names word
    /// `(address / 8) - base` of `mem`. Fixed for the heap's life.
    base: usize,
    /// The live regions, and their chunks.
    regions: regions::Regions,
    /// The code area's allocation and free blocks.
    code: code::CodeArea,
    /// The code area's read+execute view, made when the area is first
    /// used; none where the system gives none.
    /// The code area's read+execute view, made when it is first used; or
    /// why it could not be.
    code_exec: Result<fixpt_memmgmt::ExecView, String>,
    /// Base of the active semispace within `mem` — `0` or `MAX_SEMI_WORDS`.
    /// A Value's index is from the start of `mem`, whichever is active, so
    /// that where a Value points does not depend on it.
    active: usize,
    semi: usize,
    /// Next free word, from the start of `mem`: `top - active` is in use.
    top: usize,

    /// Explicit roots held by native code across a safepoint.
    roots: Vec<Value>,
    /// Weak references ([`weak_add`](Heap::weak_add)): each collection
    /// moves an entry on with its object, or, if the object died, clears
    /// it (to [`WEAK_DEAD`]). What a collection does not move (the code
    /// area, regions, the old space in a minor collection) is taken as
    /// alive.
    weak: Vec<Value>,
    /// The entries of `weak` released, for reuse.
    weak_free: Vec<usize>,
    /// Which heap this is, among those this process has made: for a
    /// weak reference held outside, to be read only in its own heap.
    serial: u64,
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
    /// Collect at every `gc_every`th safepoint whatever the heap's fill, as
    /// well as when it is full: a policy for finding rooting bugs, swept
    /// over many values so that a collection lands in every window. 0 is
    /// off; the `gc-stress` feature makes it 1 from the start.
    pub gc_every: u64,
    safepoints: u64,
    pub words_copied: u64,
    /// Time spent collecting, in nanoseconds; and the words allocated
    /// before the last collection, and `top` after it, to count allocation.
    pub gc_nanos: u64,
    pub words_allocated: u64,
    top_after_gc: usize,

    /// The nursery (`young`, `docs/research/generational-gc.md`): whether
    /// there is one; its next free word; and how many words it takes
    /// before a safepoint collects it alone.
    generational: bool,
    nursery_top: usize,
    nursery_words: usize,
    /// One byte per card of 64 words of `mem`: 1 where a store may have put
    /// a young reference since the last collection (the remembered set).
    cards: fixpt_memmgmt::Words,
    /// For each card of the semispaces, where the first object starting in
    /// it starts, plus one; 0 for none.
    crossing: fixpt_memmgmt::Words,
    /// Minor collections made, the words they copied (part of
    /// `words_copied`) and their time (part of `gc_nanos`); whether the
    /// collection due is a major one; and, under the stress policy, how
    /// many policy collections were made.
    pub minor_count: u64,
    pub minor_words_copied: u64,
    pub minor_nanos: u64,
    due_major: bool,
    policy_count: u64,
    /// Telemetry (`docs/research/telemetry.md`, stage 1): the longest pause
    /// of each kind, in nanoseconds; the most words in use, sampled as each
    /// collection starts, which is when the heap is fullest; and whether to
    /// write a line for each collection to stderr (`FIXPT_GC_TRACE`).
    pub max_major_nanos: u64,
    pub max_minor_nanos: u64,
    pub peak_words: u64,
    pub trace: bool,
    /// Check, before each minor collection, that every young reference in
    /// the old space is on a dirty card: for tests.
    pub verify_barrier: bool,
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
        let mem = fixpt_memmgmt::Words::new(MEM_WORDS).expect("address space for the heap");
        let base = mem.words().as_ptr() as usize / 8;
        // A nursery of `DEFAULT_NURSERY_WORDS`, or of `FIXPT_NURSERY` words if
        // that is set; none if it is 0.
        let nursery_words = std::env::var("FIXPT_NURSERY").ok().and_then(|n| n.parse::<usize>().ok()).unwrap_or(DEFAULT_NURSERY_WORDS);
        Heap {
            mem,
            base,
            regions: regions::Regions::new(),
            code: code::CodeArea::default(),
            code_exec: Err("the code area is not used yet".into()),
            active: 0,
            semi,
            top: 0,
            roots: Vec::new(),
            weak: Vec::new(),
            weak_free: Vec::new(),
            serial: NEXT_SERIAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            inhibited: 0,
            globals: Vec::new(),
            symbols: Vec::new(),
            symbol_index: HashMap::new(),
            gc_count: 0,
            gc_every: if cfg!(feature = "gc-stress") { 1 } else { 0 },
            safepoints: 0,
            words_copied: 0,
            gc_nanos: 0,
            words_allocated: 0,
            top_after_gc: 0,
            generational: nursery_words > 0,
            nursery_top: NURSERY_BASE,
            nursery_words: nursery_words.max(1024),
            cards: fixpt_memmgmt::Words::new(young::CARDS / 8).expect("address space for the card table"),
            crossing: fixpt_memmgmt::Words::new(young::SEMI_CARDS / 8).expect("address space for the crossing map"),
            minor_count: 0,
            minor_words_copied: 0,
            minor_nanos: 0,
            max_major_nanos: 0,
            max_minor_nanos: 0,
            peak_words: 0,
            trace: false,
            due_major: false,
            policy_count: 0,
            verify_barrier: std::env::var("FIXPT_VERIFY_BARRIER").is_ok_and(|v| v == "1"),
        }
    }

    // ------------------------------------------------------------------ stats
    /// Live words in the active semispace, and in the nursery.
    #[inline]
    pub fn used(&self) -> usize {
        self.top - self.active + (self.nursery_top - NURSERY_BASE)
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
    pub(crate) fn word(&self, rel: usize) -> u64 {
        self.mem.words()[rel]
    }
    #[inline]
    fn set_word(&mut self, rel: usize, w: u64) {
        self.mem.words_mut()[rel] = w;
    }
    #[inline]
    pub fn slot(&self, rel: usize) -> Value {
        Value(self.word(rel))
    }
    /// A value stored into word `rel` of an object: the write barrier
    /// marks its card when it puts a young reference into the old space.
    #[inline]
    pub fn set_slot(&mut self, rel: usize, v: Value) {
        self.set_word(rel, v.raw());
        if self.generational && v.is_ref() && young::is_young(v.index() - self.base) && rel < 2 * MAX_SEMI_WORDS {
            self.mark_card(rel);
        }
    }

    /// Where the heap's memory starts: word `i` of it, as the heap counts
    /// (its `top`, a region's fill), is at this address plus `8 * i`. For
    /// machine code that allocates without calling in (`fixpt-native`); a
    /// Value is an address already. Fixed for the heap's life.
    pub fn words_address(&self) -> *const u64 {
        self.mem.words().as_ptr()
    }

    /// The word of `mem` a reference names: its address, less where `mem`
    /// starts.
    #[inline(always)]
    pub(crate) fn ix(&self, v: Value) -> usize {
        v.index() - self.base
    }
    /// A pair, or a bloblet's pointer, at word `i` of `mem`: its address.
    #[inline(always)]
    fn pair_v(&self, i: usize) -> Value {
        Value::pair(i + self.base)
    }
    #[inline(always)]
    fn blob_v(&self, i: usize) -> Value {
        Value::bloblet(i + self.base)
    }

    // ------------------------------------------------------------- allocation
    /// Reserve `n` words. Never moves anything; grows the heap if needed.
    fn bump(&mut self, n: usize) -> usize {
        if let Some(h) = self.regions.target
            && let Some(at) = self.regions.bump(h, n)
        {
            return at;
        }
        if self.generational {
            let at = self.nursery_top;
            assert!(at + n <= MEM_WORDS, "the nursery is full: {n} words more");
            self.nursery_top += n;
            return at;
        }
        if self.top + n > self.active + self.semi {
            self.grow(self.top - self.active + n);
        }
        let at = self.top;
        self.top += n;
        at
    }

    /// Grow both semispaces to hold at least `need` words: in place, since
    /// each has its own address space, so nothing moves.
    fn grow(&mut self, need: usize) {
        let mut semi = self.semi;
        while semi < need {
            semi *= 2;
        }
        assert!(semi <= MAX_SEMI_WORDS, "the heap is full: it would need {need} words live, and holds at most {MAX_SEMI_WORDS}");
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
        if fields == 0 {
            // Raw data — a string, a bytevector, a number's bits — is a bloblet
            // with no fields, all suffix. Pointed at its suffix, its words are
            // at `p + i`, and its header is the word just before.
            let main = self.put_header(ty as u8, 0, bytes);
            for i in 0..len {
                self.set_word(main + 1 + i, fill.raw());
            }
            return self.blob_v(main + 1);
        }
        // An object with fields gets a trailer, so that from its pointer the
        // header is one load away whatever its size; the trailer is not part
        // of what `obj_len` counts.
        let main = self.put_header(ty as u8, fields + 1, 0);
        for i in 0..len {
            self.set_word(main + 1 + i, fill.raw());
        }
        self.set_word(main + 1 + len, Self::trailer_word(len + 1));
        self.blob_v(main + 2 + len)
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
        self.pair_v(at)
    }

    // -------------------------------------------------------------- accessors
    #[inline]
    pub fn car(&self, p: Value) -> Value {
        debug_assert!(p.is_pair());
        self.slot(self.ix(p))
    }
    #[inline]
    pub fn cdr(&self, p: Value) -> Value {
        debug_assert!(p.is_pair());
        self.slot(self.ix(p) + 1)
    }
    #[inline]
    pub fn set_car(&mut self, p: Value, v: Value) {
        debug_assert!(p.is_pair());
        self.set_slot(self.ix(p), v);
    }
    #[inline]
    pub fn set_cdr(&mut self, p: Value, v: Value) {
        debug_assert!(p.is_pair());
        self.set_slot(self.ix(p) + 1, v);
    }

    #[inline]
    fn header_of(&self, o: Value) -> u64 {
        let h = self.word(self.main_of(o));
        debug_assert!(is_header(h), "object {o:?} does not lead to a header");
        h
    }

    /// The main header's index, relative to the active space, for either
    /// kind of object pointer: an older one points at it, a bloblet pointer
    /// at the suffix after the fields.
    #[inline]
    fn main_of(&self, o: Value) -> usize {
        debug_assert!(o.is_bloblet(), "{o:?} is not an object");
        // The common case, inline: a trailer just before the suffix says how
        // far back the header is.
        let p = self.ix(o);
        let w = self.word(p - 1);
        if w & TAG_MASK == TAG_TRAILER {
            return p - 1 - layout::T_DISTANCE.get(w) as usize;
        }
        self.bloblet_main_cold(o)
    }

    /// A bloblet without a trailer: its header is just before the suffix (no
    /// fields) or found by the backward scan. Out of line, since the
    /// accessors' common case is a trailer.
    #[cold]
    #[inline(never)]
    fn bloblet_main_cold(&self, o: Value) -> usize {
        self.bloblet_main(o)
    }

    /// Where an object's payload starts: its first field, or for a bloblet
    /// with no fields, its suffix. For a bloblet with no fields that is the
    /// pointer itself, so its raw words are reached without a header read.
    #[inline]
    fn payload_base(&self, o: Value) -> usize {
        self.main_of(o) + 1
    }
    /// The type of a heap object. `None` for anything that is not an object.
    pub fn obj_type(&self, v: Value) -> Option<ObjType> {
        if !v.is_bloblet() {
            return None;
        }
        ObjType::from_code(header_kind(self.header_of(v)) as u16)
    }

    /// Field `j` of an object `alloc` made with `n` fields, read at its fixed
    /// offset from the pointer: `alloc` lays the fields out in order with a
    /// trailer after them, so field `j` is at `n + 1 - j`. One load, with no
    /// look at the trailer; for accessors of fixed-shape objects.
    #[inline]
    fn fixed(&self, o: Value, n: usize, j: usize) -> Value {
        debug_assert!(self.obj_len(o) == n, "{o:?} does not have {n} fields");
        self.slot(self.ix(o) - (n + 1 - j))
    }

    #[inline]
    fn set_fixed(&mut self, o: Value, n: usize, j: usize, v: Value) {
        debug_assert!(self.obj_len(o) == n, "{o:?} does not have {n} fields");
        self.set_slot(self.ix(o) - (n + 1 - j), v)
    }
    pub fn is_a(&self, v: Value, ty: ObjType) -> bool {
        self.obj_type(v) == Some(ty)
    }
    /// Payload length in words.
    #[inline]
    pub fn obj_len(&self, o: Value) -> usize {
        let words = read_head(self.mem.words(), self.main_of(o)).payload_words();
        // A trailer is the runtime's, not part of the object's contents.
        if o.is_bloblet() && self.word(self.ix(o) - 1) & TAG_MASK == TAG_TRAILER { words - 1 } else { words }
    }
    #[inline]
    pub fn obj_ref(&self, o: Value, i: usize) -> Value {
        debug_assert!(i < self.obj_len(o), "payload index {i} out of range");
        self.slot(self.payload_base(o) + i)
    }
    #[inline]
    pub fn obj_set(&mut self, o: Value, i: usize, v: Value) {
        debug_assert!(i < self.obj_len(o), "payload index {i} out of range");
        let at = self.payload_base(o) + i;
        self.set_slot(at, v);
    }
    #[inline]
    fn obj_word(&self, o: Value, i: usize) -> u64 {
        self.word(self.payload_base(o) + i)
    }
    #[inline]
    fn obj_set_word(&mut self, o: Value, i: usize, w: u64) {
        let at = self.payload_base(o) + i;
        self.set_word(at, w)
    }

    // ------------------------------------------------------------ constructors
    pub fn make_vector(&mut self, len: usize, fill: Value) -> Value {
        self.alloc(ObjType::Vector, len, fill)
    }

    pub fn vector_from(&mut self, items: &[Value]) -> Value {
        self.vector_with(items.len(), |i| items[i])
    }

    /// A vector of `n` elements, element `i` being `f(i)`: for filling one
    /// from somewhere that is not a slice, without making one first.
    pub fn vector_with(&mut self, n: usize, mut f: impl FnMut(usize) -> Value) -> Value {
        let v = self.alloc(ObjType::Vector, n, Value::UNSPECIFIED);
        let base = self.payload_base(v);
        for i in 0..n {
            self.set_slot(base + i, f(i));
        }
        v
    }

    /// An object's payload, in order, with its base found once.
    pub fn obj_iter(&self, o: Value) -> impl Iterator<Item = Value> + '_ {
        let base = self.payload_base(o);
        (0..self.obj_len(o)).map(move |i| self.slot(base + i))
    }

    pub fn list_from(&mut self, items: &[Value]) -> Value {
        let mut acc = Value::NULL;
        for x in items.iter().rev() {
            acc = self.cons(*x, acc);
        }
        acc
    }

    /// Collect a proper list into a `Vec`. Returns `None` for an improper list.
    /// A proper list's elements, or `None` if it is improper or cyclic (the
    /// hare, `v`, meets the tortoise, which moves every other step).
    pub fn list_to_vec(&self, mut v: Value) -> Option<Vec<Value>> {
        let mut out = Vec::new();
        let mut slow = v;
        while v.is_pair() {
            out.push(self.car(v));
            v = self.cdr(v);
            if out.len() % 2 == 0 {
                slow = self.cdr(slow);
                if slow == v && v.is_pair() {
                    return None;
                }
            }
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
        self.fixed(b, 1, 0)
    }
    #[inline]
    pub fn set_box(&mut self, b: Value, v: Value) {
        debug_assert!(self.is_a(b, ObjType::Box));
        self.set_fixed(b, 1, 0, v);
    }

    // ----------------------------------------------------------------- bloblets
    //
    // A bloblet pointer points at the start of the suffix, and a field is named
    // by its negative offset from there: field `k` (k ≥ 1) is the word `k`
    // before the suffix. A bloblet with a trailer has it as field 1, which only
    // the runtime writes. See `docs/object-model.md`.

    /// A new bloblet: `fields` fields, all the fixnum 0; `bytes` bytes of
    /// suffix, all zero; and, if `trailer`, a trailer after them, as field 1.
    /// Allocation never collects, so this is atomic as far as the collector is
    /// concerned. Code that cannot rely on that uses the construction protocol,
    /// [`bloblet_reserve`](Heap::bloblet_reserve) and after.
    pub fn make_bloblet(&mut self, kind: u8, fields: usize, bytes: usize, trailer: bool) -> Value {
        assert!(bytes as u64 <= layout::H_BYTES.max(), "a bloblet's suffix is limited to 4 GiB");
        let total = fields + trailer as usize;
        let main = self.put_header(kind, total, bytes);
        for i in 0..total + bytes.div_ceil(8) {
            self.set_word(main + 1 + i, 0);
        }
        if trailer {
            self.set_word(main + total, Self::trailer_word(total));
        }
        self.blob_v(main + 1 + total)
    }

    fn trailer_word(distance: usize) -> u64 {
        layout::T_DISTANCE.put(TAG_TRAILER, distance as u64)
    }

    /// Construction protocol, step 1: reserve room for a bloblet of `fields`
    /// fields, a trailer if `trailer`, and `bytes` suffix bytes, with a header
    /// saying `F = 0` and the whole of it suffix. A trailer is a field, so it
    /// is reserved, and zeroed in step 2, like the others. The room holds whatever it held, and that is
    /// harmless, since a suffix is never traced. Returns a pointer to the
    /// start of that suffix. Only ordinary headers: a large bloblet is made
    /// with [`make_bloblet`](Heap::make_bloblet), since its header could not
    /// change in one store.
    pub fn bloblet_reserve(&mut self, kind: u8, fields: usize, bytes: usize, trailer: bool) -> Value {
        let fields = fields + trailer as usize;
        assert!(fields as u64 <= layout::H_FIELDS.max(), "the construction protocol is for ordinary headers");
        let all = fields * 8 + bytes;
        assert!(all as u64 <= layout::H_BYTES.max(), "a bloblet's suffix is limited to 4 GiB");
        let main = self.put_header(kind, 0, all);
        self.blob_v(main + 1)
    }

    /// Construction protocol, step 2: zero the would-be fields `from..to`
    /// (counted from the header, 0-based, the trailer's slot last) of a
    /// bloblet reserved by
    /// [`bloblet_reserve`](Heap::bloblet_reserve). May be done a piece at a
    /// time, with collections in between: the words are still suffix.
    pub fn bloblet_zero_reserved(&mut self, v: Value, from: usize, to: usize) {
        let p = self.ix(v);
        for i in from..to {
            self.set_word(p + i, 0);
        }
    }

    /// Construction protocol, step 3: the one change of header, to `fields`
    /// fields (and the trailer, if one was reserved) and what is left of the
    /// suffix. Every would-be field, the trailer's slot included, must be the
    /// fixnum 0 by now: the header change makes them traced. Returns the
    /// bloblet's pointer, which has moved `fields` words forward.
    pub fn bloblet_publish(&mut self, v: Value, fields: usize, trailer: bool) -> Value {
        let main = self.ix(v) - 1;
        let head = read_head(self.mem.words(), main);
        assert_eq!(head.fields, 0, "only a reserved bloblet can be published");
        let total = fields + trailer as usize;
        assert!(head.bytes >= total * 8, "more fields than were reserved");
        for i in 0..total {
            assert_eq!(self.word(main + 1 + i), 0, "would-be field {i} is not zeroed");
        }
        let h = make_header(head.kind, total, head.bytes - total * 8);
        self.set_word(main, h);
        if trailer {
            self.set_word(main + total, Self::trailer_word(total));
        }
        self.blob_v(main + 1 + total)
    }

    /// The main header's index, relative to the active space.
    fn bloblet_main(&self, v: Value) -> usize {
        debug_assert!(v.is_bloblet(), "{v:?} is not a bloblet");
        find_main(self.mem.words(), self.ix(v)).expect("no forwarding pointers outside a collection")
    }

    /// What a bloblet's header says.
    pub fn bloblet_head(&self, v: Value) -> Head {
        read_head(self.mem.words(), self.bloblet_main(v))
    }

    pub fn bloblet_kind(&self, v: Value) -> u8 {
        self.bloblet_head(v).kind
    }

    /// Whether field 1 is a trailer.
    pub fn bloblet_has_trailer(&self, v: Value) -> bool {
        self.bloblet_head(v).fields > 0 && self.word(self.ix(v) - 1) & TAG_MASK == TAG_TRAILER
    }

    fn field_slot(&self, v: Value, k: usize) -> Result<usize, BlobletError> {
        let head = self.bloblet_head(v);
        if k == 0 || k > head.fields {
            return Err(BlobletError::NoSuchField(k));
        }
        let at = self.ix(v) - k;
        if self.word(at) & TAG_MASK == TAG_TRAILER {
            return Err(BlobletError::Trailer);
        }
        Ok(at)
    }

    /// Field `k`, read in one load at `p - k`, without looking at the header:
    /// the fixed-offset access the layout exists for. For code that knows its
    /// bloblet's shape, as the engines know a code bloblet's. Checked only in
    /// debug builds; [`bloblet_field`](Heap::bloblet_field) is the checked
    /// form.
    #[inline]
    pub fn bloblet_slot(&self, v: Value, k: usize) -> Value {
        debug_assert!(v.is_bloblet() && k >= 1 && k <= self.bloblet_head(v).fields, "{v:?} has no field -{k}");
        self.slot(self.ix(v) - k)
    }

    /// Set field `k` in one store. Unchecked but for debug builds, as
    /// [`bloblet_slot`](Heap::bloblet_slot) is; it does not look at the frozen
    /// flags, so it is for the runtime's own bloblets.
    #[inline]
    pub fn set_bloblet_slot(&mut self, v: Value, k: usize, x: Value) {
        debug_assert!(v.is_bloblet() && k >= 1 && k <= self.bloblet_head(v).fields, "{v:?} has no field -{k}");
        debug_assert!(self.word(self.ix(v) - k) & TAG_MASK != TAG_TRAILER, "field -{k} is the trailer");
        self.set_slot(self.ix(v) - k, x);
    }

    /// Field `k`, `k` words before the suffix.
    pub fn bloblet_field(&self, v: Value, k: usize) -> Result<Value, BlobletError> {
        Ok(self.slot(self.field_slot(v, k)?))
    }

    pub fn set_bloblet_field(&mut self, v: Value, k: usize, x: Value) -> Result<(), BlobletError> {
        if matches!(x.tag(), TAG_TRAILER | TAG_HEADER | TAG_FORWARD) {
            return Err(BlobletError::NotAValue);
        }
        let at = self.field_slot(v, k)?;
        if self.bloblet_head(v).fields_frozen {
            return Err(BlobletError::FieldsFrozen);
        }
        self.set_slot(at, x);
        Ok(())
    }

    /// Byte `i` of the suffix.
    pub fn bloblet_byte(&self, v: Value, i: usize) -> Result<u8, BlobletError> {
        if i >= self.bloblet_head(v).bytes {
            return Err(BlobletError::NoSuchByte(i));
        }
        Ok((self.word(self.ix(v) + i / 8) >> ((i % 8) * 8)) as u8)
    }

    pub fn set_bloblet_byte(&mut self, v: Value, i: usize, b: u8) -> Result<(), BlobletError> {
        let head = self.bloblet_head(v);
        if i >= head.bytes {
            return Err(BlobletError::NoSuchByte(i));
        }
        if head.suffix_frozen {
            return Err(BlobletError::SuffixFrozen);
        }
        let wi = self.ix(v) + i / 8;
        let shift = (i % 8) * 8;
        let w = (self.word(wi) & !(0xffu64 << shift)) | ((b as u64) << shift);
        self.set_word(wi, w);
        Ok(())
    }

    /// A flat array of `n` elements of layout `code` (`layout::FLAT_*`),
    /// all bits zero.
    pub fn make_flat_array(&mut self, code: i64, n: usize) -> Value {
        let a = self.make_bloblet(layout::kind("flat-array"), 1, n * layout::flat_size(code), true);
        self.set_bloblet_slot(a, 2, Value::fixnum(code));
        a
    }
    /// A flat array's layout (`layout::FLAT_*`).
    pub fn flat_array_code(&self, a: Value) -> i64 {
        self.bloblet_slot(a, 2).as_fixnum()
    }
    /// A flat array's length.
    pub fn flat_array_len(&self, a: Value) -> usize {
        self.bloblet_head(a).bytes / layout::flat_size(self.flat_array_code(a))
    }
    /// Element `i`'s bits (zero-extended if 4 bytes wide); in range.
    pub fn flat_bits(&self, a: Value, i: usize) -> u64 {
        if layout::flat_size(self.flat_array_code(a)) == 8 {
            self.word(self.ix(a) + i)
        } else {
            (self.word(self.ix(a) + i / 2) >> ((i % 2) * 32)) as u32 as u64
        }
    }
    /// Element `i` := `bits` (their low 32, if 4 bytes wide); in range.
    pub fn set_flat_bits(&mut self, a: Value, i: usize, bits: u64) {
        if layout::flat_size(self.flat_array_code(a)) == 8 {
            self.set_word(self.ix(a) + i, bits);
        } else {
            let (wi, shift) = (self.ix(a) + i / 2, (i % 2) * 32);
            let w = (self.word(wi) & !(0xffff_ffffu64 << shift)) | ((bits & 0xffff_ffff) << shift);
            self.set_word(wi, w);
        }
    }

    /// The whole suffix, as bytes.
    pub fn bloblet_bytes(&self, v: Value) -> Vec<u8> {
        let n = self.bloblet_head(v).bytes;
        (0..n).map(|i| (self.word(self.ix(v) + i / 8) >> ((i % 8) * 8)) as u8).collect()
    }

    /// Write `bytes` into the suffix starting at byte `at`.
    pub fn set_bloblet_bytes(&mut self, v: Value, at: usize, bytes: &[u8]) -> Result<(), BlobletError> {
        for (i, b) in bytes.iter().enumerate() {
            self.set_bloblet_byte(v, at + i, *b)?;
        }
        Ok(())
    }

    /// The 32-bit word `i` of the suffix: an instruction, for code. One load,
    /// with no look at the header outside debug builds.
    #[inline]
    pub fn bloblet_u32(&self, v: Value, i: usize) -> u32 {
        debug_assert!(4 * i + 4 <= self.bloblet_head(v).bytes);
        (self.word(self.ix(v) + i / 2) >> ((i % 2) * 32)) as u32
    }

    /// A new bloblet: `v`'s fields and suffix, with `new` prepended — in front
    /// of the existing fields, `new[0]` furthest from the suffix. Every
    /// existing field keeps its offset from the suffix, so code written
    /// against `v`'s fields works on the extension. A trailer is renewed for
    /// the new size. `v` is untouched, and the new bloblet is not frozen.
    pub fn bloblet_extend(&mut self, v: Value, new: &[Value]) -> Value {
        let head = self.bloblet_head(v);
        let trailer = self.bloblet_has_trailer(v);
        let old = head.fields - trailer as usize;
        let n = self.make_bloblet(head.kind, new.len() + old, head.bytes, trailer);
        let skip = trailer as usize;
        // Old field k (counting from the suffix) is at the same k in the new.
        for k in 1 + skip..=head.fields {
            let x = self.slot(self.ix(v) - k);
            self.set_slot(self.ix(n) - k, x);
        }
        for (i, x) in new.iter().enumerate() {
            // `new[0]` is furthest from the suffix.
            let k = head.fields + new.len() - i;
            self.set_slot(self.ix(n) - k, *x);
        }
        for w in 0..head.bytes.div_ceil(8) {
            let x = self.word(self.ix(v) + w);
            self.set_word(self.ix(n) + w, x);
        }
        n
    }

    /// A cellular closure over nothing, its word to come (field 2 is #f
    /// until set): what a compiler makes once for a procedure it lifts,
    /// before the procedures that call it are compiled.
    pub fn closure_over_nothing(&mut self) -> Value {
        let c = self.make_bloblet(layout::kind("cellular-closure"), 1, 0, true);
        self.set_bloblet_slot(c, layout::cellular::CLOSURE_WORD, Value::FALSE);
        c
    }

    /// A frozen bloblet of `kind` with `fields`, in order: a sum or a
    /// product, as `%make-frozen` makes them, or as a compiler makes a
    /// constant one once.
    pub fn make_frozen(&mut self, kind: u8, fields: &[Value]) -> Value {
        let b = self.make_bloblet(kind, fields.len(), 0, true);
        for (i, v) in fields.iter().enumerate() {
            self.set_bloblet_slot(b, i + 2, *v);
        }
        self.freeze_bloblet(b, true, true);
        b
    }

    /// A copy, in this heap, of everything `root` reaches in heap `from`:
    /// pairs and bloblets alike, sharing and cycles kept, raw suffixes as
    /// they are, frozen flags too; an interned symbol is this heap's symbol
    /// of the same name. For carrying compiled code between heaps (a cache
    /// of it in an image of its own). Nothing collects meanwhile: allocation
    /// never does. Code in a code area is not carried; its reference, if
    /// any, would be, and must be none.
    pub fn copy_graph_from(&mut self, from: &Heap, root: Value) -> Value {
        use std::collections::hash_map::Entry;
        // First every object is made, empty; then the fields are filled in.
        let mut made: HashMap<u64, Value> = HashMap::new();
        let mut order: Vec<Value> = Vec::new();
        let mut todo = vec![root];
        while let Some(v) = todo.pop() {
            if !v.is_ref() {
                continue;
            }
            let Entry::Vacant(slot) = made.entry(v.raw()) else { continue };
            if v.is_pair() {
                slot.insert(self.cons(Value::NULL, Value::NULL));
                order.push(v);
                todo.extend([from.car(v), from.cdr(v)]);
                continue;
            }
            if from.is_a(v, ObjType::Symbol) && from.symbol_index.contains_key(&from.symbol_name(v)) {
                let name = from.symbol_name(v);
                slot.insert(self.intern(&name));
                continue;
            }
            let head = from.bloblet_head(v);
            let trailer = from.bloblet_has_trailer(v);
            let copy = self.make_bloblet(head.kind, head.fields - trailer as usize, head.bytes, trailer);
            slot.insert(copy);
            order.push(v);
            for k in (1 + trailer as usize)..=head.fields {
                todo.push(from.slot(from.ix(v) - k));
            }
        }
        let map = |x: Value| if x.is_ref() { made[&x.raw()] } else { x };
        for v in order {
            let copy = made[&v.raw()];
            if v.is_pair() {
                let (a, d) = (map(from.car(v)), map(from.cdr(v)));
                self.set_car(copy, a);
                self.set_cdr(copy, d);
                continue;
            }
            let head = from.bloblet_head(v);
            let trailer = from.bloblet_has_trailer(v);
            for k in (1 + trailer as usize)..=head.fields {
                let x = map(from.slot(from.ix(v) - k));
                self.set_bloblet_slot(copy, k, x);
            }
            for j in 0..head.bytes.div_ceil(8) {
                let w = from.word(from.ix(v) + j);
                let at = self.ix(copy) + j;
                self.set_word(at, w);
            }
            if head.fields_frozen || head.suffix_frozen {
                self.freeze_bloblet(copy, head.fields_frozen, head.suffix_frozen);
            }
        }
        map(root)
    }

    /// Freeze a bloblet's fields, its suffix, or both. There is no thawing.
    pub fn freeze_bloblet(&mut self, v: Value, fields: bool, suffix: bool) {
        let main = self.bloblet_main(v);
        let mut h = self.word(main);
        if fields {
            h = layout::H_FIELDS_FROZEN.put(h, 1);
        }
        if suffix {
            h = layout::H_SUFFIX_FROZEN.put(h, 1);
        }
        self.set_word(main, h);
    }

    // ----------------------------------------------------------------- closures

    /// A closure over `code`, with `extra` its environment or captured values.
    /// See `layout::closure` for why it is laid out back to front.
    pub fn make_closure(&mut self, code: Value, extra: &[Value]) -> Value {
        use layout::closure::{CLOSURE_CODE, CLOSURE_EXTRA0};
        let c = self.make_bloblet(ObjType::Closure as u8, 1 + extra.len(), 0, true);
        self.set_bloblet_slot(c, CLOSURE_CODE, code);
        for (i, x) in extra.iter().enumerate() {
            self.set_bloblet_slot(c, CLOSURE_EXTRA0 + i, *x);
        }
        c
    }

    /// A closure's code. One load.
    #[inline]
    pub fn closure_code(&self, c: Value) -> Value {
        self.bloblet_slot(c, layout::closure::CLOSURE_CODE)
    }

    /// A closure's extra value `i`: its environment, or captured value `i`.
    /// One load.
    #[inline]
    pub fn closure_ref(&self, c: Value, i: usize) -> Value {
        self.bloblet_slot(c, layout::closure::CLOSURE_EXTRA0 + i)
    }

    #[inline]
    pub fn set_closure_ref(&mut self, c: Value, i: usize, x: Value) {
        self.set_bloblet_slot(c, layout::closure::CLOSURE_EXTRA0 + i, x)
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
        self.is_a(sym, ObjType::Symbol) && self.fixed(sym, 3, 2).as_fixnum() >= 0
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
        self.string_to_rust(self.fixed(sym, 3, 0))
    }
    #[inline]
    pub fn symbol_global_slot(&self, sym: Value) -> usize {
        debug_assert!(self.is_a(sym, ObjType::Symbol));
        self.fixed(sym, 3, 2).as_fixnum() as usize
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

    /// Whether collection is held off ([`inhibit_collection`](Heap::inhibit_collection)).
    pub fn collection_inhibited(&self) -> bool {
        self.inhibited > 0
    }

    /// Every Value the heap itself roots, for `sro`.
    pub(crate) fn roots_for_sro(&self) -> Vec<Value> {
        self.roots.iter().chain(&self.globals).chain(&self.symbols).copied().collect()
    }

    // ------------------------------------------------------------ native roots
    /// Root `v` for the duration of a native operation that spans a safepoint.
    /// Returns the depth to unwind to.
    pub fn push_root(&mut self, v: Value) -> usize {
        self.roots.push(v);
        self.roots.len() - 1
    }
    /// How many explicit roots there are: the depth to pop back to.
    pub fn root_count(&self) -> usize {
        self.roots.len()
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
        if self.collection_due() {
            self.collect_due(extra_roots);
        }
    }

    /// The collection [`collection_due`](Heap::collection_due) said is due:
    /// of the nursery alone, or of everything.
    pub fn collect_due(&mut self, extra_roots: &mut [&mut [Value]]) {
        if self.generational && !self.due_major {
            self.collect_minor(extra_roots);
        } else {
            self.collect(extra_roots);
        }
    }

    /// A safepoint, counted: whether the heap warrants a collection there,
    /// which the caller then makes with [`collect`](Heap::collect). For a
    /// machine whose roots cost something to gather, which it gathers only
    /// then.
    pub fn collection_due(&mut self) -> bool {
        if self.inhibited > 0 {
            return false;
        }
        let full = (self.top - self.active) as f64 >= self.semi as f64 * COLLECT_THRESHOLD
            || self.regions.reap_taken as f64 >= self.semi as f64 * COLLECT_THRESHOLD
            || self.code.taken as f64 >= self.semi as f64 * COLLECT_THRESHOLD;
        self.safepoints += 1;
        let policy = self.gc_every > 0 && self.safepoints.is_multiple_of(self.gc_every);
        let nursery_full = self.generational && self.nursery_top - NURSERY_BASE >= self.nursery_words;
        // Under the stress policy, a generational heap's policy collections
        // are minor ones, but every fourth, which is major.
        if policy {
            self.policy_count += 1;
        }
        self.due_major = full || (policy && (!self.generational || self.policy_count.is_multiple_of(4)));
        full || policy || nursery_full
    }

    /// Which heap this is, among those this process has made.
    pub fn serial(&self) -> u64 {
        self.serial
    }

    /// A weak reference to `v`, a pair or bloblet: its number, for
    /// [`weak_get`](Heap::weak_get). It does not keep `v` alive.
    pub fn weak_add(&mut self, v: Value) -> usize {
        assert!(v.is_ref(), "a weak reference is to an object");
        match self.weak_free.pop() {
            Some(i) => {
                self.weak[i] = v;
                i
            }
            None => {
                self.weak.push(v);
                self.weak.len() - 1
            }
        }
    }

    /// Weak reference `i`'s object, where it is now; `None` once a
    /// collection has found it dead.
    pub fn weak_get(&self, i: usize) -> Option<Value> {
        let v = self.weak[i];
        v.is_ref().then_some(v)
    }

    /// Weak reference `i` no longer wanted: its number may be given again.
    pub fn weak_release(&mut self, i: usize) {
        self.weak[i] = WEAK_DEAD;
        self.weak_free.push(i);
    }

    /// Cheney semispace copy. Compacts, which is also what makes a dumped image
    /// contiguous and relocation-free.
    pub fn collect(&mut self, extra_roots: &mut [&mut [Value]]) {
        let started = std::time::Instant::now();
        let before = self.used();
        self.peak_words = self.peak_words.max(before as u64);
        self.words_allocated += self.top.saturating_sub(self.top_after_gc) as u64 + (self.nursery_top - NURSERY_BASE) as u64;
        let from = self.active;
        let to = if self.active == 0 { MAX_SEMI_WORDS } else { 0 };
        let mem = self.mem.words_mut();
        let reaps = self.regions.live.len();
        let arenas: Vec<(usize, usize)> = self.regions.arena_ranges().collect();
        let owner = std::mem::take(&mut self.regions.owner);
        let mut c = Copier {
            base: self.base,
            from,
            to,
            free: 0,
            owner,
            new: vec![Vec::new(); reaps],
            marked: HashSet::new(),
            code_marks: HashSet::new(),
            code_gray: Vec::new(),
            regions: &mut self.regions,
            minor: false,
            crossing: &mut self.crossing,
            last_card: usize::MAX,
        };

        // `scan` and `c.free` are relative to `to`.
        let mut scan = 0usize;

        // Under the bug-finding policy, start to-space with a filler whose
        // size changes from one collection to the next, so that every object
        // moves at every collection. Otherwise a copying collector tends to
        // put each object back where it was, and a stale Value someone held
        // across a collection still finds its object, and the bug hides.
        if self.gc_every > 0 {
            let pad = 1 + (self.gc_count as usize % 7);
            if self.top - self.active + pad <= self.semi {
                // A raw bloblet: a header, then a suffix the scan skips.
                mem[to] = make_header(layout::kind("bloblet"), 0, (pad - 1) * 8);
                for i in 1..pad {
                    mem[to + i] = 0;
                }
                c.free = pad;
                scan = pad;
                c.crossed(to, pad);
            }
        }

        // Forward every root. Done by hand rather than through a closure so the
        // borrow checker stays out of the way in the hot loop.
        macro_rules! fwd {
            ($v:expr) => {{
                let v = $v;
                if v.is_ref() {
                    Self::copy_out(mem, &mut c, v)
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
        // What the arenas hold is live, and stays where it is.
        for (lo, hi) in arenas {
            let mut at = lo;
            while at < hi {
                at += Self::scan_one(mem, at, &mut c);
            }
        }

        // Scan to-space linearly, and each reap's new chunks, until neither
        // has anything left to scan: each may copy into the other.
        let mut reap_scan = vec![(0usize, 0usize); reaps];
        loop {
            let mut more = false;
            while scan < c.free {
                scan += Self::scan_one(mem, to + scan, &mut c);
                more = true;
            }
            // The code area's bloblets found live, scanned in place.
            while let Some(main) = c.code_gray.pop() {
                Self::scan_one(mem, main, &mut c);
                more = true;
            }
            for (h, rs) in reap_scan.iter_mut().enumerate() {
                while let Some(&(start, fill)) = c.new[h].get(rs.0) {
                    let at = rs.1.max(start);
                    if at < fill {
                        rs.1 = at + Self::scan_one(mem, at, &mut c);
                        more = true;
                    } else if rs.0 + 1 < c.new[h].len() {
                        *rs = (rs.0 + 1, 0);
                    } else {
                        rs.1 = at;
                        break;
                    }
                }
            }
            if !more {
                break;
            }
        }
        update_weak(mem, self.base, &mut self.weak, from, false);
        let Copier { free, new, marked, code_marks, .. } = c;
        self.sweep_code(&code_marks);
        // Ended reaps' chunks no reference was found into may be reused;
        // the rest wait for a collection that finds none.
        let quarantine = std::mem::take(&mut self.regions.quarantine);
        for q in quarantine {
            if marked.contains(&q) {
                self.regions.quarantine.insert(q);
            } else {
                self.regions.reap_free.push(q);
            }
        }

        // Each reap's old chunks given back, its new ones in their place:
        // the last is its current chunk, which machine code allocates in.
        for (h, mut chunks) in new.into_iter().enumerate() {
            if !self.regions.reap[h] {
                continue;
            }
            let old: Vec<(usize, usize)> = self.regions.chunks_of(h).collect();
            let old_current = self.regions.current(h).map_or(0, |(start, fill)| fill - start);
            // Every reference into them has been moved on: they may be
            // reused at once.
            for (start, _) in old {
                self.mem.release(start..start + regions::CHUNK_WORDS);
                self.regions.reap_free.push(start);
            }
            let current = chunks.pop();
            let r = &mut self.regions;
            r.table[h] = current.map_or([0, 0], |(start, fill)| [fill, start + regions::CHUNK_WORDS]);
            let new_current = current.map_or(0, |(start, fill)| fill - start);
            // Allocated before, as `region_words` counts: what was current,
            // though copied. What is current now is not counted yet.
            r.words = r.words + old_current as u64 - new_current as u64;
            for &(start, _) in chunks.iter().chain(current.iter()) {
                r.owner.insert(start, h);
            }
            r.live[h] = chunks;
        }
        self.regions.reap_taken = 0;

        self.active = to;
        self.top = to + free;
        self.gc_count += 1;
        self.words_copied += free as u64;
        // The nursery emptied into the old space; no card of it dirty.
        self.nursery_top = NURSERY_BASE;
        self.clear_cards(to, to + free);

        // Keep headroom in proportion to what is live: a semispace at least
        // three times it, so that the next collection comes after at least
        // 1.25 times the live data is allocated, and copying costs less than
        // a word per word allocated. Growing only when the live data was
        // three quarters of the space collected again after a sliver of it,
        // copying everything each time.
        if free * LIVE_RATIO > self.semi {
            self.grow(free * LIVE_RATIO);
        }
        self.top_after_gc = self.top;
        let nanos = started.elapsed().as_nanos() as u64;
        self.gc_nanos += nanos;
        self.max_major_nanos = self.max_major_nanos.max(nanos);
        self.traced("major", self.gc_count, nanos, free, before);
    }

    /// For `FIXPT_GC_TRACE`: a line for the collection just made, of `kind`
    /// and number `n`, which took `nanos` and copied `copied` words, the
    /// heap having `before` words in use as it started.
    pub(crate) fn traced(&self, kind: &str, n: u64, nanos: u64, copied: usize, before: usize) {
        if self.trace {
            let m = |w: usize| w as f64 / 1e6;
            eprintln!(
                "; gc {kind} {n}: {:.2} ms, {:.2} M words copied, {:.2} M in use before, {:.2} M after",
                nanos as f64 / 1e6,
                m(copied),
                m(before),
                m(self.used())
            );
        }
    }

    /// For machine code that allocates without calling in (`fixpt-native`):
    /// where `top` is. The address holds while the heap does not move.
    pub fn top_address(&mut self) -> *mut usize {
        if self.generational { &mut self.nursery_top } else { &mut self.top }
    }

    /// How far machine code may take `top` before it must call in to
    /// allocate: short of where a safepoint would collect, so that
    /// collection comes when it would have, whichever machine runs the
    /// program, and runs compare. (Machine code needs no headroom, and could
    /// go to the end of the semispace; a program that allocates mostly
    /// inline would then collect less often, but at other points than the
    /// Rust machine.) 0 while a policy collects at every safepoint, or
    /// collection is inhibited: then every allocation calls in.
    pub fn inline_limit(&self) -> usize {
        if self.gc_every > 0 || self.inhibited > 0 {
            0
        } else if self.generational {
            NURSERY_BASE + self.nursery_words
        } else {
            self.active + (self.semi as f64 * COLLECT_THRESHOLD) as usize
        }
    }

    /// Words allocated since the heap was made: in the semispaces and the
    /// nursery, in regions, and in the code area.
    pub fn allocated(&self) -> u64 {
        self.words_allocated
            + self.top.saturating_sub(self.top_after_gc) as u64
            + (self.nursery_top - NURSERY_BASE) as u64
            + self.region_words()
            + self.code.allocated
    }

    /// Collections made, minor and major.
    pub fn collections(&self) -> u64 {
        self.gc_count + self.minor_count
    }

    /// The semispace's size in words, for reports.
    pub fn semispace_words(&self) -> usize {
        self.semi
    }

    /// Forward the references in the object or pair that starts at `at`;
    /// its size. The first word at a boundary is either a header (an object
    /// follows) or an ordinary Value (a pair cell follows); see `value.rs` on
    /// why tag 110 is reserved to make this unambiguous.
    #[inline(always)]
    fn scan_one(mem: &mut [u64], at: usize, c: &mut Copier) -> usize {
        let w = mem[at];
        if is_header(w) {
            // The collector needs only `F` and `B`: trace the fields, skip
            // the suffix. It never asks what kind of object this is.
            let main = at + is_extension(w) as usize;
            let head = read_head(mem, main);
            for i in 0..head.fields {
                let v = Value(mem[main + 1 + i]);
                if v.is_ref() {
                    mem[main + 1 + i] = Self::copy_out(mem, c, v).raw();
                }
            }
            head.size()
        } else {
            for i in 0..2 {
                let v = Value(mem[at + i]);
                if v.is_ref() {
                    mem[at + i] = Self::copy_out(mem, c, v).raw();
                }
            }
            2
        }
    }

    /// Copy one object out of from-space, or out of a live reap's old
    /// chunks, if it is not already; leaving a forwarding pointer behind.
    /// Returns where it is now. Anything else (an arena's, or a reference an
    /// ended region left) stays as it is.
    ///
    /// A forwarding pointer always records where the object's *main header*
    /// went, whichever kind of pointer found it.
    #[inline(always)]
    fn copy_out(mem: &mut [u64], c: &mut Copier, v: Value) -> Value {
        let i = v.index() - c.base;
        let young = young::is_young(i);
        // A minor collection copies the nursery's objects, and only them.
        if c.minor && !young {
            return v;
        }
        let reap = if young || (c.from..c.from + MAX_SEMI_WORDS).contains(&i) {
            None
        } else if code::in_code_area(i) {
            // It never moves: marked, and scanned once.
            debug_assert!(v.tag() == TAG_BLOBLET, "only bloblets are in the code area");
            code::mark_code(mem, i, &mut c.code_marks, &mut c.code_gray);
            return v;
        } else if i >= REAP_BASE {
            // A bloblet with no suffix is pointed at one past its fields,
            // which may be the next chunk; its last field is not.
            let within = if v.is_pair() { i } else { i - 1 };
            let chunk = within & !(regions::CHUNK_WORDS - 1);
            match c.owner.get(&chunk) {
                Some(&h) => Some(h),
                None => {
                    // A reference an ended reap left: not followed, but
                    // its chunk not reused while it is there.
                    if c.regions.quarantine.contains(&chunk) {
                        c.marked.insert(chunk);
                    }
                    return v;
                }
            }
        } else {
            return v;
        };
        if v.is_pair() {
            let first = Value(mem[i]);
            if first.is_forward() {
                return Value::pair(first.index() + c.base);
            }
            let dst = c.alloc(reap, 2);
            mem[dst] = mem[i];
            mem[dst + 1] = mem[i + 1];
            mem[i] = Value::forward(dst).raw();
            return Value::pair(dst + c.base);
        }
        // A bloblet pointer, at the start of the suffix. Find the header, by
        // the trailer or the backward scan, and copy as any object. Leave a
        // second forward just before the suffix, so that the next pointer to
        // this bloblet finds it in one step, trailer or not.
        debug_assert!(v.tag() == TAG_BLOBLET);
        let new_main = match find_main(mem, i) {
            Err(done) => done,
            Ok(main) => {
                let new_main = Self::copy_object(mem, main, c, reap);
                if i - 1 != main {
                    mem[i - 1] = Value::forward(new_main).raw();
                }
                new_main
            }
        };
        let head = read_head(mem, new_main);
        Value::bloblet(new_main + 1 + head.fields + c.base)
    }

    /// Copy the object whose main header is at `main`, unless it has been
    /// already: to to-space, or to reap `reap`'s new chunks. Returns its
    /// main header's new index.
    fn copy_object(mem: &mut [u64], main: usize, c: &mut Copier, reap: Option<usize>) -> usize {
        let first = Value(mem[main]);
        if first.is_forward() {
            return first.index();
        }
        let head = read_head(mem, main);
        let start = main - head.pre;
        let words = head.size();
        let dst = c.alloc(reap, words);
        mem.copy_within(start..start + words, dst);
        let new_main = dst + head.pre;
        mem[main] = Value::forward(new_main).raw();
        new_main
    }

    // ------------------------------------------------------- image support
    /// The live prefix of the active semispace, ready to be written out as-is.
    /// The live words, globals, symbols and roots, with every reference
    /// rebased as though the active semispace began at word 0: an image's
    /// contents, which `from_image` loads at word 0. Raw suffix words are
    /// left as they are.
    pub fn image_parts(&self) -> (Vec<u64>, Vec<Value>, Vec<Value>, Vec<Value>) {
        assert_eq!(self.live_regions(), 0, "an image is made with no region live");
        assert_eq!(self.code.used, 0, "an image cannot yet carry the code area (docs/object-model.md, \"A collected code area\")");
        // The old space, then the nursery after it, as one run of words.
        let old = self.top - self.active;
        let shift = ((self.base + self.active) as u64) << 3;
        let young_shift = ((self.base + NURSERY_BASE) as u64 - old as u64) << 3;
        let rebase = |v: Value| match v.is_ref() {
            true if young::is_young(v.index() - self.base) => Value(v.raw() - young_shift),
            true => Value(v.raw() - shift),
            false => v,
        };
        let mut words = self.mem.words()[self.active..self.top].to_vec();
        words.extend_from_slice(&self.mem.words()[NURSERY_BASE..self.nursery_top]);
        map_refs(&mut words, rebase);
        let all = |vs: &[Value]| vs.iter().map(|v| rebase(*v)).collect::<Vec<_>>();
        (words, all(&self.globals), all(&self.symbols), all(&self.roots))
    }

    /// The explicit roots, in order: part of an image, since a runtime
    /// finds its own by position (`fixpt_runtime::ERROR_RTD_ROOT`).
    pub fn roots_slice(&self) -> &[Value] {
        &self.roots
    }

    pub fn live_words(&self) -> &[u64] {
        &self.mem.words()[self.active..self.top]
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
        roots: Vec<Value>,
    ) -> Result<Heap, String> {
        let mut semi = DEFAULT_SEMI_WORDS;
        while semi < words.len() {
            semi *= 2;
        }
        let mut heap = Heap::with_semispace(semi);
        // An image's references count from word 0: here they are
        // addresses, of where it is loaded.
        let shift = (heap.base as u64) << 3;
        let relocate = |v: Value| if v.is_ref() { Value(v.raw() + shift) } else { v };
        heap.mem.words_mut()[..words.len()].copy_from_slice(words);
        map_refs(&mut heap.mem.words_mut()[..words.len()], relocate);
        heap.top = words.len();
        heap.cross_all(0, words.len());
        heap.globals = globals.into_iter().map(relocate).collect();
        heap.symbols = symbols.into_iter().map(relocate).collect();
        heap.roots = roots.into_iter().map(relocate).collect();
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
        self.verify_range(self.active, self.top)?;
        self.verify_range(NURSERY_BASE, self.nursery_top).map_err(|e| format!("in the nursery: {e}"))?;
        for (lo, hi) in self.regions.ranges() {
            self.verify_range(lo, hi).map_err(|e| format!("in a region: {e}"))?;
        }
        if self.code.top > CODE_BASE {
            self.verify_range(CODE_BASE, self.code.top).map_err(|e| format!("in the code area: {e}"))?;
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

    /// The objects and pairs from `lo` up to `top`, walked and checked.
    fn verify_range(&self, lo: usize, top: usize) -> Result<(), String> {
        let mut scan = lo;
        while scan < top {
            let w = self.word(scan);
            if is_header(w) {
                let main = scan + is_extension(w) as usize;
                if main >= top || !is_header(self.word(main)) || is_extension(self.word(main)) {
                    return Err(format!("the extension word at {scan} is not followed by a main header"));
                }
                if is_extension(w) != header_is_large(self.word(main)) {
                    return Err(format!("the header at {main} disagrees with its extension word"));
                }
                let head = read_head(self.mem.words(), main);
                if scan + head.size() > top {
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
                if scan + 2 > top {
                    return Err(format!("pair at {scan} runs past the end of the heap"));
                }
                self.check_ref(self.slot(scan), scan)?;
                self.check_ref(self.slot(scan + 1), scan)?;
                scan += 2;
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
        if v.tag() == crate::value::TAG_UNUSED {
            return Err(format!("a word with the retired tag 010, at word {at}"));
        }
        // A region's objects are checked as its chunks are walked; and a
        // reference to one ended may linger, unused, in what is dead.
        if v.is_ref() && Self::in_region_area(self.ix(v)) {
            return Ok(());
        }
        // The code area's objects are checked as it is walked.
        if v.is_bloblet() && code::in_code_area(self.ix(v)) {
            return Ok(());
        }
        if v.is_ref() {
            // A bloblet with no suffix is pointed at one past its last field,
            // which for the last object in the heap is the top itself.
            let (lo, hi) = if young::is_young(self.ix(v)) { (NURSERY_BASE, self.nursery_top) } else { (self.active, self.top) };
            let beyond = if v.is_bloblet() { self.ix(v) > hi || self.ix(v) <= lo } else { self.ix(v) >= hi || self.ix(v) < lo };
            if beyond {
                return Err(format!("dangling reference {v:?} at word {at}"));
            }
            if v.is_bloblet() {
                let p = self.ix(v);
                let main = find_main(self.mem.words(), p)
                    .map_err(|_| format!("bloblet reference {v:?} at word {at} meets a forwarding pointer"))?;
                let head = read_head(self.mem.words(), main);
                if main + 1 + head.fields != p {
                    return Err(format!(
                        "bloblet reference {v:?} at word {at} is not at the start of its suffix"
                    ));
                }
            }
            if v.is_pair() && is_header(self.word(self.ix(v))) {
                return Err(format!(
                    "pair reference {v:?} at word {at} lands on a header"
                ));
            }
        }
        Ok(())
    }
}

/// Where a collection copies to: the heap's to-space, and each live reap's
/// new chunks.
struct Copier<'r> {
    /// Where the heap's memory starts, in words (`Heap::base`).
    base: usize,
    from: usize,
    to: usize,
    /// Words used in to-space.
    free: usize,
    /// Each live reap's chunks before this collection, by where they start,
    /// with its handle: what is copied out of them.
    owner: HashMap<usize, usize>,
    /// Each region's new chunks, by handle, and how far each is filled
    /// (none for an arena).
    new: Vec<Vec<(usize, usize)>>,
    /// The quarantined chunks a reference was found into.
    marked: HashSet<usize>,
    /// The code area's bloblets found live, by main header, and those not
    /// yet scanned.
    code_marks: HashSet<usize>,
    code_gray: Vec<usize>,
    regions: &'r mut regions::Regions,
    /// Whether this is a minor collection, which copies the nursery's
    /// objects to the end of the old space and nothing else.
    minor: bool,
    /// The crossing map, kept as objects are copied into the old space; and
    /// the card the last one started in.
    crossing: &'r mut fixpt_memmgmt::Words,
    last_card: usize,
}

impl Copier<'_> {
    /// `n` words to copy into: in reap `reap`'s new chunks, or, for the
    /// heap's objects (or if the reaps' area is used up), in to-space.
    #[inline(always)]
    fn alloc(&mut self, reap: Option<usize>, n: usize) -> usize {
        if let Some(h) = reap {
            if let Some((start, fill)) = self.new[h].last_mut()
                && *fill + n <= *start + regions::CHUNK_WORDS
            {
                let at = *fill;
                *fill += n;
                return at;
            }
            if let Some(chunk) = self.regions.reap_chunk() {
                self.new[h].push((chunk, chunk + n));
                return chunk;
            }
        }
        let at = self.to + self.free;
        self.free += n;
        self.crossed(at, n);
        at
    }
}

/// Every reference in `words`, a sequence of objects and pairs as a
/// semispace is, replaced by `f` of it.
fn map_refs(words: &mut [u64], f: impl Fn(Value) -> Value) {
    let mut scan = 0;
    while scan < words.len() {
        let w = words[scan];
        if is_header(w) {
            let main = scan + is_extension(w) as usize;
            let head = read_head(words, main);
            for i in 0..head.fields {
                words[main + 1 + i] = f(Value(words[main + 1 + i])).raw();
            }
            scan += head.size();
        } else {
            words[scan] = f(Value(words[scan])).raw();
            words[scan + 1] = f(Value(words[scan + 1])).raw();
            scan += 2;
        }
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
