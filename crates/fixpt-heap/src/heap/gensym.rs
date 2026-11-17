//! Uninterned symbols, gensyms among them, and the handles the Rust side
//! holds of every symbol (`TODO.md` §292, the user's, 2026-11-17).
//!
//! A symbol is three fields, `[name, hash, global-slot]`, wherever it is
//! made (compiled code reads the hash at its offset). An interned symbol's
//! name is its string. An uninterned one's field 0 is a record instead,
//! `[name, prefix, seed, suffix, handle]`: its name is `prefix`, then
//! `seed`'s name if `seed` is a symbol, then `suffix`, made the first time
//! it is asked for and kept in `name` (`#f` until then), so a gensym that is
//! never printed never has one, and the name is the same whenever it is
//! made, from no counter. A gensym is equal to itself alone (`eq?`,
//! `symbol=?`): never to an interned symbol, nor to another of the same
//! parts. Its hash is made from its parts when it is made.
//!
//! A handle names a symbol to the Rust side, the same kind for every
//! symbol, one for each: an interned symbol's is its place in the symbols
//! table (its global slot, the two tables pushed together); an uninterned
//! one's is `UNINTERNED_HANDLES` and its place in `sym_handles`, a table
//! rooting what it holds, made the first time it is asked for and recorded
//! in the symbol's record (where the record cannot be written, the static
//! area's, in `static_sym_handles`). What a record says is a hint, taken
//! only if the table's entry is that symbol: a record copied into another
//! heap, or an image, or one whose handle was released, names no entry of
//! this heap's that is not its own. Handles are released by a mark, as a
//! session drops what it held ([`release_symbol_handles`]).
//!
//! [`release_symbol_handles`]: Heap::release_symbol_handles

use super::*;

/// The fields of an uninterned symbol's record (its field 0).
const R_NAME: usize = 0;
const R_PREFIX: usize = 1;
const R_SEED: usize = 2;
const R_SUFFIX: usize = 3;
const R_HANDLE: usize = 4;
const R_LEN: usize = 5;

/// The first handle of an uninterned symbol: `UNINTERNED_HANDLES + j` is
/// `sym_handles[j]`'s; an interned symbol's handle is below it.
pub const UNINTERNED_HANDLES: u32 = 1 << 31;

impl Heap {
    /// A symbol `eq?` to no other, named `prefix`, then `seed`'s name, then
    /// `suffix`, its name made when first asked for (a gensym; `seed` a
    /// symbol, kept for the name and for what reads it, `fresh_seed`).
    pub fn make_gensym(&mut self, prefix: &str, seed: Value, suffix: &str) -> Value {
        debug_assert!(self.is_a(seed, ObjType::Symbol));
        let (p, s) = (self.make_string(prefix), self.make_string(suffix));
        self.gensym_of(p, seed, s)
    }

    /// [`make_gensym`](Heap::make_gensym) of heap strings `prefix` and
    /// `suffix`, copied (the gensym's name is what they say now).
    pub fn make_gensym_of_strings(&mut self, prefix: Value, seed: Value, suffix: Value) -> Value {
        debug_assert!(self.is_a(seed, ObjType::Symbol));
        let p = self.string_append(&[prefix]);
        let s = self.string_append(&[suffix]);
        self.gensym_of(p, seed, s)
    }

    /// A symbol `eq?` to no other, not even the interned symbol `name`: to
    /// carry an identifier's identity into Scheme code (a procedural
    /// macro's input) and back. It has no global slot.
    pub fn make_uninterned_symbol(&mut self, name: &str) -> Value {
        let (p, s) = (self.make_string(name), self.make_string(""));
        self.gensym_of(p, Value::FALSE, s)
    }

    /// An uninterned symbol of strings `prefix` and `suffix`, which are its
    /// own, and seed `seed`.
    fn gensym_of(&mut self, prefix: Value, seed: Value, suffix: Value) -> Value {
        let seed_hash = if seed.is_ref() { self.fixed(seed, 3, 1).as_fixnum() as u64 } else { 0 };
        let h = (self.string_fnv(prefix) ^ seed_hash.rotate_left(17)).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ self.string_fnv(suffix);
        // As long as anything holds it: not in a region, which may end
        // while it is held (no `letregion` discharges making one).
        let region = self.regions.target.take();
        let record = self.make_vector(R_LEN, Value::FALSE);
        self.obj_set(record, R_PREFIX, prefix);
        self.obj_set(record, R_SEED, seed);
        self.obj_set(record, R_SUFFIX, suffix);
        let sym = self.alloc(ObjType::Symbol, 3, Value::fixnum(0));
        self.regions.target = region;
        self.obj_set(sym, 0, record);
        self.obj_set(sym, 1, Value::fixnum_wrapping(h as i64 & i64::MAX));
        self.obj_set(sym, 2, Value::fixnum(-1));
        sym
    }

    /// Whether symbol `sym` is uninterned (its field 0 a record).
    #[inline]
    pub fn is_uninterned_symbol(&self, sym: Value) -> bool {
        self.is_a(sym, ObjType::Symbol) && !self.is_a(self.fixed(sym, 3, 0), ObjType::String)
    }

    /// An uninterned symbol's record.
    fn record(&self, sym: Value) -> Option<Value> {
        let r = self.fixed(sym, 3, 0);
        (!self.is_a(r, ObjType::String)).then_some(r)
    }

    /// An uninterned symbol's seed and the strings before and after it.
    pub fn gensym_parts(&self, sym: Value) -> Option<(Value, Value, Value)> {
        let r = self.record(sym)?;
        Some((self.obj_ref(r, R_PREFIX), self.obj_ref(r, R_SEED), self.obj_ref(r, R_SUFFIX)))
    }

    /// Symbol `sym`'s name, made where it has none yet (and not kept: see
    /// [`symbol_name_string`](Heap::symbol_name_string)).
    pub fn symbol_name(&self, sym: Value) -> String {
        debug_assert!(self.is_a(sym, ObjType::Symbol));
        let mut out = String::new();
        self.symbol_name_into(sym, &mut out);
        out
    }

    /// Symbol `sym`'s name onto `out`.
    pub fn symbol_name_into(&self, sym: Value, out: &mut String) {
        let mut sym = sym;
        // A seed's seed's, ..., each's suffix after: kept to be written
        // last, the innermost first.
        let mut after = Vec::new();
        loop {
            let Some(r) = self.record(sym) else {
                self.string_into(self.fixed(sym, 3, 0), out);
                break;
            };
            let name = self.obj_ref(r, R_NAME);
            if name.is_ref() {
                self.string_into(name, out);
                break;
            }
            self.string_into(self.obj_ref(r, R_PREFIX), out);
            after.push(self.obj_ref(r, R_SUFFIX));
            let seed = self.obj_ref(r, R_SEED);
            if !seed.is_ref() {
                break;
            }
            sym = seed;
        }
        for s in after.into_iter().rev() {
            self.string_into(s, out);
        }
    }

    /// The string that is symbol `sym`'s name, itself, made and kept if it
    /// had none (but where its record cannot be written, the static
    /// area's): the symbol's, not to be written (`symbol->string` copies
    /// it).
    pub fn symbol_name_string(&mut self, sym: Value) -> Value {
        debug_assert!(self.is_a(sym, ObjType::Symbol));
        let Some(r) = self.record(sym) else { return self.fixed(sym, 3, 0) };
        let name = self.obj_ref(r, R_NAME);
        if name.is_ref() {
            return name;
        }
        let text = self.symbol_name(sym);
        let s = self.make_string(&text);
        if !self.is_static(r) {
            self.obj_set(r, R_NAME, s);
        }
        s
    }

    /// Two symbols' names compared, as `string_cmp`, with nothing copied
    /// where both are interned.
    pub fn symbol_cmp(&self, a: Value, b: Value) -> std::cmp::Ordering {
        debug_assert!(self.is_a(a, ObjType::Symbol) && self.is_a(b, ObjType::Symbol));
        let (x, y) = (self.fixed(a, 3, 0), self.fixed(b, 3, 0));
        if self.is_a(x, ObjType::String) && self.is_a(y, ObjType::String) {
            return self.string_cmp(x, y);
        }
        // By code points, as `string_cmp`: UTF-8's order is theirs.
        self.symbol_name(a).cmp(&self.symbol_name(b))
    }

    // ------------------------------------------------------------ handles
    /// Symbol `sym`'s handle: the same each time it is asked for, until
    /// released, and another symbol's never.
    pub fn symbol_handle(&mut self, sym: Value) -> u32 {
        debug_assert!(self.is_a(sym, ObjType::Symbol));
        let Some(r) = self.record(sym) else {
            let i = self.fixed(sym, 3, 2).as_fixnum();
            assert!((0..UNINTERNED_HANDLES as i64).contains(&i), "an interned symbol's place");
            debug_assert_eq!(self.table_get(Which::Symbols, i as usize), sym);
            return i as u32;
        };
        if let Some(h) = self.uninterned_handle(sym, r) {
            return h;
        }
        let j = self.sym_handles.len();
        assert!(j < UNINTERNED_HANDLES as usize, "too many symbols held");
        self.sym_handles.push(sym);
        if self.is_static(r) {
            self.static_sym_handles.insert(sym.raw(), j as u32);
        } else {
            self.obj_set(r, R_HANDLE, Value::fixnum(j as i64));
        }
        UNINTERNED_HANDLES + j as u32
    }

    /// Uninterned symbol `sym`'s handle, if it has one: what its record
    /// says, if the table's entry there is `sym`.
    fn uninterned_handle(&self, sym: Value, r: Value) -> Option<u32> {
        let j = if self.is_static(r) {
            *self.static_sym_handles.get(&sym.raw())? as usize
        } else {
            let f = self.obj_ref(r, R_HANDLE);
            if !f.is_fixnum() {
                return None;
            }
            usize::try_from(f.as_fixnum()).ok()?
        };
        (self.sym_handles.get(j) == Some(&sym)).then_some(UNINTERNED_HANDLES + j as u32)
    }

    /// The symbol handle `h` names, if any.
    pub fn handle_symbol(&self, h: u32) -> Option<Value> {
        if h < UNINTERNED_HANDLES {
            ((h as usize) < self.symbols.len).then(|| self.table_get(Which::Symbols, h as usize))
        } else {
            self.sym_handles.get((h - UNINTERNED_HANDLES) as usize).copied()
        }
    }

    /// What [`release_symbol_handles`](Heap::release_symbol_handles)
    /// releases back to: the uninterned symbols' handles made after it.
    pub fn symbol_handles_mark(&self) -> usize {
        self.sym_handles.len()
    }

    /// Every uninterned symbol's handle made since `mark` released, the
    /// symbols no longer held by them, and the handles made again.
    pub fn release_symbol_handles(&mut self, mark: usize) {
        if mark >= self.sym_handles.len() {
            return;
        }
        self.sym_handles.truncate(mark);
        self.static_sym_handles.retain(|_, j| (*j as usize) < mark);
    }
}
