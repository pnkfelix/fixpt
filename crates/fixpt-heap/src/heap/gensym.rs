//! Uninterned symbols, gensyms among them, and the handles the Rust side
//! holds of every symbol (`TODO.md` §292, the user's, 2026-11-17).
//!
//! A symbol is three fields, `[name, hash, global-slot]`, wherever it is
//! made (compiled code reads the hash at its offset). An interned symbol's
//! name is a text, a name of its heap's (`Heap::text`). An uninterned one's
//! field 0 is a record instead,
//! `[name, prefix, seed, handle]`: its name is `prefix`, then `seed`'s
//! name if `seed` is a symbol, made the first time
//! it is asked for and kept in `name` (`#f` until then), so a gensym that is
//! never printed never has one, and the name is the same whenever it is
//! made, from no counter. A gensym is equal to itself alone (`eq?`,
//! `symbol=?`): never to an interned symbol, nor to another of the same
//! parts. Its hash is made from its parts when it is made.
//!
//! The Rust side holds a symbol by a `SymbolRef` (`Heap::symbol_ref`): an
//! interned one's place pinned; an uninterned one's in an entry of
//! `sym_handles`, a table rooting what it holds, made the first time it is
//! held and recorded in the symbol's record (where the record cannot be
//! written, the static area's, in `static_sym_handles`). What a record says
//! is a hint, taken only if the table's entry is that symbol: a record
//! copied into another heap, or an image, or one whose entry was let go,
//! names no entry of this heap's that is not its own. An entry no ref holds
//! is let go before a collection, and before one is made, so that what
//! nothing else holds is collected ([`release_unheld`]).
//!
//! [`release_unheld`]: Heap::release_unheld

use super::*;

/// The fields of an uninterned symbol's record (its field 0).
const R_NAME: usize = 0;
const R_PREFIX: usize = 1;
const R_SEED: usize = 2;
const R_HANDLE: usize = 3;
const R_LEN: usize = 4;

impl Heap {
    /// A symbol `eq?` to no other, named `prefix`, then `seed`'s name, its
    /// name made when first asked for (a gensym; `seed` a symbol, kept for
    /// the name and for what reads it, [`gensym_parts`](Heap::gensym_parts)).
    pub fn make_gensym(&mut self, prefix: &str, seed: Value) -> Value {
        debug_assert!(self.is_a(seed, ObjType::Symbol));
        let p = self.make_string(prefix);
        self.gensym_of(p, seed)
    }

    /// [`make_gensym`](Heap::make_gensym) of heap string `prefix`, copied
    /// (the gensym's name is what it says now).
    pub fn make_gensym_of_string(&mut self, prefix: Value, seed: Value) -> Value {
        debug_assert!(self.is_a(seed, ObjType::Symbol));
        let p = self.string_append(&[prefix]);
        self.gensym_of(p, seed)
    }

    /// A symbol `eq?` to no other, not even the interned symbol `name`: to
    /// carry an identifier's identity into Scheme code (a procedural
    /// macro's input) and back. It has no global slot.
    pub fn make_uninterned_symbol(&mut self, name: &str) -> Value {
        let p = self.make_string(name);
        self.gensym_of(p, Value::FALSE)
    }

    /// An uninterned symbol of string `prefix`, which is its own, and seed
    /// `seed`.
    fn gensym_of(&mut self, prefix: Value, seed: Value) -> Value {
        let seed_hash = if seed.is_ref() { self.fixed(seed, 3, 1).as_fixnum() as u64 } else { 0 };
        let h = (self.string_fnv(prefix) ^ seed_hash.rotate_left(17)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        // As long as anything holds it: not in a region, which may end
        // while it is held (no `letregion` discharges making one).
        let region = self.regions.target.take();
        let record = self.make_vector(R_LEN, Value::FALSE);
        self.obj_set(record, R_PREFIX, prefix);
        self.obj_set(record, R_SEED, seed);
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
        self.is_a(sym, ObjType::Symbol) && !self.fixed(sym, 3, 0).is_text()
    }

    /// An uninterned symbol's record.
    fn record(&self, sym: Value) -> Option<Value> {
        let r = self.fixed(sym, 3, 0);
        (!r.is_text()).then_some(r)
    }

    /// An uninterned symbol's prefix, a string, and seed (`#f` if none).
    pub fn gensym_parts(&self, sym: Value) -> Option<(Value, Value)> {
        let r = self.record(sym)?;
        Some((self.obj_ref(r, R_PREFIX), self.obj_ref(r, R_SEED)))
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
        loop {
            let Some(r) = self.record(sym) else {
                out.push_str(self.interned_name(sym));
                break;
            };
            let name = self.obj_ref(r, R_NAME);
            if name.is_ref() {
                self.string_into(name, out);
                break;
            }
            self.string_into(self.obj_ref(r, R_PREFIX), out);
            let seed = self.obj_ref(r, R_SEED);
            if !seed.is_ref() {
                break;
            }
            sym = seed;
        }
    }

    /// Interned symbol `sym`'s name, where its heap keeps it.
    #[inline]
    fn interned_name(&self, sym: Value) -> &str {
        self.text_of(self.fixed(sym, 3, 0)).expect("an interned symbol's name is a name of its heap's")
    }

    /// A new string of interned symbol `sym`'s name: the name copied first,
    /// the heap's names borrowed no longer than that, as making the string
    /// takes the heap.
    fn interned_name_string(&mut self, sym: Value) -> Value {
        let mut name = std::mem::take(&mut self.name_buf);
        name.clear();
        name.push_str(self.interned_name(sym));
        let s = self.make_string(&name);
        self.name_buf = name;
        s
    }

    /// Symbol `sym`'s name, a new string (`symbol->string`).
    pub fn symbol_to_string(&mut self, sym: Value) -> Value {
        debug_assert!(self.is_a(sym, ObjType::Symbol));
        if self.record(sym).is_none() {
            return self.interned_name_string(sym);
        }
        let name = self.symbol_name_string(sym);
        self.string_append(&[name])
    }

    /// A string that is symbol `sym`'s name: an uninterned one's own, made
    /// and kept if it had none (but where its record cannot be written,
    /// the static area's), not to be written; an interned one's, made.
    pub fn symbol_name_string(&mut self, sym: Value) -> Value {
        debug_assert!(self.is_a(sym, ObjType::Symbol));
        let Some(r) = self.record(sym) else { return self.interned_name_string(sym) };
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

    /// Two symbols' names compared, as `string_cmp`, by code points (UTF-8's
    /// order is theirs), with nothing copied where both are interned.
    pub fn symbol_cmp(&self, a: Value, b: Value) -> std::cmp::Ordering {
        debug_assert!(self.is_a(a, ObjType::Symbol) && self.is_a(b, ObjType::Symbol));
        match (self.record(a), self.record(b)) {
            (None, None) => self.interned_name(a).cmp(self.interned_name(b)),
            _ => self.symbol_name(a).cmp(&self.symbol_name(b)),
        }
    }

    // ------------------------------------------------------------ handles
    /// Uninterned symbol `sym`'s entry among those held: its own, the same
    /// while some ref holds it; made if it has none.
    pub(super) fn uninterned_entry(&mut self, sym: Value) -> symref::HandleIx {
        let r = self.record(sym).expect("an uninterned symbol");
        if let Some(j) = self.uninterned_handle(sym, r) {
            return j;
        }
        self.debug_held(sym);
        if self.handle_free.is_empty() {
            self.release_unheld();
        }
        let j = match self.handle_free.pop() {
            Some(j) => {
                self.sym_handles[j.index()] = Some(sym);
                j
            }
            None => {
                self.sym_handles.push(Some(sym));
                symref::HandleIx::new(self.sym_handles.len() - 1)
            }
        };
        if self.is_static(r) {
            self.static_sym_handles.insert(sym.raw(), j);
        } else {
            self.obj_set(r, R_HANDLE, Value::fixnum(j.index() as i64));
        }
        j
    }

    /// Uninterned symbol `sym`'s entry, if it has one: what its record
    /// says, if the table's entry there is `sym`.
    fn uninterned_handle(&self, sym: Value, r: Value) -> Option<symref::HandleIx> {
        let j = if self.is_static(r) {
            *self.static_sym_handles.get(&sym.raw())?
        } else {
            let f = self.obj_ref(r, R_HANDLE);
            if !f.is_fixnum() {
                return None;
            }
            symref::HandleIx::new(usize::try_from(f.as_fixnum()).ok()?)
        };
        (self.sym_handles.get(j.index()) == Some(&Some(sym))).then_some(j)
    }

    /// Every entry of the uninterned symbols held that no ref holds now let
    /// go, free to be made again: what only it held is collected.
    pub(super) fn release_unheld(&mut self) {
        for i in 0..self.sym_handles.len() {
            let j = symref::HandleIx::new(i);
            if self.sym_handles[i].is_some() && !self.pins.pinned(symref::Held::Handle(j)) {
                self.sym_handles[i] = None;
                self.handle_free.push(j);
            }
        }
        let held = &self.sym_handles;
        self.static_sym_handles.retain(|&raw, j| held[j.index()].is_some_and(|s| s.raw() == raw));
    }
}
