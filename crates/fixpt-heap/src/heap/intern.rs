//! Interned data (`TODO.md` §51): immutable, acyclic data made canonical,
//! as symbols are, so that equal data a program quotes are one object,
//! whichever machine made them, and `eq?` on them says what `equal?` would.
//! R7RS leaves `(eq? '(a) '(a))` unspecified, so sharing is allowed.
//!
//! Hash-consing, bottom up: a pair is found by its car and cdr once those
//! are interned, a string, float or vector by its contents (a vector's
//! elements interned). Symbols and immediates are canonical already.
//!
//! The table is in the heap, so that an image keeps it (`dump-heap`): the
//! global of a symbol of its own, a vector `[stamp, count, buckets]`;
//! `buckets` a vector of chains, an entry a vector `[object, next]`, `next`
//! another entry or `#f`. A pair's hash is of its parts' addresses, which a
//! collection moves, so the table is stamped with the heap's count of
//! collections when it was last hashed, and an intern that finds the count
//! moved relinks every entry first, as an `eqtable` does
//! (`fixpt_runtime::eqtable`). Allocation never collects outside a
//! safepoint, so nothing moves during an intern. The entries are held
//! strongly: what is interned is what programs quote, which their code
//! holds anyway, so a weak table would free little.

use super::Heap;
use crate::value::{ObjType, Value};

const STAMP: usize = 0;
const COUNT: usize = 1;
const BUCKETS: usize = 2;
const OBJECT: usize = 0;
const NEXT: usize = 1;

/// The global the table is in.
const TABLE: &str = "%fx26-interned-data";

fn mix(h: u64, x: u64) -> u64 {
    // SplitMix64's finalizer, over the running hash and the next word.
    let mut z = h ^ x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

impl Heap {
    /// `v`, data nothing will write and no cycle runs through, made the one
    /// object equal to it: the interned one if there is one, else `v`
    /// itself (or, of a pair or vector whose parts were not interned, a
    /// copy over the interned parts), interned from now on.
    pub fn intern_datum(&mut self, v: Value) -> Value {
        let candidate = if v.is_pair() {
            let (a, d) = (self.car(v), self.cdr(v));
            let (ia, id) = (self.intern_datum(a), self.intern_datum(d));
            if ia == a && id == d { v } else { self.cons(ia, id) }
        } else {
            match self.obj_type(v) {
                Some(ObjType::String | ObjType::Flonum) => v,
                Some(ObjType::Vector) => {
                    let items: Vec<Value> = (0..self.obj_len(v)).map(|i| self.obj_ref(v, i)).collect();
                    let canon: Vec<Value> = items.iter().map(|x| self.intern_datum(*x)).collect();
                    if canon == items { v } else { self.vector_from(&canon) }
                }
                _ => return v,
            }
        };
        let t = self.interned_table();
        let h = self.datum_hash(candidate);
        let buckets = self.obj_ref(t, BUCKETS);
        let n = self.obj_len(buckets);
        let mut e = self.obj_ref(buckets, (h % n as u64) as usize);
        while !e.is_false() {
            let o = self.obj_ref(e, OBJECT);
            if self.datum_same(o, candidate) {
                return o;
            }
            e = self.obj_ref(e, NEXT);
        }
        let entry = self.make_vector(2, Value::FALSE);
        self.obj_set(entry, OBJECT, candidate);
        self.obj_set(entry, NEXT, self.obj_ref(buckets, (h % n as u64) as usize));
        self.obj_set(buckets, (h % n as u64) as usize, entry);
        let count = self.obj_ref(t, COUNT).as_fixnum() + 1;
        self.obj_set(t, COUNT, Value::fixnum(count));
        if count as usize > 2 * n {
            self.interned_relink(t, 4 * n);
        }
        candidate
    }

    /// The table, made if there is none, its entries hashed as their parts'
    /// addresses are now.
    fn interned_table(&mut self) -> Value {
        let sym = self.intern(TABLE);
        let slot = self.symbol_global_slot(sym);
        let t = self.global(slot);
        if self.obj_type(t) != Some(ObjType::Vector) {
            let buckets = self.make_vector(64, Value::FALSE);
            let t = self.make_vector(3, Value::FALSE);
            self.obj_set(t, STAMP, Value::fixnum(self.collections() as i64));
            self.obj_set(t, COUNT, Value::fixnum(0));
            self.obj_set(t, BUCKETS, buckets);
            self.set_global(slot, t);
            return t;
        }
        if self.obj_ref(t, STAMP).as_fixnum() != self.collections() as i64 {
            let n = self.obj_len(self.obj_ref(t, BUCKETS));
            self.interned_relink(t, n);
        }
        t
    }

    /// Every entry of table `t` linked into `n` new buckets by its hash now,
    /// and the table stamped.
    fn interned_relink(&mut self, t: Value, n: usize) {
        let old = self.obj_ref(t, BUCKETS);
        let mut entries = Vec::new();
        for i in 0..self.obj_len(old) {
            let mut e = self.obj_ref(old, i);
            while !e.is_false() {
                entries.push(e);
                e = self.obj_ref(e, NEXT);
            }
        }
        let buckets = self.make_vector(n, Value::FALSE);
        for e in entries {
            let b = (self.datum_hash(self.obj_ref(e, OBJECT)) % n as u64) as usize;
            self.obj_set(e, NEXT, self.obj_ref(buckets, b));
            self.obj_set(buckets, b, e);
        }
        self.obj_set(t, BUCKETS, buckets);
        self.obj_set(t, STAMP, Value::fixnum(self.collections() as i64));
    }

    /// An interned object's hash: of a pair's parts' addresses, a string's
    /// characters, a float's bits, a vector's elements' addresses.
    fn datum_hash(&self, o: Value) -> u64 {
        if o.is_pair() {
            return mix(mix(1, self.car(o).raw()), self.cdr(o).raw());
        }
        match self.obj_type(o) {
            Some(ObjType::String) => mix(2, crate::heap::string_hash_of(&self.string_to_rust(o)) as u64),
            Some(ObjType::Flonum) => mix(3, self.flonum_value(o).to_bits()),
            Some(ObjType::Vector) => (0..self.obj_len(o)).fold(4, |h, i| mix(h, self.obj_ref(o, i).raw())),
            _ => 0,
        }
    }

    /// Whether interned `o` and candidate `c` are equal: the same parts (by
    /// identity, both interned), characters or bits.
    fn datum_same(&self, o: Value, c: Value) -> bool {
        if o.is_pair() || c.is_pair() {
            return o.is_pair() && c.is_pair() && self.car(o) == self.car(c) && self.cdr(o) == self.cdr(c);
        }
        match (self.obj_type(o), self.obj_type(c)) {
            (Some(ObjType::String), Some(ObjType::String)) => self.string_to_rust(o) == self.string_to_rust(c),
            (Some(ObjType::Flonum), Some(ObjType::Flonum)) => self.flonum_value(o).to_bits() == self.flonum_value(c).to_bits(),
            (Some(ObjType::Vector), Some(ObjType::Vector)) => {
                self.obj_len(o) == self.obj_len(c) && (0..self.obj_len(o)).all(|i| self.obj_ref(o, i) == self.obj_ref(c, i))
            }
            _ => false,
        }
    }
}
