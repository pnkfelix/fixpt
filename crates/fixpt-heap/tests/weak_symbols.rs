//! The symbols table weak (`TODO.md` §292, step 5, the user's design,
//! 2026-11-18): an interned symbol nothing reaches, no `SymbolRef` pins and
//! whose global is unbound is freed at a major collection, its name with
//! it unless a holder holds it, its place given to the next symbol made;
//! any other is kept. An image of a heap with free places carries them.

use fixpt_heap::{Heap, Value, image};

#[test]
fn a_symbol_nothing_needs_is_freed_by_a_major_collection() {
    let mut h = Heap::new();
    let before = h.symbol_count();
    h.intern("weak:gone");
    assert_eq!(h.symbol_count(), before + 1);
    // A minor collection keeps every symbol.
    h.collect_young(&mut []);
    assert!(h.interned("weak:gone").is_some());
    h.collect(&mut []);
    h.verify().unwrap();
    assert_eq!(h.interned("weak:gone"), None);
    assert_eq!(h.names().find("weak:gone"), None, "its name swept");
    assert_eq!(h.symbol_count(), before);
    // Its place given again: the tables no longer.
    let globals = h.global_count();
    let again = h.intern("weak:again");
    assert_eq!(h.global_count(), globals, "a free place taken");
    assert_eq!(h.symbol_name(again), "weak:again");
    assert_eq!(h.global_of(again), Value::UNBOUND);
    h.verify().unwrap();
}

#[test]
fn a_symbol_reached_pinned_or_bound_is_kept() {
    let mut h = Heap::new();
    let reached = h.intern("weak:reached");
    let l = h.cons(reached, Value::NULL);
    let root = h.push_root(l);
    let pinned = h.intern("weak:pinned");
    let pin = h.symbol_ref(pinned);
    let bound = h.intern("weak:bound");
    h.set_global_of(bound, Value::fixnum(3));
    h.intern("weak:not");
    for _ in 0..2 {
        h.collect(&mut []);
        h.verify().unwrap();
    }
    assert_eq!(h.car(h.root_at(root)), h.interned("weak:reached").unwrap());
    assert_eq!(h.symbol_name(h.symbol_of(&pin)), "weak:pinned");
    assert_eq!(h.global_of(h.interned("weak:bound").unwrap()), Value::fixnum(3));
    assert_eq!(h.interned("weak:not"), None);
    // Let go, then freed.
    drop(pin);
    h.collect(&mut []);
    assert_eq!(h.interned("weak:pinned"), None);
}

/// A name a holder holds outlives its symbol; the symbol made again is
/// another object, of the same name.
#[test]
fn a_held_name_outlives_its_symbol() {
    let mut h = Heap::new();
    let mut names = h.names().holder();
    let n = names.hold_text("weak:held");
    h.intern("weak:held");
    h.collect(&mut []);
    assert_eq!(h.interned("weak:held"), None);
    assert_eq!(names.get(n), Some("weak:held"));
    let again = h.intern_text(n);
    assert_eq!(h.symbol_name(again), "weak:held");
    drop(names);
    let l = h.cons(again, Value::NULL);
    h.push_root(l);
    h.collect(&mut []);
    assert_eq!(h.names().find("weak:held"), Some(n), "its symbol's");
}

/// An image of a heap with free places: loaded, and spliced, each place a
/// symbol's or free as it was, a free one taken by the next symbol made.
#[test]
fn an_image_carries_free_places() {
    let mut h = Heap::new();
    for i in 0..10 {
        h.intern(&format!("weak:img{i}"));
    }
    let kept = h.intern("weak:kept");
    h.set_global_of(kept, Value::fixnum(9));
    h.collect(&mut []);
    let count = h.symbol_count();
    for dump in [image::dump_packed, image::dump_static] {
        let bytes = dump(&h);
        let mut loaded = image::load(&bytes).unwrap();
        loaded.verify().unwrap();
        assert_eq!(loaded.symbol_count(), count);
        assert_eq!(loaded.global_of(loaded.interned("weak:kept").unwrap()), Value::fixnum(9));
        let globals = loaded.global_count();
        loaded.intern("weak:new");
        assert_eq!(loaded.global_count(), globals, "a free place the image carried, taken");
        loaded.verify().unwrap();
        let parts = image::parts(&bytes, true).unwrap();
        let mut other = Heap::new();
        other.splice_image(&parts, &[]).unwrap();
        other.verify().unwrap();
        assert_eq!(other.global_of(other.interned("weak:kept").unwrap()), Value::UNBOUND, "a splice carries no global");
    }
}
