//! Uninterned symbols, gensyms among them, and the handles the Rust side
//! holds of symbols (`heap/gensym.rs`; `TODO.md` §292).

use fixpt_heap::{Heap, UNINTERNED_HANDLES, Value, image};

/// A gensym's name is its parts', made when asked for; it is equal to no
/// other symbol, the interned one of its name nor another of its parts.
#[test]
fn a_gensym_is_named_by_its_parts_and_is_itself_alone() {
    let mut h = Heap::new();
    let x = h.intern("x");
    let g = h.make_gensym("%", x, ":3.1");
    assert_eq!(h.symbol_name(g), "%x:3.1");
    assert!(h.is_uninterned_symbol(g) && !h.is_interned_symbol(g));
    assert_ne!(g, h.intern("%x:3.1"), "not the interned symbol of its name");
    assert_eq!(h.interned("%x:3.1").map(|s| s == g), Some(false));
    let g2 = h.make_gensym("%", x, ":3.1");
    assert_ne!(g, g2, "nor another of its parts");
    // Seeded by a gensym: the seed's name inside.
    let gg = h.make_gensym("%~", g, "");
    assert_eq!(h.symbol_name(gg), "%~%x:3.1");
    let (p, seed, s) = h.gensym_parts(gg).unwrap();
    assert_eq!((h.string_to_rust(p), seed, h.string_to_rust(s)), ("%~".into(), g, "".into()));
    assert!(h.gensym_parts(x).is_none());
    // `symbol->string`'s: made once, then the same string.
    let n = h.symbol_name_string(gg);
    assert_eq!(h.string_to_rust(n), "%~%x:3.1");
    assert_eq!(h.symbol_name_string(gg), n);
    // An uninterned symbol of a name.
    let u = h.make_uninterned_symbol("x");
    assert_eq!(h.symbol_name(u), "x");
    assert_ne!(u, x);
    h.verify().unwrap();
}

/// Names compared, gensyms' too, as their texts.
#[test]
fn gensyms_compare_by_their_names() {
    let mut h = Heap::new();
    let a = h.intern("a");
    let syms = [h.intern("%a:1"), h.make_gensym("%", a, ":2"), h.make_gensym("%", a, ":1"), h.intern("b"), h.make_uninterned_symbol("")];
    for &s in &syms {
        for &t in &syms {
            assert_eq!(h.symbol_cmp(s, t), h.symbol_name(s).cmp(&h.symbol_name(t)));
        }
    }
}

/// A handle names its symbol the same through collections, an interned
/// symbol's its place; released ones are made again, and name no symbol
/// they did not.
#[test]
fn a_handle_names_its_symbol_until_released() {
    let mut h = Heap::new();
    let x = h.intern("x");
    let hx = h.symbol_handle(x);
    assert!(hx < UNINTERNED_HANDLES);
    assert_eq!(h.symbol_handle(x), hx);
    let mark = h.symbol_handles_mark();
    let gs: Vec<Value> = (0..100).map(|i| h.make_gensym("%", x, &format!(":{i}"))).collect();
    let hs: Vec<u32> = gs.iter().map(|&g| h.symbol_handle(g)).collect();
    assert!(hs.iter().all(|&k| k >= UNINTERNED_HANDLES));
    assert_eq!(hs.iter().collect::<fixpt_heap::HashSet<_>>().len(), 100, "each its own");
    // Held by the handles alone, through a minor and a major collection.
    drop(gs);
    for major in [false, true] {
        if major {
            h.collect(&mut []);
        } else {
            h.collect_young(&mut []);
        }
        h.verify().unwrap();
        for (i, &k) in hs.iter().enumerate() {
            let g = h.handle_symbol(k).unwrap();
            assert_eq!(h.symbol_name(g), format!("%x:{i}"));
            assert_eq!(h.symbol_handle(g), k, "the same handle, the symbol moved");
        }
    }
    let x = h.intern("x");
    assert_eq!(h.handle_symbol(hx), Some(x), "the interned symbol, where it is now");
    // Released: a symbol held otherwise is given a new one, and the old
    // names it no more.
    let mut keep = [h.handle_symbol(hs[7]).unwrap()];
    h.release_symbol_handles(mark);
    assert_eq!(h.handle_symbol(hs[7]), None);
    let other = h.make_gensym("%", x, ":other");
    let ho = h.symbol_handle(other);
    assert_eq!(ho, hs[0], "a released handle made again");
    h.collect(&mut [&mut keep]);
    let k7 = h.symbol_handle(keep[0]);
    assert_ne!(k7, hs[7]);
    assert_eq!(h.handle_symbol(k7), Some(keep[0]));
    assert_eq!(h.handle_symbol(ho).map(|s| h.symbol_name(s)), Some("%x:other".into()));
    let x = h.intern("x");
    assert_eq!(h.symbol_handle(x), hx, "an interned symbol's is permanent");
}

/// Nothing but what holds a gensym keeps it: making one leaves no trace.
#[test]
fn a_gensym_no_one_holds_is_collected() {
    let mut h = Heap::new();
    let x = h.intern("x");
    let g = h.make_gensym("%", x, ":1");
    let w = h.weak_add(g);
    let held = h.make_gensym("%", x, ":2");
    let wh = h.weak_add(held);
    let k = h.symbol_handle(held);
    let symbols = h.symbol_count();
    h.collect(&mut []);
    assert_eq!(h.weak_get(w), None, "collected");
    assert!(h.weak_get(wh).is_some(), "held by its handle");
    assert_eq!(h.symbol_count(), symbols, "no symbol interned");
    h.release_symbol_handles(0);
    h.collect(&mut []);
    assert_eq!(h.weak_get(wh), None, "released, then collected");
    assert_eq!(h.handle_symbol(k), None);
}

/// A gensym in an image, loaded or copied into another heap, is its own
/// there, its name as it was; the handle its record names is not taken
/// for another's.
#[test]
fn a_gensym_carried_elsewhere_is_its_own_there() {
    let mut h = Heap::new();
    let x = h.intern("x");
    let g = h.make_gensym("%", x, ":1");
    assert!(h.symbol_handle(g) >= UNINTERNED_HANDLES);
    let l = h.cons(g, Value::NULL);
    let l = h.cons(g, l);
    h.push_root(l);
    for dump in [image::dump_packed, image::dump_static] {
        let mut back = image::load(&dump(&h)).unwrap();
        let l = back.root_at(0);
        let (a, b) = (back.car(l), back.car(back.cdr(l)));
        assert_eq!(a, b, "one gensym, shared");
        assert_eq!(back.symbol_name(a), "%x:1");
        assert!(back.is_uninterned_symbol(a));
        assert_ne!(Some(a), back.interned("%x:1"));
        // Its record names a handle of the heap it was made in: not this
        // one's, whose table is empty, nor, once there is one, another's.
        let other = back.make_uninterned_symbol("y");
        let ko = back.symbol_handle(other);
        let ka = back.symbol_handle(a);
        assert_ne!(ka, ko);
        assert_eq!(back.handle_symbol(ka), Some(a));
        assert_eq!(back.handle_symbol(ko), Some(other));
        // Its name made and kept: where its record is static, not kept,
        // made each time the same.
        let n = back.symbol_name_string(a);
        assert_eq!(back.string_to_rust(n), "%x:1");
        back.verify().unwrap();
    }
    let mut c = Heap::new();
    let y = c.make_uninterned_symbol("y");
    let ky = c.symbol_handle(y);
    let copied = c.copy_graph_from(&h, l);
    let a = c.car(copied);
    assert_eq!(c.car(c.cdr(copied)), a);
    assert_eq!(c.symbol_name(a), "%x:1");
    assert_ne!(c.symbol_handle(a), ky, "the copy's record names no handle of this heap's");
    c.verify().unwrap();
}

/// An uninterned symbol whose name is interned is copied as itself, not
/// made the interned one.
#[test]
fn copying_keeps_an_uninterned_symbol_uninterned() {
    let mut h = Heap::new();
    h.intern("x");
    let u = h.make_uninterned_symbol("x");
    let mut c = Heap::new();
    let x = c.intern("x");
    let v = c.copy_graph_from(&h, u);
    assert_ne!(v, x);
    assert!(c.is_uninterned_symbol(v));
    assert_eq!(c.symbol_name(v), "x");
}
