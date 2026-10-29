//! An image put into a heap that holds something already
//! (`Heap::splice_image`, `TODO.md` §160): what it holds comes in as a copy
//! of its graph would, its interned symbols this heap's, and the heap sound
//! after, across collections.

use fixpt_heap::{Heap, Value, image, layout};

fn raw() -> u8 {
    layout::kind("bloblet")
}

/// A heap of its own holding `(code shared fresh "text" . 42)`, its code a
/// code bloblet whose fields are a pair and the symbol `shared`; dumped.
fn an_image() -> Vec<u8> {
    let mut h = Heap::new();
    let shared = h.intern("shared");
    let fresh = h.intern("only-in-the-image");
    let text = h.make_string("text");
    let pair = h.cons(Value::fixnum(1), Value::fixnum(2));
    let code = h.make_code_bloblet(raw(), 2, 16, false);
    h.set_bloblet_slot(code, 1, pair);
    h.set_bloblet_slot(code, 2, shared);
    let l = h.cons(text, Value::fixnum(42));
    let l = h.cons(fresh, l);
    let l = h.cons(shared, l);
    let l = h.cons(code, l);
    h.push_root(l);
    image::dump(&h)
}

fn collect(h: &mut Heap) {
    h.collect(&mut []);
    h.verify().unwrap_or_else(|e| panic!("after a collection: {e}"));
}

#[test]
fn a_spliced_image_is_its_graph_in_this_heap() {
    let bytes = an_image();
    let img = image::parts(&bytes, true).unwrap();
    let mut h = Heap::new();
    // Something here first, a symbol the image has too among it.
    let before = h.cons(Value::fixnum(7), Value::NULL);
    let mine = h.intern("shared");
    let r0 = h.push_root(before);
    let roots = h.splice_image(&img, &[]).unwrap();
    h.verify().unwrap();
    let r1 = h.push_root(roots[0]);
    for round in 0..2 {
        let l = h.root_at(r1);
        let code = h.car(l);
        assert!(h.is_code_bloblet(code), "round {round}: its code is code here");
        let pair = h.bloblet_slot(code, 1);
        assert_eq!((h.car(pair), h.cdr(pair)), (Value::fixnum(1), Value::fixnum(2)));
        let rest = h.cdr(l);
        let shared = h.intern("shared");
        assert_eq!(h.car(rest), shared, "an interned symbol is this heap's");
        assert_eq!(h.bloblet_slot(code, 2), shared);
        let fresh = h.car(h.cdr(rest));
        assert_eq!(h.intern_existing("only-in-the-image"), Some(fresh), "a new one is interned here");
        assert_ne!(h.symbol_global_slot(fresh), h.symbol_global_slot(shared));
        let rest = h.cdr(h.cdr(rest));
        assert_eq!(h.string_to_rust(h.car(rest)), "text");
        assert_eq!(h.cdr(rest), Value::fixnum(42));
        assert_eq!(h.car(h.root_at(r0)), Value::fixnum(7), "what was here stays");
        collect(&mut h);
    }
    assert_eq!(h.intern_existing("shared"), Some(h.car(h.cdr(h.root_at(r1)))));
    let _ = mine;
}

#[test]
fn a_splice_with_a_young_symbol_marks_its_card() {
    // A generational heap: a symbol interned just before is in the nursery,
    // and an old object of the image's that refers to it is remembered.
    let bytes = an_image();
    let img = image::parts(&bytes, true).unwrap();
    let mut h = Heap::new();
    if !h.is_generational() {
        return;
    }
    // A minor collection checks that no old reference to a young object
    // went unremembered.
    h.verify_barrier = true;
    h.intern("shared");
    let roots = h.splice_image(&img, &[]).unwrap();
    let r = h.push_root(roots[0]);
    h.collect_young(&mut []);
    h.verify().unwrap();
    let l = h.root_at(r);
    let sym = h.car(h.cdr(l));
    assert_eq!(h.symbol_name(sym), "shared", "the reference followed the symbol out of the nursery");
    assert_eq!(h.bloblet_slot(h.car(l), 2), sym);
}
