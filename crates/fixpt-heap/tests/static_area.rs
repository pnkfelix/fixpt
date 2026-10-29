//! The static area (`TODO.md` §161): what an image put there never moves,
//! nor is copied; its objects are roots, so what they refer to lives and
//! follows when it moves, by their dirty cards in a minor collection.

use fixpt_heap::{Heap, Value, image, layout};

/// A heap of its own holding `(7 "text" (1 . 2))`, dumped with its old
/// space as the image's static area.
fn a_static_image() -> Vec<u8> {
    let mut h = Heap::new();
    let text = h.make_string("text");
    let pair = h.cons(Value::fixnum(1), Value::fixnum(2));
    let l = h.cons(pair, Value::NULL);
    let l = h.cons(text, l);
    let l = h.cons(Value::fixnum(7), l);
    h.push_root(l);
    image::dump_static(&h)
}

fn spliced(h: &mut Heap) -> usize {
    let bytes = a_static_image();
    let img = image::parts(&bytes, true).unwrap();
    assert!(img.words.is_empty() && !img.statics.is_empty(), "the image's words are its static area's");
    let roots = h.splice_image(&img, &[]).unwrap();
    h.push_root(roots[0])
}

#[test]
fn a_static_image_stays_where_it_is_put() {
    let mut h = Heap::new();
    let r = spliced(&mut h);
    let l = h.root_at(r);
    assert!(h.is_static(l));
    let words = h.static_words();
    for round in 0..3 {
        h.collect(&mut []);
        h.verify().unwrap();
        assert_eq!(h.root_at(r), l, "round {round}: it did not move");
        assert_eq!(h.static_words(), words, "nor was copied");
        assert_eq!(h.car(l), Value::fixnum(7));
        assert_eq!(h.string_to_rust(h.car(h.cdr(l))), "text");
    }
}

#[test]
fn what_a_static_object_refers_to_lives_and_follows() {
    let mut h = Heap::new();
    h.verify_barrier = true;
    let r = spliced(&mut h);
    let l = h.root_at(r);
    // A young list stored into the static list's last pair: only the
    // static object refers to it.
    let young = h.make_string("young");
    let young = h.cons(young, Value::NULL);
    let last = h.cdr(h.cdr(l));
    h.set_car(last, young);
    h.collect_young(&mut []);
    h.verify().unwrap();
    let moved = h.car(last);
    assert_ne!(moved, young, "it moved out of the nursery, and the static field followed");
    assert_eq!(h.string_to_rust(h.car(moved)), "young");
    for _ in 0..2 {
        h.collect(&mut []);
        h.verify().unwrap();
        assert_eq!(h.string_to_rust(h.car(h.car(last))), "young");
    }
    assert_eq!(h.root_at(r), l);
}

#[test]
fn a_heap_with_a_static_area_is_dumped_with_it() {
    let mut h = Heap::new();
    let r = spliced(&mut h);
    let l = h.root_at(r);
    let other = h.cons(Value::fixnum(9), l);
    h.push_root(other);
    for bytes in [image::dump_mappable(&h), image::dump_packed(&h)] {
        let back = image::load(&bytes).unwrap();
        assert_eq!(back.static_words(), h.static_words());
        let o = back.root_at(r + 1);
        assert!(!back.is_static(o) && back.is_static(back.cdr(o)), "each where it was");
        assert_eq!(back.string_to_rust(back.car(back.cdr(back.cdr(o)))), "text");
    }
}

/// An image made static sorts its objects into the static area's halves:
/// what no field of may come to refer to what moves (a string, a symbol, a
/// sum) into the immutable, what may (a pair, a vector, a bloblet of no
/// declared kind) into the mutable; every reference to each followed, a
/// bloblet of no suffix's (pointed at where the next object starts) too.
#[test]
fn an_image_made_static_is_sorted_into_its_halves() {
    let mut h = Heap::new();
    let text = h.make_string("text");
    let sym = h.intern("a-symbol");
    let sum = h.make_frozen(layout::kind("sum"), &[sym, text]);
    // A bloblet of fields and no suffix, then a string right after it.
    let empty = h.make_bloblet(layout::kind("bloblet"), 1, 0, true);
    let after = h.make_string("after");
    h.set_bloblet_slot(empty, 2, after);
    let v = h.make_vector(2, Value::fixnum(0));
    h.obj_set(v, 0, empty);
    h.obj_set(v, 1, sum);
    let l = h.cons(v, Value::NULL);
    h.push_root(l);
    let bytes = image::dump_static(&h);
    let back = image::load(&bytes).unwrap();
    assert!(back.immutable_words() > 0 && back.static_words() > back.immutable_words(), "both halves");
    let l = back.root_at(0);
    assert!(back.is_static(l));
    let v = back.car(l);
    let empty = back.obj_ref(v, 0);
    assert_eq!(back.string_to_rust(back.bloblet_slot(empty, 2)), "after", "the no-suffix bloblet's own field");
    let sum = back.obj_ref(v, 1);
    assert_eq!(back.symbol_name(back.bloblet_slot(sum, 2)), "a-symbol");
    assert_eq!(back.string_to_rust(back.bloblet_slot(sum, 3)), "text");
    back.verify().unwrap();
}

/// An image whose immutable half ends with a bloblet of no suffix (a
/// symbol, pointed at one past its fields: at the half's end) splices, and
/// the symbol is this heap's.
#[test]
fn a_splice_finds_an_object_at_its_halfs_end() {
    let mut h = Heap::new();
    let l = h.cons(Value::fixnum(1), Value::NULL);
    let sym = h.intern("last");
    let l = h.cons(sym, l);
    h.push_root(l);
    let bytes = image::dump_static(&h);
    let img = image::parts(&bytes, true).unwrap();
    let mut into = Heap::new();
    let roots = into.splice_image(&img, &[]).expect("splices");
    let l = roots[0];
    assert_eq!(into.symbol_name(into.car(l)), "last");
    assert_eq!(into.intern_existing("last"), Some(into.car(l)));
    into.verify().unwrap();
}

/// An image spliced into a heap at the base it was made for, whose old
/// space and static area are empty but which has a symbol of its own made
/// already, in the nursery (a front end read after the runtime's symbols,
/// `fixpt check` lowered): its immutable half goes to the mutable half,
/// since the heap's symbol, which moves, stands for the image's, so it is
/// not in place, and every field is moved, not only its fixups. (In place,
/// the fixups were written where the immutable half was made for, and the
/// words moved kept the image's references: `TODO.md` §168.)
#[test]
fn an_immutable_half_moved_aside_is_walked() {
    let bytes = {
        let mut h = Heap::new();
        let text = h.make_string("text");
        let sym = h.intern("a-symbol");
        let sum = h.make_frozen(layout::kind("sum"), &[sym, text]);
        let l = h.cons(sum, Value::NULL);
        h.push_root(l);
        image::dump_static(&h)
    };
    let mut into = Heap::new();
    if into.base_word() != Heap::image_base_word() || !into.is_generational() {
        return;
    }
    let mine = into.intern("a-symbol");
    let img = image::parts(&bytes, true).unwrap();
    assert!(!img.immutable.is_empty(), "the sum is immutable");
    let roots = into.splice_image(&img, &[]).expect("splices");
    let r = into.push_root(roots[0]);
    let m = into.push_root(mine);
    for round in 0..2 {
        let sum = into.car(into.root_at(r));
        assert_eq!(into.bloblet_slot(sum, 2), into.root_at(m), "round {round}: the image's symbol is this heap's");
        assert_eq!(into.string_to_rust(into.bloblet_slot(sum, 3)), "text", "round {round}");
        into.verify().unwrap();
        into.collect(&mut []);
    }
}
