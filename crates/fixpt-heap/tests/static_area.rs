//! The static area (`TODO.md` §161): what an image put there never moves,
//! nor is copied; its objects are roots, so what they refer to lives and
//! follows when it moves, by their dirty cards in a minor collection.

use fixpt_heap::{Heap, Value, image};

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
