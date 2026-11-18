//! A reference into another heap is refused by the collection that meets
//! it (`Heap::copy_out_object`): that heap's object is never followed nor
//! kept alive, so the reference would dangle once that heap is dropped.

use fixpt_heap::{Heap, Value};

/// A vector of heap `b`'s, young, holding a pair of heap `a`'s, rooted.
fn crossed(a: &mut Heap, b: &mut Heap) {
    let theirs = a.cons(Value::fixnum(1), Value::NULL);
    let v = b.make_vector(1, Value::FALSE);
    // A young place: the store's barrier looks at nothing.
    b.obj_set(v, 0, theirs);
    b.push_root(v);
}

#[test]
#[should_panic(expected = "a reference to no word of this heap's")]
fn a_minor_collection_refuses_another_heaps_reference() {
    let (mut a, mut b) = (Heap::new(), Heap::new());
    crossed(&mut a, &mut b);
    b.collect_young(&mut []);
}

#[test]
#[should_panic(expected = "a reference to no word of this heap's")]
fn a_major_collection_refuses_another_heaps_reference() {
    let (mut a, mut b) = (Heap::new(), Heap::new());
    crossed(&mut a, &mut b);
    b.collect(&mut []);
}

/// What stays legitimate: a heap's own references, through both.
#[test]
fn a_heaps_own_references_are_traced() {
    let mut b = Heap::new();
    let mine = b.cons(Value::fixnum(1), Value::NULL);
    let v = b.make_vector(1, mine);
    b.push_root(v);
    b.collect_young(&mut []);
    b.collect(&mut []);
    let v = b.root_at(0);
    assert_eq!(b.car(b.obj_ref(v, 0)), Value::fixnum(1));
    b.verify().unwrap();
}
