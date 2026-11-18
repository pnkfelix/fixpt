//! A reference into another heap is refused (`TODO.md` §293): where it is
//! stored, in a debug build (`Heap::may_hold`, at every store, a
//! constructor's fields, a root), and, in any build, by the collection that
//! meets it (`Heap::copy_out_object`). That heap's object is never followed
//! nor kept alive here, so the reference would dangle once that heap is
//! dropped.

use fixpt_heap::{Heap, Value};

/// A pair of another heap's.
fn theirs(a: &mut Heap) -> Value {
    a.cons(Value::fixnum(1), Value::NULL)
}

/// A vector of heap `b`'s, young, holding a pair of heap `a`'s, rooted:
/// in a build with no store's check.
#[cfg(not(debug_assertions))]
fn crossed(a: &mut Heap, b: &mut Heap) {
    let t = theirs(a);
    let v = b.make_vector(1, Value::FALSE);
    // A young place: the store's barrier looks at nothing.
    b.obj_set(v, 0, t);
    b.push_root(v);
}

#[cfg(not(debug_assertions))]
#[test]
#[should_panic(expected = "a collection traced")]
fn a_minor_collection_refuses_another_heaps_reference() {
    let (mut a, mut b) = (Heap::new(), Heap::new());
    crossed(&mut a, &mut b);
    b.collect_young(&mut []);
}

#[cfg(not(debug_assertions))]
#[test]
#[should_panic(expected = "a collection traced")]
fn a_major_collection_refuses_another_heaps_reference() {
    let (mut a, mut b) = (Heap::new(), Heap::new());
    crossed(&mut a, &mut b);
    b.collect(&mut []);
}

/// Each way a value enters a heap, in a debug build.
#[cfg(debug_assertions)]
mod stores {
    use super::*;

    fn refused(enter: fn(&mut Heap, Value)) {
        let (mut a, mut b) = (Heap::new(), Heap::new());
        let t = theirs(&mut a);
        let said = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| enter(&mut b, t))).expect_err("refused");
        let said = said.downcast_ref::<String>().cloned().unwrap_or_default();
        assert!(said.contains("stored in the heap"), "{said}");
    }

    #[test]
    fn a_store_refuses_another_heaps_reference() {
        refused(|b, t| {
            let v = b.make_vector(1, Value::FALSE);
            b.obj_set(v, 0, t);
        });
        refused(|b, t| {
            let p = b.cons(Value::NULL, Value::NULL);
            b.set_cdr(p, t);
        });
        refused(|b, t| {
            let g = b.intern("cross-heap:g");
            let slot = b.symbol_global_slot(g);
            b.set_global(slot, t);
        });
    }

    #[test]
    fn a_constructor_refuses_another_heaps_reference() {
        refused(|b, t| {
            b.cons(t, Value::NULL);
        });
        refused(|b, t| {
            b.cons(Value::NULL, t);
        });
        refused(|b, t| {
            b.make_vector(3, t);
        });
    }

    #[test]
    fn a_root_refuses_another_heaps_reference() {
        refused(|b, t| {
            b.push_root(t);
        });
        refused(|b, t| {
            b.push_root(Value::NULL);
            b.set_root_at(0, t);
        });
    }

    /// A suffix ref of another heap's whose owner is no bloblet here.
    #[test]
    fn another_heaps_suffix_ref_naming_nothing_here_is_refused() {
        let (mut a, mut b) = (Heap::new(), Heap::new());
        // Words into `a`'s old space, where `b` has nothing yet.
        for _ in 0..64 {
            let x = a.make_vector(4, Value::NULL);
            a.push_root(x);
        }
        a.collect(&mut []);
        let owner = a.make_bytevector(&[0; 16]);
        let mut keep = [owner];
        a.collect(&mut [&mut keep]);
        let s = a.suffix_ref(keep[0], 8).unwrap();
        assert!(a.may_hold(s), "its own heap's");
        let v = b.make_vector(1, Value::FALSE);
        let said = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| b.obj_set(v, 0, s))).expect_err("refused");
        assert!(said.downcast_ref::<String>().is_some_and(|m| m.contains("stored in the heap")));
    }
}

/// What stays legitimate: a heap's own references, through both.
#[test]
fn a_heaps_own_references_are_held_and_traced() {
    let mut b = Heap::new();
    let mine = b.cons(Value::fixnum(1), Value::NULL);
    let v = b.make_vector(1, mine);
    b.push_root(v);
    b.collect_young(&mut []);
    b.collect(&mut []);
    let v = b.root_at(0);
    assert_eq!(b.car(b.obj_ref(v, 0)), Value::fixnum(1));
    assert!(b.may_hold(v) && b.may_hold(Value::fixnum(3)));
    b.verify().unwrap();
}
