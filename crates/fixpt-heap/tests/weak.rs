//! Weak pairs (`Heap::make_weak_pair`, `docs/research/weak-references.md`):
//! a collection keeps no car alive for a weak pair's sake, moves on a car
//! something else keeps, and clears to `WEAK_DEAD` a car that died; the
//! cdr is held as a pair's is. In minor collections and major ones alike.

use fixpt_heap::{Heap, Value};

fn heap() -> Heap {
    let mut h = Heap::new();
    h.set_nursery(4096);
    h.verify_barrier = true;
    h
}

fn list(h: &mut Heap, n: i64) -> Value {
    (1..=n).fold(Value::NULL, |l, i| h.cons(Value::fixnum(i), l))
}

fn sum(h: &Heap, mut l: Value) -> i64 {
    let mut s = 0;
    while l != Value::NULL {
        s += h.car(l).as_fixnum();
        l = h.cdr(l);
    }
    s
}

#[test]
fn a_major_collection_clears_a_dead_car_and_moves_a_live_one() {
    let mut h = Heap::new();
    let (dead, kept) = (list(&mut h, 10), list(&mut h, 20));
    let three = list(&mut h, 3);
    let (w1, w2) = (h.make_weak_pair(dead, Value::fixnum(1)), h.make_weak_pair(kept, three));
    let mut roots = [w1, w2, kept];
    h.collect(&mut [&mut roots]);
    let [w1, w2, kept] = roots;
    assert_eq!(h.weak_car(w1), None, "nothing else held it");
    assert_eq!(h.weak_car(w2), Some(kept), "moved on with it");
    assert_eq!(sum(&h, h.weak_car(w2).unwrap()), 210);
    assert_eq!(sum(&h, h.weak_cdr(w2)), 6, "the cdr is held");
    assert_eq!(h.weak_cdr(w1), Value::fixnum(1));
    h.verify().unwrap();
}

#[test]
fn a_minor_collection_clears_a_young_dead_car() {
    let mut h = heap();
    let (dead, kept) = (list(&mut h, 10), list(&mut h, 20));
    let (w1, w2) = (h.make_weak_pair(dead, Value::NULL), h.make_weak_pair(kept, Value::NULL));
    let mut roots = [w1, w2, kept];
    let minors = h.minor_count;
    h.collect_due(&mut [&mut roots]);
    assert_eq!(h.minor_count, minors + 1);
    assert_eq!(h.weak_car(roots[0]), None);
    assert_eq!(h.weak_car(roots[1]), Some(roots[2]));
    h.verify().unwrap();
}

#[test]
fn an_old_weak_pair_holds_no_young_car_alive() {
    let mut h = heap();
    // An old weak pair, made then promoted.
    let w = h.make_weak_pair(Value::fixnum(0), Value::NULL);
    let mut roots = [w, Value::NULL];
    h.collect_due(&mut [&mut roots]);
    // Its car a young list nothing else holds, and another kept.
    let young = list(&mut h, 30);
    h.set_bloblet_slot(roots[0], 2, young);
    h.collect_due(&mut [&mut roots]);
    assert_eq!(h.weak_car(roots[0]), None, "found by its card, and not traced");
    let kept = list(&mut h, 40);
    h.set_bloblet_slot(roots[0], 2, kept);
    roots[1] = kept;
    h.collect_due(&mut [&mut roots]);
    assert_eq!(h.weak_car(roots[0]), Some(roots[1]));
    assert_eq!(sum(&h, roots[1]), 820);
    h.verify().unwrap();
    // A major collection, with the list let go.
    roots[1] = Value::NULL;
    h.collect(&mut [&mut roots]);
    assert_eq!(h.weak_car(roots[0]), None);
    h.verify().unwrap();
}

#[test]
fn an_immediate_car_is_kept() {
    let mut h = Heap::new();
    let w = h.make_weak_pair(Value::fixnum(7), Value::NULL);
    let mut roots = [w];
    h.collect(&mut [&mut roots]);
    assert_eq!(h.weak_car(roots[0]), Some(Value::fixnum(7)));
}

/// The intern table (`Heap::intern_datum`) holds its data weakly: equal data
/// are one object while one is held, and what only the table held is
/// collected and its entry dropped.
#[test]
fn interned_data_live_only_while_held() {
    let mut h = heap();
    let a = list(&mut h, 3);
    let b = list(&mut h, 3);
    let (ia, ib) = (h.intern_datum(a), h.intern_datum(b));
    assert_eq!(ia, ib, "equal data, one object");
    let held = h.interned_count();
    assert!(held >= 3, "each pair of the list: {held}");
    let mut roots = [ia];
    h.collect(&mut [&mut roots]);
    assert_eq!(h.interned_count(), held, "held, so kept");
    let again = list(&mut h, 3);
    assert_eq!(h.intern_datum(again), roots[0], "the same object after a collection");
    roots[0] = Value::NULL;
    h.collect_due(&mut [&mut roots]);
    h.collect(&mut [&mut roots]);
    assert_eq!(h.interned_count(), 0, "let go, so collected");
    h.verify().unwrap();
}
