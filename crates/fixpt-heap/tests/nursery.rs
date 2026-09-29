//! The nursery and minor collections (`docs/research/generational-gc.md`):
//! what is live in the nursery is promoted, old objects that point into it
//! are found by their dirty cards, and the rest is left where it is.

use fixpt_heap::{Heap, Value};

fn heap() -> Heap {
    let mut h = Heap::new();
    h.set_nursery(4096);
    h.verify_barrier = true;
    h
}

/// A list of `n` fixnums, from `n` down to 1.
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
fn a_minor_collection_promotes_what_is_live() {
    let mut h = heap();
    let mut root = [list(&mut h, 100)];
    let _garbage = list(&mut h, 1000);
    assert!(h.nursery_used() > 2000);
    let (copied, minors) = (h.words_copied, h.minor_count);
    h.collect_due(&mut [&mut root]);
    assert_eq!(h.minor_count, minors + 1, "a minor collection");
    assert_eq!(h.nursery_used(), 0);
    assert_eq!(h.words_copied - copied, 200, "only the live list");
    assert_eq!(sum(&h, root[0]), 5050);
    h.verify().unwrap();
}

#[test]
fn an_old_object_that_points_into_the_nursery_is_found_by_its_card() {
    let mut h = heap();
    // An old pair: made, then promoted.
    let mut root = [h.cons(Value::fixnum(0), Value::NULL)];
    h.collect_due(&mut [&mut root]);
    assert_eq!(h.nursery_used(), 0);
    // A young list, reachable only through the old pair.
    let young = list(&mut h, 50);
    h.set_car(root[0], young);
    h.collect_due(&mut [&mut root]);
    assert_eq!(sum(&h, h.car(root[0])), 1275);
    h.verify().unwrap();
    // A major collection, and again.
    h.collect(&mut [&mut root]);
    assert_eq!(sum(&h, h.car(root[0])), 1275);
    h.verify().unwrap();
}

#[test]
fn a_far_field_of_a_large_old_object_is_found_by_the_crossing_map() {
    let mut h = heap();
    // Old: a large vector between two small objects, each promoted.
    let mut roots = [list(&mut h, 3), Value::NULL, list(&mut h, 3)];
    roots[1] = h.alloc(fixpt_heap::ObjType::Vector, 2000, Value::fixnum(0));
    h.collect_due(&mut [&mut roots]);
    for k in [0, 7, 999, 1998, 1999] {
        let young = list(&mut h, k as i64 + 1);
        h.obj_set(roots[1], k, young);
    }
    h.collect_due(&mut [&mut roots]);
    for k in [0usize, 7, 999, 1998, 1999] {
        let n = k as i64 + 1;
        assert_eq!(sum(&h, h.obj_ref(roots[1], k)), n * (n + 1) / 2, "field {k}");
    }
    assert_eq!(sum(&h, roots[0]) + sum(&h, roots[2]), 12);
    h.verify().unwrap();
}

#[test]
fn stores_across_generations_survive_many_collections() {
    let mut h = heap();
    h.gc_every = 3;
    // A table of old pairs, each overwritten with young lists as it goes,
    // collecting at safepoints, minor and major.
    let mut roots = [Value::NULL];
    for i in 0..64 {
        roots[0] = h.cons(Value::fixnum(i), roots[0]);
    }
    for round in 0..200i64 {
        let mut p = roots[0];
        let mut k = 0;
        while p != Value::NULL {
            if (k + round) % 5 == 0 {
                let young = list(&mut h, (round % 7) + 1);
                h.set_car(p, young);
            }
            p = h.cdr(p);
            k += 1;
        }
        h.maybe_collect(&mut [&mut roots]);
    }
    h.verify().unwrap();
    assert!(h.minor_count > 10 && h.gc_count > 3, "{} minor, {} major", h.minor_count, h.gc_count);
}
