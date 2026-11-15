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
    (h.gc_every, h.gc_major_every) = (3, 12);
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

/// Telemetry (`docs/research/telemetry.md`, stage 1): the most words in use
/// is sampled as each collection starts, so it is at least what was live
/// then; and the longest pause of each kind is counted apart.
#[test]
fn the_peak_and_the_longest_pauses_are_kept() {
    let mut h = heap();
    let mut roots = [list(&mut h, 1000)];
    let before = h.used() as u64;
    h.collect_due(&mut [&mut roots]);
    h.collect(&mut [&mut roots]);
    assert!(h.peak_words >= before, "{} < {before}", h.peak_words);
    assert!(h.minor_count + h.gc_count >= 1);
    if h.gc_count > 0 {
        assert!(h.max_major_nanos > 0 && h.max_major_nanos <= h.gc_nanos);
    }
    assert_eq!(sum(&h, roots[0]), 500500);
}

/// A young reference stored into the code area is found by its card, as
/// one in the old space is: in a field on a later card than the bloblet's
/// header, and in a bloblet allocated into a hole the collector left.
#[test]
fn young_references_in_code_bloblets_are_found_by_their_cards() {
    let mut h = heap();
    let raw = fixpt_heap::layout::kind("bloblet");
    let long = h.make_code_bloblet(raw, 100, 8, false);
    let _gap = h.make_code_bloblet(raw, 2, 64, false);
    let end = h.make_code_bloblet(raw, 2, 8, false);
    let mut root = [long, end];
    h.collect(&mut [&mut root]);
    let hole = h.make_code_bloblet(raw, 2, 8, false);
    let fields = [(long, 1), (end, 1), (hole, 2)];
    for (b, k) in fields {
        let l = list(&mut h, 10);
        h.set_bloblet_slot(b, k, l);
    }
    h.collect_young(&mut [&mut root]);
    assert_eq!(h.nursery_used(), 0);
    for (b, k) in fields {
        assert_eq!(sum(&h, h.bloblet_slot(b, k)), 55, "field {k} of {b:?}");
    }
    h.verify().unwrap();
}

/// Tenured allocation (`Heap::tenure_enter`) and collections of the
/// nursery alone (`Heap::young_only_enter`), together what the Rust front
/// end's syntax is held raw by across a procedural macro's transformer
/// (`TODO.md` §278): what is made tenured stays where it is through any
/// collection asked for then, a major one too, while the nursery's
/// garbage is reclaimed; a young value it refers to, found by its card.
#[test]
fn tenured_values_stay_put_while_collections_are_young_only() {
    let mut h = heap();
    let young = h.cons(Value::fixnum(7), Value::NULL);
    h.tenure_enter();
    let held = h.cons(young, Value::NULL);
    h.tenure_exit();
    assert!(!h.is_young_ref(held), "made in the old space");
    assert!(h.is_young_ref(young));
    let (majors, minors) = (h.majors(), h.minor_count);
    h.young_only_enter();
    let _garbage = list(&mut h, 1000);
    h.collect(&mut []);
    h.collect_old(&mut []);
    assert_eq!(h.majors(), majors, "no major collection while young-only");
    assert_eq!(h.minor_count, minors + 2, "each asked for, a minor one");
    assert_eq!(h.nursery_used(), 0, "the nursery's garbage reclaimed");
    // Held raw across them: where it was, its young part found and moved.
    let promoted = h.car(held);
    assert!(!h.is_young_ref(promoted));
    assert_eq!(h.car(promoted), Value::fixnum(7));
    // A major collection each safepoint, by the stress policy: none now.
    h.gc_major_every = 1;
    for _ in 0..3000 {
        h.cons(Value::NULL, Value::NULL);
    }
    assert!(h.collection_due(), "the nursery full");
    h.collect_due(&mut []);
    assert_eq!(h.majors(), majors, "a major one due waits");
    h.gc_major_every = 0;
    h.young_only_exit();
    h.verify().unwrap();
}

/// A heap with no nursery collects nothing while young-only: the heap
/// grows instead.
#[test]
fn a_heap_with_no_nursery_holds_collection_off_while_young_only() {
    let mut h = Heap::new();
    h.set_nursery(0);
    h.young_only_enter();
    for _ in 0..10_000 {
        h.cons(Value::NULL, Value::NULL);
    }
    let n = h.collections();
    assert!(!h.collection_due());
    h.collect(&mut []);
    assert_eq!(h.collections(), n);
    h.young_only_exit();
}
