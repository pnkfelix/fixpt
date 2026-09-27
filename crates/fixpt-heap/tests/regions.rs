//! Regions (`heap/regions.rs`): what is allocated in one stays where it is,
//! keeps what it points to in the heap alive, and is given back when the
//! region ends.

use fixpt_heap::{Heap, Value};

fn gc(heap: &mut Heap, roots: &mut [Value]) {
    let slice: &mut [Value] = roots;
    heap.collect(&mut [slice]);
    heap.verify().expect("heap is structurally sound after collection");
}

fn list_sum(h: &Heap, mut v: Value) -> i64 {
    let mut n = 0;
    while v.is_pair() {
        n += h.car(v).as_fixnum();
        v = h.cdr(v);
    }
    n
}

/// A list built in a region does not move when the heap is collected, and
/// the heap strings it holds live on, though nothing else roots them.
#[test]
fn a_region_is_a_root_that_does_not_move() {
    let mut h = Heap::new();
    let r = h.region_enter();
    let mut xs = Value::NULL;
    for i in 1..=100 {
        let s = h.make_string(&format!("s{i}"));
        let pair = h.in_region(r, |h| h.cons(Value::fixnum(i), s));
        xs = h.in_region(r, |h| h.cons(pair, xs));
    }
    assert_eq!(h.region_words(), 400);
    let before = xs;
    let mut roots = [xs];
    gc(&mut h, &mut roots);
    assert_eq!(roots[0], before, "a region's objects stay where they are");
    let mut v = xs;
    let mut i = 100;
    while v.is_pair() {
        let pair = h.car(v);
        assert_eq!(h.car(pair).as_fixnum(), i);
        assert_eq!(h.string_to_rust(h.cdr(pair)), format!("s{i}"));
        v = h.cdr(v);
        i -= 1;
    }
    h.region_exit(r);
    assert_eq!(h.live_regions(), 0);
}

/// An older region allocated in while a newer one is live: what it gets
/// outlives the newer region, whose chunks are reused.
#[test]
fn an_older_region_outlives_a_newer() {
    let mut h = Heap::new();
    let old = h.region_enter();
    let mut xs = Value::NULL;
    for round in 0..50 {
        let new = h.region_enter();
        let mut junk = Value::NULL;
        for i in 0..100 {
            junk = h.in_region(new, |h| h.cons(Value::fixnum(i), junk));
        }
        xs = h.in_region(old, |h| h.cons(Value::fixnum(round), xs));
        h.region_exit(new);
    }
    let mut roots = [xs];
    gc(&mut h, &mut roots);
    assert_eq!(list_sum(&h, xs), (0..50).sum::<i64>());
    h.region_exit(old);
}

/// Ending a region ends any newer one left live, as an escape leaves them;
/// and a region no longer live gives heap allocation.
#[test]
fn ending_a_region_ends_the_newer() {
    let mut h = Heap::new();
    let a = h.region_enter();
    let _b = h.region_enter();
    let _c = h.region_enter();
    assert_eq!(h.live_regions(), 3);
    h.region_exit(a);
    assert_eq!(h.live_regions(), 0);
    let used = h.used();
    let p = h.in_region(a, |h| h.cons(Value::fixnum(1), Value::NULL));
    assert_eq!(h.used(), used + 2, "in the heap");
    assert_eq!(h.car(p).as_fixnum(), 1);
}

/// What does not fit a chunk goes to the heap; smaller things fill chunk
/// after chunk.
#[test]
fn large_objects_go_to_the_heap() {
    let mut h = Heap::new();
    let r = h.region_enter();
    let used = h.used();
    let big = h.in_region(r, |h| h.make_vector(10_000, Value::fixnum(7)));
    assert!(h.used() > used + 10_000);
    let used = h.used();
    let mut xs = Value::NULL;
    for i in 0..20_000 {
        xs = h.in_region(r, |h| h.cons(Value::fixnum(i), xs));
    }
    assert_eq!(h.used(), used, "no pair in the heap");
    assert_eq!(h.region_words(), 40_000);
    let mut roots = [big, xs];
    gc(&mut h, &mut roots);
    assert_eq!(list_sum(&h, roots[1]), (0..20_000).sum::<i64>());
    assert_eq!(h.obj_ref(roots[0], 9_999).as_fixnum(), 7);
    h.region_exit(r);
}

/// A reap is collected with the heap: what is reachable in it is copied
/// within it, and what is not is dropped; references into it from the heap
/// and from roots follow, and what it points to in the heap lives.
#[test]
fn a_reap_is_collected() {
    let mut h = Heap::new();
    let r = h.reap_enter();
    let mut keep = Value::NULL;
    for i in 0..10_000 {
        let junk = h.in_region(r, |h| h.cons(Value::fixnum(i), Value::NULL));
        let _ = junk;
        if i % 100 == 0 {
            let s = h.make_string(&format!("s{i}"));
            let cell = h.in_region(r, |h| h.cons(Value::fixnum(i), s));
            keep = h.in_region(r, |h| h.cons(cell, keep));
        }
    }
    // A heap object pointing into the reap.
    let boxed = h.make_box(keep);
    let before = h.region_words();
    assert_eq!(h.region_in_use(r), 10_000 * 2 + 100 * 4);
    let mut roots = [boxed];
    gc(&mut h, &mut roots);
    assert_eq!(h.region_words(), before, "allocation, as counted, is not undone by copying");
    assert_eq!(h.region_in_use(r), 100 * 4, "only what is reachable is kept");
    let keep = h.unbox(roots[0]);
    let mut v = keep;
    let mut n = 0;
    while v.is_pair() {
        let cell = h.car(v);
        let i = h.car(cell).as_fixnum();
        assert_eq!(h.string_to_rust(h.cdr(cell)), format!("s{i}"));
        v = h.cdr(v);
        n += 1;
    }
    assert_eq!(n, 100);
    h.region_exit(r);
}

/// A reference into a reap that has ended, left somewhere the collector
/// looks, is not followed, though a new reap is made and collected.
#[test]
fn a_reference_an_ended_reap_left_is_not_followed() {
    let mut h = Heap::new();
    let r = h.reap_enter();
    let stale = h.in_region(r, |h| h.cons(Value::fixnum(1), Value::NULL));
    h.region_exit(r);
    let r2 = h.reap_enter();
    let mut xs = Value::NULL;
    for i in 0..5_000 {
        xs = h.in_region(r2, |h| h.cons(Value::fixnum(i), xs));
    }
    let mut roots = [stale, xs];
    gc(&mut h, &mut roots);
    assert_eq!(roots[0], stale, "left as it was");
    assert_eq!(list_sum(&h, roots[1]), (0..5_000).sum::<i64>());
    h.region_exit(r2);

    // Its chunk is not reused while the reference is there; once a
    // collection finds none, it is.
    let chunk = |v: Value| v.index() >> 13;
    let mut roots = [stale];
    gc(&mut h, &mut roots);
    let r3 = h.reap_enter();
    let mut seen = Vec::new();
    for _ in 0..20_000 {
        seen.push(chunk(h.in_region(r3, |h| h.cons(Value::NULL, Value::NULL))));
    }
    assert!(!seen.contains(&chunk(stale)), "a chunk a reference is into is not reused");
    h.region_exit(r3);
    gc(&mut h, &mut []);
    let r4 = h.reap_enter();
    let mut seen = Vec::new();
    for _ in 0..40_000 {
        seen.push(chunk(h.in_region(r4, |h| h.cons(Value::NULL, Value::NULL))));
    }
    assert!(seen.contains(&chunk(stale)), "once none is found, it is");
    h.region_exit(r4);
}
