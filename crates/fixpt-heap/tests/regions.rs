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

/// What does not fit a chunk is a large object of the region's, in a run
/// of chunks of its own: none of it in the heap, it keeps what it points
/// to alive and does not move; smaller things fill chunk after chunk. Its
/// run, given back when the region ends, holds the next large object it
/// fits.
#[test]
fn a_large_object_is_its_regions() {
    let mut h = Heap::new();
    let r = h.region_enter();
    let used = h.used();
    let big = h.in_region(r, |h| h.make_vector(10_000, Value::fixnum(7)));
    let s = h.make_string("held");
    h.obj_set(big, 0, s);
    let used = (h.used() - used, h.used());
    assert!(used.0 < 10, "in the heap: {} words", used.0);
    assert_eq!(h.region_in_use(r), 10_002);
    let mut xs = Value::NULL;
    for i in 0..20_000 {
        xs = h.in_region(r, |h| h.cons(Value::fixnum(i), xs));
    }
    assert_eq!(h.used(), used.1, "no pair in the heap");
    assert_eq!(h.region_words(), 10_002 + 40_000);
    let mut roots = [xs];
    gc(&mut h, &mut roots);
    assert_eq!(list_sum(&h, roots[0]), (0..20_000).sum::<i64>());
    assert_eq!(h.obj_ref(big, 9_999).as_fixnum(), 7);
    assert_eq!(h.string_to_rust(h.obj_ref(big, 0)), "held", "what it points to lives");
    h.region_exit(r);
    let r = h.region_enter();
    let again = h.in_region(r, |h| h.make_vector(9_000, Value::fixnum(1)));
    assert_eq!(again.index() >> 13, big.index() >> 13, "its run reused");
    h.region_exit(r);
}

/// A reap's large object is not copied: reached, it stays where it is, its
/// references into the reap and the heap followed; not reached, its run is
/// given back, for the next.
#[test]
fn a_reaps_large_object_is_marked_not_copied() {
    let mut h = Heap::new();
    let r = h.reap_enter();
    let big = h.in_region(r, |h| h.make_vector(20_000, Value::NULL));
    let small = h.in_region(r, |h| h.cons(Value::fixnum(5), Value::NULL));
    let s = h.make_string("held");
    h.obj_set(big, 1, small);
    h.obj_set(big, 19_999, s);
    let dropped = h.in_region(r, |h| h.make_vector(30_000, Value::fixnum(0)));
    for i in 0..5_000 {
        let _ = h.in_region(r, |h| h.cons(Value::fixnum(i), Value::NULL));
    }
    let boxed = h.make_box(big);
    let mut roots = [boxed];
    gc(&mut h, &mut roots);
    let kept = h.unbox(roots[0]);
    assert_eq!(kept, big, "not moved");
    assert_eq!(h.car(h.obj_ref(big, 1)).as_fixnum(), 5, "what it points to in the reap, followed");
    assert_eq!(h.string_to_rust(h.obj_ref(big, 19_999)), "held");
    assert_eq!(h.region_in_use(r), 20_002 + 2, "the one not reached given back");
    let next = h.in_region(r, |h| h.make_vector(25_000, Value::NULL));
    assert_eq!(next.index() >> 13, dropped.index() >> 13, "its run reused");
    let mut roots = [h.make_box(big)];
    gc(&mut h, &mut roots);
    assert_eq!(h.car(h.obj_ref(h.unbox(roots[0]), 1)).as_fixnum(), 5);
    h.region_exit(r);
}

/// A region nested past the slots machine code reads is allocated in, as
/// one with a slot is: none of it in the heap.
#[test]
fn a_region_past_the_tables_slots_is_still_a_region() {
    let mut h = Heap::new();
    let handles: Vec<usize> = (0..fixpt_heap::heap::REGION_SLOTS + 10).map(|_| h.region_enter()).collect();
    let deep = *handles.last().expect("entered");
    assert!(deep >= fixpt_heap::heap::REGION_SLOTS);
    let used = h.used();
    let mut xs = Value::NULL;
    for i in 0..10_000 {
        xs = h.in_region(deep, |h| h.cons(Value::fixnum(i), xs));
    }
    assert_eq!(h.used(), used, "no pair in the heap");
    assert_eq!(h.region_in_use(deep), 20_000);
    let mut roots = [xs];
    gc(&mut h, &mut roots);
    assert_eq!(list_sum(&h, roots[0]), (0..10_000).sum::<i64>());
    h.region_exit(handles[0]);
    assert_eq!(h.live_regions(), 0);
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

/// Two tasks' regions interleaved (`regions.rs`, Q1): A enters an arena and
/// a reap, B enters its own, and A leaves its regions first. B's live on,
/// through collections, and each task counts and ends only its own.
#[test]
fn tasks_end_their_own_regions_in_any_order() {
    let mut h = Heap::new();
    let a = 0;
    let b = h.task_new();
    let (a_arena, a_reap) = (h.region_enter(), h.reap_enter());
    h.task_switch(b);
    assert_eq!(h.live_regions(), 0, "B has none yet");
    let (b_arena, b_reap) = (h.region_enter(), h.reap_enter());
    let mut b_lists = [Value::NULL, Value::NULL];
    let mut a_lists = [Value::NULL, Value::NULL];
    for i in 0..3_000 {
        h.task_switch(a);
        a_lists[0] = h.in_region(a_arena, |h| h.cons(Value::fixnum(i), a_lists[0]));
        a_lists[1] = h.in_region(a_reap, |h| h.cons(Value::fixnum(i), a_lists[1]));
        h.task_switch(b);
        b_lists[0] = h.in_region(b_arena, |h| h.cons(Value::fixnum(2 * i), b_lists[0]));
        b_lists[1] = h.in_region(b_reap, |h| h.cons(Value::fixnum(2 * i), b_lists[1]));
    }
    // A leaves first, though B entered after it.
    h.task_switch(a);
    assert_eq!(h.live_regions(), 2);
    h.region_exit(a_arena);
    assert_eq!(h.live_regions(), 0);
    assert_eq!(h.all_live_regions(), 2, "B's are live");
    // A's handle again, from A, is nothing; B's, from A, ends nothing either.
    h.region_exit(b_arena);
    assert_eq!(h.all_live_regions(), 2);
    // A new region of A's takes the lowest free slot, A's old one, and its
    // chunks; B's are not given out.
    let a_again = h.region_enter();
    assert_eq!(a_again, a_arena);
    let mut junk = Value::NULL;
    for i in 0..20_000 {
        junk = h.in_region(a_again, |h| h.cons(Value::fixnum(i), junk));
    }
    let mut roots = [b_lists[0], b_lists[1], junk];
    gc(&mut h, &mut roots);
    h.task_switch(b);
    assert_eq!(h.live_regions(), 2);
    assert_eq!(list_sum(&h, roots[0]), (0..3_000).map(|i| 2 * i).sum::<i64>());
    assert_eq!(list_sum(&h, roots[1]), (0..3_000).map(|i| 2 * i).sum::<i64>());
    assert_eq!(h.region_in_use(b_reap), 3_000 * 2, "B's reap, collected, keeps its list");
    // Ending B ends what it left, and makes A current.
    h.task_end(b);
    assert_eq!(h.task_current(), a);
    assert_eq!(h.all_live_regions(), 1);
    h.region_exit(a_again);
    assert_eq!(h.all_live_regions(), 0);
}

/// A task's place stack where it was left, after another task has entered
/// and ended regions: an abort's depth is the task's own.
#[test]
fn an_abort_ends_only_the_current_tasks_regions() {
    let mut h = Heap::new();
    let b = h.task_new();
    let _outer = h.region_enter();
    let depth = h.live_regions();
    let _inner = h.region_enter();
    h.task_switch(b);
    let theirs = h.region_enter();
    h.task_switch(0);
    h.regions_exit_to(depth);
    assert_eq!(h.live_regions(), 1);
    h.task_switch(b);
    assert_eq!(h.live_regions(), 1);
    let p = h.in_region(theirs, |h| h.cons(Value::fixnum(5), Value::NULL));
    assert_eq!(h.car(p).as_fixnum(), 5);
    h.tasks_reset();
    assert_eq!(h.task_current(), 0);
    assert_eq!(h.all_live_regions(), 1);
    h.regions_exit_to(0);
    assert_eq!(h.all_live_regions(), 0);
}

/// A message's copy (`Heap::copy_within`): pairs and bloblets copied,
/// sharing and cycles kept, raw suffixes and frozen flags as they were;
/// what the predicate says to share, shared, with what it reaches.
#[test]
fn a_message_is_copied_but_what_is_shared() {
    use fixpt_heap::layout::kind;
    let mut h = Heap::new();
    let shared = h.make_bloblet(kind("icell"), 3, 0, true);
    let s = h.make_string("hello");
    let product = h.make_frozen(kind("product"), &[Value::fixnum(7), s, shared]);
    let tail = h.cons(product, Value::NULL);
    let list = h.cons(product, tail);
    let (copy, words) = h.copy_within(list, |h, v| !v.is_pair() && h.bloblet_kind(v) == kind("icell"));
    assert_ne!(copy, list, "the list is copied");
    let (p0, p1) = (h.car(copy), h.car(h.cdr(copy)));
    assert_ne!(p0, product, "the product is copied");
    assert_eq!(p0, p1, "sharing is kept");
    assert_eq!(h.bloblet_slot(p0, 2).as_fixnum(), 7);
    let s2 = h.bloblet_slot(p0, 3);
    assert_ne!(s2, s, "the string is copied");
    assert_eq!(h.string_to_rust(s2), "hello");
    assert_eq!(h.bloblet_slot(p0, 4), shared, "the I-cell is shared");
    assert!(h.bloblet_head(p0).fields_frozen, "still frozen");
    assert!(words > 6, "{words} words copied");
}
