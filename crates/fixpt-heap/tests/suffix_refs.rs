//! Suffix refs (tag `010`, `docs/object-model.md`): pointers into a
//! bloblet's binary suffix that keep their owner alive, move with it, and
//! read the same bytes after any collection.

use fixpt_heap::{BlobletError, Heap, ObjType, Value, layout};

/// A heap with a nursery, its write barrier checked at each minor
/// collection.
fn generational() -> Heap {
    let mut h = Heap::new();
    h.set_nursery(4096);
    h.verify_barrier = true;
    h
}

/// A plain bloblet of `n` bytes, byte `i` holding `seed + i` (mod 256).
fn owner(h: &mut Heap, n: usize, seed: u8) -> Value {
    let b = h.make_bloblet(layout::kind("bloblet"), 1, n, true);
    for i in 0..n {
        let r = h.suffix_ref(b, i).expect("in range");
        h.suffix_ref_write(r, 1, (seed as u64 + i as u64) & 0xff).expect("writable");
    }
    b
}

/// The byte at `r`, which should be `seed + offset`.
fn check(h: &Heap, r: Value, seed: u8, what: &str) {
    let want = (seed as u64 + r.offset() as u64) & 0xff;
    assert_eq!(h.suffix_ref_read(r, 1).expect("in range"), want, "{what}: {r:?}");
}

/// Garbage, so that a collection has something to leave behind and the
/// nursery fills.
fn garbage(h: &mut Heap, n: usize) {
    for i in 0..n {
        h.cons(Value::fixnum(i as i64), Value::NULL);
    }
}

#[test]
fn a_suffix_ref_is_made_only_into_its_owners_suffix() {
    let mut h = Heap::new();
    let b = owner(&mut h, 16, 0);
    let r = h.suffix_ref(b, 0).unwrap();
    assert_eq!((r.offset(), h.suffix_ref_owner(r)), (0, b));
    assert_eq!(h.suffix_ref(b, 15).unwrap().offset(), 15);
    assert_eq!(h.suffix_ref(b, 16), Err(BlobletError::NoSuchByte(16)));
    let empty = h.make_bloblet(layout::kind("bloblet"), 1, 0, true);
    assert_eq!(h.suffix_ref(empty, 0), Err(BlobletError::NoSuchByte(0)));
    assert_eq!(h.suffix_ref_add(r, 15).unwrap().offset(), 15);
    assert_eq!(h.suffix_ref_add(r, 16), Err(BlobletError::NoSuchByte(16)));
    // A read that would run past the suffix is refused, wherever it starts.
    let last = h.suffix_ref(b, 12).unwrap();
    assert_eq!(h.suffix_ref_read(last, 4).unwrap(), 0x0f0e0d0c);
    assert_eq!(h.suffix_ref_read(last, 8), Err(BlobletError::NoSuchByte(19)));
    // `eq?` is a word compare: one owner and offset, one word.
    assert_eq!(h.suffix_ref(b, 3).unwrap(), h.suffix_ref(b, 3).unwrap());
}

#[test]
fn a_suffix_too_large_to_point_into_is_refused() {
    let mut h = Heap::new();
    let n = fixpt_heap::value::SUFFIX_OFFSET_LIMIT;
    let b = h.make_bloblet(layout::kind("bloblet"), 1, n, true);
    assert_eq!(h.suffix_ref(b, 0), Err(BlobletError::SuffixTooLarge(n)));
    let b = h.make_bloblet(layout::kind("bloblet"), 1, n - 1, true);
    assert_eq!(h.suffix_ref(b, n - 2).unwrap().offset(), n - 2);
}

#[test]
fn writes_through_a_ref_respect_a_frozen_suffix() {
    let mut h = Heap::new();
    let b = owner(&mut h, 8, 40);
    let r = h.suffix_ref(b, 2).unwrap();
    h.suffix_ref_write(r, 4, 0xdead_beef).unwrap();
    assert_eq!(h.suffix_ref_read(r, 4).unwrap(), 0xdead_beef);
    h.freeze_bloblet(b, false, true);
    assert_eq!(h.suffix_ref_write(r, 1, 7), Err(BlobletError::SuffixFrozen));
    assert_eq!(h.suffix_ref_read(r, 4).unwrap(), 0xdead_beef, "reads need no check");
    // Fields frozen alone do not stop a suffix write.
    let c = owner(&mut h, 8, 0);
    h.freeze_bloblet(c, true, false);
    h.suffix_ref_write(h.suffix_ref(c, 0).unwrap(), 1, 9).unwrap();
}

/// Refs in roots, in an old object's fields and in the nursery, across
/// minor and major collections: each reads its bytes after.
#[test]
fn suffix_refs_survive_minor_and_major_collections() {
    let mut h = generational();
    // An old vector, promoted, that will hold refs to young owners.
    let mut roots = [Value::NULL; 4];
    roots[0] = h.alloc(ObjType::Vector, 8, Value::NULL);
    h.collect_due(&mut [&mut roots]);
    assert_eq!(h.nursery_used(), 0, "the vector is old");
    for round in 0..6u8 {
        // Young owners: one reachable only through refs in the old vector
        // (its card marked by the barrier), one through a ref in a root,
        // one through a young pair holding a ref.
        let a = owner(&mut h, 40, round * 3);
        let b = owner(&mut h, 24, round * 3 + 1);
        let c = owner(&mut h, 9, round * 3 + 2);
        for k in 0..4 {
            let r = h.suffix_ref(a, 7 * k + round as usize).unwrap();
            h.obj_set(roots[0], k, r);
        }
        roots[1] = h.suffix_ref(b, 23).unwrap();
        let rc = h.suffix_ref(c, 0).unwrap();
        roots[2] = h.cons(rc, Value::NULL);
        roots[3] = h.suffix_ref(b, 0).unwrap();
        garbage(&mut h, 600);
        if round % 2 == 0 {
            h.collect_due(&mut [&mut roots]);
        } else {
            h.collect(&mut [&mut roots]);
        }
        h.verify().unwrap();
        h.verify_remembered().unwrap();
        for k in 0..4 {
            check(&h, h.obj_ref(roots[0], k), round * 3, "in an old vector");
        }
        check(&h, roots[1], round * 3 + 1, "in a root");
        check(&h, roots[3], round * 3 + 1, "in another root");
        check(&h, h.car(roots[2]), round * 3 + 2, "in a young pair");
        // Two refs to one owner still share it after it moved.
        assert_eq!(h.suffix_ref_owner(roots[1]), h.suffix_ref_owner(roots[3]));
        assert_eq!(h.suffix_ref_add(roots[3], 23).unwrap(), roots[1]);
    }
}

/// A ref keeps its whole owner alive: the owner's fields too.
#[test]
fn a_suffix_ref_keeps_its_owners_fields_alive() {
    let mut h = Heap::new();
    let b = h.make_bloblet(layout::kind("bloblet"), 2, 16, true);
    let s = h.make_string("kept");
    h.set_bloblet_slot(b, 2, s);
    let mut roots = [h.suffix_ref(b, 5).unwrap()];
    for _ in 0..3 {
        garbage(&mut h, 1000);
        h.collect(&mut [&mut roots]);
        h.verify().unwrap();
    }
    let o = h.suffix_ref_owner(roots[0]);
    assert_eq!(h.string_to_rust(h.bloblet_slot(o, 2)), "kept");
}

/// Owners in an arena stay where they are; owners in a reap are copied
/// into its new chunks; refs to either read the same bytes.
#[test]
fn suffix_refs_into_regions() {
    let mut h = Heap::new();
    let arena = h.region_enter();
    let reap = h.reap_enter();
    let a = h.in_region(arena, |h| owner(h, 32, 11));
    let r = h.in_region(reap, |h| owner(h, 32, 22));
    let mut roots = [h.suffix_ref(a, 31).unwrap(), h.suffix_ref(r, 17).unwrap()];
    let before = roots[0];
    garbage(&mut h, 500);
    h.collect(&mut [&mut roots]);
    h.verify().unwrap();
    assert_eq!(roots[0], before, "an arena's owner does not move");
    check(&h, roots[0], 11, "into an arena");
    check(&h, roots[1], 22, "into a reap");
    h.region_exit(reap);
    h.region_exit(arena);
}

#[test]
fn a_weak_reference_to_a_suffix_ref_follows_or_dies_with_its_owner() {
    let mut h = Heap::new();
    let kept = owner(&mut h, 8, 50);
    let dead = owner(&mut h, 8, 60);
    let wk = h.suffix_ref(kept, 3).unwrap();
    let wd = h.suffix_ref(dead, 3).unwrap();
    let (ik, id) = (h.weak_add(wk), h.weak_add(wd));
    let mut roots = [kept];
    h.collect(&mut [&mut roots]);
    let now = h.weak_get(ik).expect("its owner is alive");
    assert_eq!(h.suffix_ref_owner(now), roots[0]);
    check(&h, now, 50, "through a weak reference");
    assert_eq!(h.weak_get(id), None, "its owner died");
}

#[test]
fn suffix_refs_round_trip_through_an_image() {
    let mut h = generational();
    let old = owner(&mut h, 16, 70);
    let mut roots = [old];
    h.collect_due(&mut [&mut roots]);
    let young = owner(&mut h, 16, 80);
    let v = h.alloc(ObjType::Vector, 2, Value::NULL);
    let (ro, ry) = (h.suffix_ref(roots[0], 9).unwrap(), h.suffix_ref(young, 4).unwrap());
    h.obj_set(v, 0, ro);
    h.obj_set(v, 1, ry);
    h.push_root(v);
    h.push_root(ry);
    let (words, globals, symbols, image_roots) = h.image_parts();
    let back = Heap::from_image(&words, globals, symbols, image_roots).unwrap();
    back.verify().unwrap();
    let n = back.root_count();
    let (v, ry) = (back.root_at(n - 2), back.root_at(n - 1));
    check(&back, back.obj_ref(v, 0), 70, "an old owner's, from an image");
    check(&back, back.obj_ref(v, 1), 80, "a young owner's, from an image");
    assert_eq!(back.obj_ref(v, 1), ry, "one ref, one word");
}

#[test]
fn copying_a_graph_carries_its_suffix_refs() {
    let mut from = Heap::new();
    let b = owner(&mut from, 12, 90);
    let v = from.alloc(ObjType::Vector, 3, Value::NULL);
    from.obj_set(v, 0, from.suffix_ref(b, 0).unwrap());
    from.obj_set(v, 1, from.suffix_ref(b, 11).unwrap());
    from.obj_set(v, 2, b);
    let mut to = Heap::new();
    let c = to.copy_graph_from(&from, v);
    to.verify().unwrap();
    check(&to, to.obj_ref(c, 0), 90, "copied");
    check(&to, to.obj_ref(c, 1), 90, "copied");
    assert_eq!(to.suffix_ref_owner(to.obj_ref(c, 0)), to.obj_ref(c, 2), "the owner copied once");
}

/// A `010` word that names no byte of a live bloblet's suffix is a
/// verification error.
#[test]
fn the_verifier_refuses_a_suffix_ref_past_its_owner() {
    let mut h = Heap::new();
    let b = owner(&mut h, 8, 0);
    let good = h.suffix_ref(b, 7).unwrap();
    let v = h.alloc(ObjType::Vector, 1, good);
    let mut roots = [v];
    h.collect(&mut [&mut roots]);
    h.verify().unwrap();
    let r = h.obj_ref(roots[0], 0);
    let bad = Value::suffix_ref(r.owner(), 8).unwrap();
    h.obj_set(roots[0], 0, bad);
    let e = h.verify().unwrap_err();
    assert!(e.contains("past its owner's 8 bytes"), "{e}");
}
