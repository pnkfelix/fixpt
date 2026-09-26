//! Bloblets (`docs/object-model.md`): a header, tagged fields, and an untraced
//! suffix, with every pointer at the start of the suffix. These are the cases
//! the collector has to get right because of that — the backward scan, the
//! trailer, and bloblets with no fields or no suffix — and the construction
//! protocol that is safe wherever a collection falls.

use fixpt_heap::{BlobletError, Heap, Value, image};

const KIND: u8 = 32;

/// Collect with `vals` as the roots, and check the heap is sound afterwards.
fn collect(h: &mut Heap, vals: &mut [Value]) {
    h.collect(&mut [vals]);
    h.verify().unwrap_or_else(|e| panic!("unsound after a collection: {e}"));
}

/// Put some other objects in front, so a collection really moves things.
fn clutter(h: &mut Heap) {
    for i in 0..50 {
        h.cons(Value::fixnum(i), Value::NULL);
    }
}

#[test]
fn fields_are_named_from_the_suffix() {
    let mut h = Heap::new();
    let b = h.make_bloblet(KIND, 3, 5, true);
    let head = h.bloblet_head(b);
    assert_eq!((head.kind, head.fields, head.bytes), (KIND, 4, 5), "three fields and the trailer");
    assert!(h.bloblet_has_trailer(b));
    // Field 1 is the trailer, which only the runtime writes.
    assert_eq!(h.bloblet_field(b, 1), Err(BlobletError::Trailer));
    assert_eq!(h.set_bloblet_field(b, 1, Value::TRUE), Err(BlobletError::Trailer));
    for k in 2..=4 {
        assert_eq!(h.bloblet_field(b, k), Ok(Value::fixnum(0)), "fields start as the fixnum 0");
        h.set_bloblet_field(b, k, Value::fixnum(k as i64 * 10)).expect("sets");
    }
    assert_eq!(h.bloblet_field(b, 5), Err(BlobletError::NoSuchField(5)));
    h.set_bloblet_bytes(b, 0, b"hello").expect("writes");
    assert_eq!(h.bloblet_bytes(b), b"hello");
    assert_eq!(h.bloblet_byte(b, 5), Err(BlobletError::NoSuchByte(5)));
    h.verify().expect("sound");
}

#[test]
fn a_bloblet_survives_being_moved() {
    let mut h = Heap::new();
    clutter(&mut h);
    let inner = h.make_bloblet(KIND, 1, 0, false);
    h.set_bloblet_field(inner, 1, Value::fixnum(7)).unwrap();
    let pair = h.cons(Value::fixnum(1), Value::fixnum(2));
    let outer = h.make_bloblet(KIND, 2, 16, true);
    h.set_bloblet_field(outer, 2, inner).unwrap();
    h.set_bloblet_field(outer, 3, pair).unwrap();
    h.set_bloblet_bytes(outer, 0, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]).unwrap();
    let mut roots = [outer];
    collect(&mut h, &mut roots);
    let outer = roots[0];
    assert_ne!(outer.index(), 0);
    let inner = h.bloblet_field(outer, 2).unwrap();
    assert!(inner.is_bloblet());
    assert_eq!(h.bloblet_field(inner, 1), Ok(Value::fixnum(7)));
    let pair = h.bloblet_field(outer, 3).unwrap();
    assert_eq!(h.car(pair), Value::fixnum(1));
    assert_eq!(h.bloblet_bytes(outer), (1..=16).collect::<Vec<u8>>());
}

/// With no trailer, the collector finds the header by the backward scan, and
/// every pointer to the bloblet must end up at the same new place — the
/// second forward it leaves is what the later ones find.
#[test]
fn many_pointers_to_a_bloblet_without_a_trailer() {
    let mut h = Heap::new();
    clutter(&mut h);
    let b = h.make_bloblet(KIND, 40, 3, false);
    for k in 1..=40 {
        h.set_bloblet_field(b, k, Value::fixnum(k as i64)).unwrap();
    }
    let t = h.make_bloblet(KIND, 40, 3, true);
    let mut roots = [b, t, b, t, b];
    collect(&mut h, &mut roots);
    assert!(roots.iter().step_by(2).all(|v| *v == roots[0]), "{roots:?}");
    assert!(roots[1] == roots[3]);
    for k in 1..=40 {
        assert_eq!(h.bloblet_field(roots[0], k), Ok(Value::fixnum(k as i64)));
    }
    // And once more, from where they are now.
    collect(&mut h, &mut roots);
    assert_eq!(h.bloblet_field(roots[4], 40), Ok(Value::fixnum(40)));
}

/// No fields: the pointer is one word past the header. No suffix: the
/// pointer is one word past the last field, which may be the next object's
/// header.
#[test]
fn bloblets_with_no_fields_or_no_suffix() {
    let mut h = Heap::new();
    let bytes_only = h.make_bloblet(KIND, 0, 12, false);
    h.set_bloblet_bytes(bytes_only, 0, b"twelve bytes").unwrap();
    let fields_only = h.make_bloblet(KIND, 2, 0, false);
    let next = h.make_bloblet(KIND, 1, 0, false);
    h.set_bloblet_field(fields_only, 1, next).unwrap();
    h.set_bloblet_field(next, 1, Value::fixnum(99)).unwrap();
    h.verify().expect("sound before");
    let mut roots = [fields_only, bytes_only];
    collect(&mut h, &mut roots);
    assert_eq!(h.bloblet_bytes(roots[1]), b"twelve bytes");
    let next = h.bloblet_field(roots[0], 1).unwrap();
    assert_eq!(h.bloblet_field(next, 1), Ok(Value::fixnum(99)));
}

/// More fields than the main header can count: an extension word before it.
#[test]
fn a_large_bloblet_and_a_large_vector() {
    let mut h = Heap::new();
    let n = 300_000;
    let b = h.make_bloblet(KIND, n, 8, true);
    h.set_bloblet_field(b, 2, Value::fixnum(2)).unwrap();
    h.set_bloblet_field(b, n + 1, Value::fixnum(-1)).unwrap();
    let v = h.make_vector(n, Value::fixnum(5));
    h.obj_set(v, n - 1, Value::TRUE);
    let mut roots = [b, v];
    collect(&mut h, &mut roots);
    let (b, v) = (roots[0], roots[1]);
    assert_eq!(h.bloblet_head(b).fields, n + 1);
    assert_eq!(h.bloblet_field(b, 2), Ok(Value::fixnum(2)));
    assert_eq!(h.bloblet_field(b, n + 1), Ok(Value::fixnum(-1)));
    assert_eq!(h.obj_len(v), n);
    assert_eq!(h.obj_ref(v, 0), Value::fixnum(5));
    assert_eq!(h.obj_ref(v, n - 1), Value::TRUE);
}

/// The construction protocol, with collections at its every stage. The
/// reserved words start out as garbage that looks like pointers, which is
/// harmless while they are suffix.
#[test]
fn the_construction_protocol_survives_collections_anywhere() {
    let mut h = Heap::new();
    clutter(&mut h);
    let r = h.bloblet_reserve(KIND, 3, 4, true);
    // Garbage that would be catastrophic if traced, in all four would-be
    // fields, the trailer's included.
    let junk = Value::pair(123_456).raw().to_le_bytes();
    for f in 0..4 {
        h.set_bloblet_bytes(r, f * 8, &junk).unwrap();
    }
    let mut roots = [r];
    collect(&mut h, &mut roots);
    h.bloblet_zero_reserved(roots[0], 0, 2);
    collect(&mut h, &mut roots);
    h.bloblet_zero_reserved(roots[0], 2, 4);
    collect(&mut h, &mut roots);
    let b = h.bloblet_publish(roots[0], 3, true);
    assert_eq!(b.index(), roots[0].index() + 4, "the pointer moves forward past the fields and the trailer");
    let head = h.bloblet_head(b);
    assert_eq!((head.fields, head.bytes), (4, 4));
    for k in 2..=4 {
        assert_eq!(h.bloblet_field(b, k), Ok(Value::fixnum(0)));
    }
    let s = h.make_string("filled");
    h.set_bloblet_field(b, 4, s).unwrap();
    let mut roots = [b];
    collect(&mut h, &mut roots);
    let s = h.bloblet_field(roots[0], 4).unwrap();
    assert_eq!(h.string_to_rust(s), "filled");
}

#[test]
fn extending_keeps_every_field_where_it_was() {
    let mut h = Heap::new();
    let b = h.make_bloblet(KIND, 2, 3, true);
    h.set_bloblet_field(b, 2, Value::fixnum(20)).unwrap();
    h.set_bloblet_field(b, 3, Value::fixnum(30)).unwrap();
    h.set_bloblet_bytes(b, 0, b"abc").unwrap();
    let e = h.bloblet_extend(b, &[Value::fixnum(50), Value::fixnum(40)]);
    assert_eq!(h.bloblet_head(e).fields, 5);
    assert!(h.bloblet_has_trailer(e));
    assert_eq!(h.bloblet_field(e, 2), Ok(Value::fixnum(20)));
    assert_eq!(h.bloblet_field(e, 3), Ok(Value::fixnum(30)));
    assert_eq!(h.bloblet_field(e, 4), Ok(Value::fixnum(40)));
    assert_eq!(h.bloblet_field(e, 5), Ok(Value::fixnum(50)));
    assert_eq!(h.bloblet_bytes(e), b"abc");
    assert_eq!(h.bloblet_head(b).fields, 3, "the original is untouched");
    h.verify().expect("sound");
}

#[test]
fn fields_and_suffix_freeze_independently() {
    let mut h = Heap::new();
    let b = h.make_bloblet(KIND, 1, 1, false);
    h.freeze_bloblet(b, false, true);
    assert_eq!(h.set_bloblet_byte(b, 0, 1), Err(BlobletError::SuffixFrozen));
    h.set_bloblet_field(b, 1, Value::TRUE).expect("fields still writable");
    h.freeze_bloblet(b, true, false);
    assert_eq!(h.set_bloblet_field(b, 1, Value::FALSE), Err(BlobletError::FieldsFrozen));
    let mut roots = [b];
    collect(&mut h, &mut roots);
    assert!(h.bloblet_head(roots[0]).fields_frozen && h.bloblet_head(roots[0]).suffix_frozen);
}

#[test]
fn verification_notices_a_pointer_into_the_middle() {
    let mut h = Heap::new();
    let b = h.make_bloblet(KIND, 2, 0, false);
    let v = h.make_vector(1, Value::fixnum(0));
    h.obj_set(v, 0, Value::bloblet(b.index() - 1));
    let err = h.verify().expect_err("a pointer to a field is not a bloblet pointer");
    assert!(err.contains("not at the start of its suffix"), "{err}");
}

#[test]
fn bloblets_travel_in_heap_images() {
    let mut h = Heap::new();
    let b = h.make_bloblet(KIND, 1, 4, true);
    h.set_bloblet_bytes(b, 0, b"code").unwrap();
    let sym = h.intern("the-bloblet");
    let slot = h.symbol_global_slot(sym);
    h.set_global(slot, b);
    h.collect(&mut []);
    let bytes = image::dump(&h);
    let loaded = image::load(&bytes).expect("loads");
    loaded.verify().expect("sound");
    let b = loaded.global(loaded.symbol_global_slot(loaded.intern_existing("the-bloblet").unwrap()));
    assert_eq!(loaded.bloblet_bytes(b), b"code");
    assert!(loaded.bloblet_has_trailer(b));
}
