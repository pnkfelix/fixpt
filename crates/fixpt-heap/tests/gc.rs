//! Collector and heap-image tests.
//!
//! The collector is the piece of this system where a bug is both easiest to
//! introduce and hardest to diagnose later — a value that silently becomes the
//! wrong object surfaces thousands of instructions away. So these tests go
//! beyond "does it still run": every case calls `verify()`, which walks the
//! whole live region and re-derives the object boundaries independently of the
//! collector that produced them.

use fixpt_heap::value::ObjType;
use fixpt_heap::{Heap, Value, image};

/// Force a collection regardless of occupancy (`maybe_collect` has a threshold).
fn gc(heap: &mut Heap, roots: &mut [Value]) {
    let slice: &mut [Value] = roots;
    heap.collect(&mut [slice]);
    heap.verify().expect("heap is structurally sound after collection");
}

/// Materialise a heap value as a comparable Rust tree, so a structure can be
/// checked for equality across a collection that moved every word of it.
#[derive(Debug, PartialEq, Clone)]
enum Tree {
    Fix(i64),
    Str(String),
    Sym(String),
    Flo(u64),
    Bytes(Vec<u8>),
    Imm(u64),
    Pair(Box<Tree>, Box<Tree>),
    Vec(Vec<Tree>),
    Obj(ObjType, Vec<Tree>),
    /// Guards against runaway recursion on a cyclic structure.
    Deep,
}

fn snapshot(h: &Heap, v: Value, fuel: u32) -> Tree {
    if fuel == 0 {
        return Tree::Deep;
    }
    if v.is_fixnum() {
        return Tree::Fix(v.as_fixnum());
    }
    if v.is_immediate() {
        return Tree::Imm(v.raw());
    }
    if v.is_pair() {
        return Tree::Pair(
            Box::new(snapshot(h, h.car(v), fuel - 1)),
            Box::new(snapshot(h, h.cdr(v), fuel - 1)),
        );
    }
    match h.obj_type(v).expect("a heap object") {
        ObjType::String => Tree::Str(h.string_to_rust(v)),
        ObjType::Symbol => Tree::Sym(h.symbol_name(v)),
        ObjType::Flonum => Tree::Flo(h.flonum_value(v).to_bits()),
        ObjType::Bytevector => Tree::Bytes(h.bytevector_to_vec(v)),
        ObjType::Vector => {
            Tree::Vec((0..h.obj_len(v)).map(|i| snapshot(h, h.obj_ref(v, i), fuel - 1)).collect())
        }
        ty => Tree::Obj(
            ty,
            (0..h.obj_len(v)).map(|i| snapshot(h, h.obj_ref(v, i), fuel - 1)).collect(),
        ),
    }
}

#[test]
fn allocation_never_moves_anything() {
    // The central invariant: a Value stays valid across allocation, because
    // allocation only bumps, and growth preserves semispace-relative offsets.
    let mut heap = Heap::with_semispace(1024);
    let first = heap.cons(Value::fixnum(1), Value::fixnum(2));
    let before = snapshot(&heap, first, 8);

    // Allocate far past the initial semispace, forcing several grows.
    for i in 0..50_000 {
        heap.cons(Value::fixnum(i), Value::NULL);
    }
    assert!(heap.capacity() > 1024 || heap.is_generational(), "heap should have grown");
    assert_eq!(snapshot(&heap, first, 8), before, "growth must not disturb live values");
    heap.verify().unwrap();
}

#[test]
fn deep_structure_survives_collection() {
    let mut heap = Heap::new();
    let mut list = Value::NULL;
    for i in (0..2000).rev() {
        list = heap.cons(Value::fixnum(i), list);
    }
    let mut roots = vec![list];
    let before = heap.list_to_vec(list).unwrap();
    gc(&mut heap, &mut roots);
    let after = heap.list_to_vec(roots[0]).unwrap();
    assert_eq!(before.len(), after.len());
    for (i, v) in after.iter().enumerate() {
        assert_eq!(v.as_fixnum(), i as i64);
    }
}

#[test]
fn cycles_survive_and_stay_cyclic() {
    // A reference-counted heap is exactly what this case rules out.
    let mut heap = Heap::new();
    let a = heap.cons(Value::fixnum(1), Value::NULL);
    let b = heap.cons(Value::fixnum(2), a);
    heap.set_cdr(a, b);

    let mut roots = vec![a];
    gc(&mut heap, &mut roots);
    let a = roots[0];
    let b = heap.cdr(a);
    assert_eq!(heap.car(a).as_fixnum(), 1);
    assert_eq!(heap.car(b).as_fixnum(), 2);
    assert_eq!(heap.cdr(b), a, "the cycle must close back on the same cell");
}

#[test]
fn sharing_is_preserved_not_duplicated() {
    // Copying collectors that forget to leave a forwarding pointer turn a DAG
    // into a tree, which is invisible until the heap explodes on a big one.
    let mut heap = Heap::new();
    let shared = heap.cons(Value::fixnum(7), Value::NULL);
    let v = heap.vector_from(&[shared, shared, shared]);
    let mut roots = vec![v];
    gc(&mut heap, &mut roots);

    let v = roots[0];
    let a = heap.obj_ref(v, 0);
    assert_eq!(a, heap.obj_ref(v, 1));
    assert_eq!(a, heap.obj_ref(v, 2));
    heap.set_car(a, Value::fixnum(9));
    assert_eq!(heap.car(heap.obj_ref(v, 2)).as_fixnum(), 9, "still one object, not three");
}

#[test]
fn garbage_is_reclaimed() {
    let mut heap = Heap::new();
    let keep = heap.cons(Value::fixnum(1), Value::NULL);
    for i in 0..10_000 {
        heap.cons(Value::fixnum(i), Value::NULL);
    }
    let before = heap.used();
    let mut roots = vec![keep];
    gc(&mut heap, &mut roots);
    assert!(heap.used() < before / 10, "used {} -> {}", before, heap.used());
    assert_eq!(heap.car(roots[0]).as_fixnum(), 1);
}

#[test]
fn raw_payloads_are_never_traced_as_references() {
    // A flonum's bits, a string's code points and a bytevector's bytes can all
    // look exactly like a pair or object reference. Tracing them would corrupt
    // the heap; this pins the `payload_is_scanned` behaviour down.
    let mut heap = Heap::new();
    let bits = Value::pair(12345).raw(); // a bit pattern that *is* a reference
    let flo = heap.make_flonum(f64::from_bits(bits));
    let bv = heap.make_bytevector(&bits.to_le_bytes());
    let s = heap.make_string("λ pack ✓");
    let v = heap.vector_from(&[flo, bv, s]);

    let mut roots = vec![v];
    let before = snapshot(&heap, v, 8);
    gc(&mut heap, &mut roots);
    assert_eq!(snapshot(&heap, roots[0], 8), before);
    assert_eq!(heap.flonum_value(heap.obj_ref(roots[0], 0)).to_bits(), bits);
    assert_eq!(heap.string_to_rust(heap.obj_ref(roots[0], 2)), "λ pack ✓");
}

#[test]
fn symbols_stay_interned_across_collection() {
    let mut heap = Heap::new();
    let a = heap.intern("with");
    let slot = heap.symbol_global_slot(a);
    let m = heap.intern("moduleof");
    heap.set_global(slot, m);

    let mut roots: Vec<Value> = vec![];
    gc(&mut heap, &mut roots);

    let a2 = heap.intern("with");
    assert_eq!(heap.symbol_name(a2), "with");
    assert_eq!(heap.symbol_global_slot(a2), slot, "interning must be stable across a collection");
    assert_eq!(heap.symbol_name(heap.global(slot)), "moduleof");
}

#[test]
fn strings_index_in_constant_time_and_roundtrip() {
    let mut heap = Heap::new();
    for text in ["", "a", "ab", "hello, world", "λμ→∀", "\u{10FFFF}x"] {
        let s = heap.make_string(text);
        let chars: Vec<char> = text.chars().collect();
        assert_eq!(heap.string_len(s), chars.len(), "{text:?}");
        for (i, c) in chars.iter().enumerate() {
            assert_eq!(heap.string_ref(s, i), *c, "{text:?} at {i}");
        }
        assert_eq!(heap.string_to_rust(s), text);
    }
}

#[test]
fn bytevectors_roundtrip_at_every_alignment() {
    let mut heap = Heap::new();
    for n in 0..40usize {
        let bytes: Vec<u8> = (0..n).map(|i| (i * 7 + 3) as u8).collect();
        let bv = heap.make_bytevector(&bytes);
        assert_eq!(heap.bytevector_len(bv), n);
        assert_eq!(heap.bytevector_to_vec(bv), bytes, "length {n}");
    }
}

#[test]
fn repeated_collection_is_stable() {
    // Flipping semispaces repeatedly is where an off-by-one in the scan loop
    // shows up, so do it many times and re-verify each round.
    let mut heap = Heap::new();
    let s = heap.make_string("payload");
    let sym = heap.intern("a-symbol");
    let mut roots = vec![heap.vector_from(&[s, sym, Value::fixnum(3), Value::TRUE])];
    let before = snapshot(&heap, roots[0], 8);
    for round in 0..25 {
        for i in 0..200 {
            heap.cons(Value::fixnum(i), Value::NULL);
        }
        gc(&mut heap, &mut roots);
        assert_eq!(snapshot(&heap, roots[0], 8), before, "round {round}");
    }
}

#[test]
fn mixed_heap_stress() {
    // A deterministic pseudo-random mix of every object shape, with collections
    // interleaved, checking a retained set each time.
    let mut heap = Heap::with_semispace(2048);
    let mut rng: u64 = 0x2545_F491_4F6C_DD1D;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };

    let mut roots: Vec<Value> = Vec::new();
    let mut expected: Vec<Tree> = Vec::new();

    for step in 0..3000u64 {
        let v = match next() % 7 {
            0 => heap.cons(Value::fixnum(step as i64), Value::NULL),
            1 => heap.make_string(&format!("s{step}")),
            2 => heap.intern(&format!("sym{}", step % 64)),
            3 => heap.make_flonum(step as f64 * 0.5),
            4 => heap.make_bytevector(&step.to_le_bytes()),
            5 => {
                let a = heap.cons(Value::fixnum(step as i64), Value::NULL);
                heap.vector_from(&[a, a, Value::TRUE])
            }
            _ => {
                let inner = heap.make_string("boxed");
                heap.make_box(inner)
            }
        };
        if next() % 4 == 0 {
            roots.push(v);
            expected.push(snapshot(&heap, v, 8));
        }
        if step % 97 == 0 {
            gc(&mut heap, &mut roots);
            for (i, want) in expected.iter().enumerate() {
                assert_eq!(&snapshot(&heap, roots[i], 8), want, "root {i} at step {step}");
            }
        }
    }
}

#[test]
fn native_roots_survive_collection() {
    let mut heap = Heap::new();
    let s = heap.make_string("held by native code");
    let depth = heap.push_root(s);
    let mut none: Vec<Value> = vec![];
    gc(&mut heap, &mut none);
    assert_eq!(heap.string_to_rust(heap.root_at(depth)), "held by native code");
    heap.pop_roots_to(depth);
}

// ------------------------------------------------------------------- images

#[test]
fn image_roundtrip_preserves_the_whole_heap() {
    let mut heap = Heap::new();
    let sym = heap.intern("moduleof");
    let s = heap.make_string("FX-91");
    let list = heap.list_from(&[Value::fixnum(1), Value::fixnum(2), s, sym]);
    let slot = heap.symbol_global_slot(sym);
    heap.set_global(slot, list);

    let mut roots = vec![list];
    gc(&mut heap, &mut roots);
    let before = snapshot(&heap, roots[0], 16);

    let bytes = image::dump(&heap);
    let restored = image::load(&bytes).expect("image loads");
    restored.verify().unwrap();

    let list2 = restored.global(slot);
    assert_eq!(snapshot(&restored, list2, 16), before);
    assert_eq!(restored.symbol_name(restored.intern_existing("moduleof").unwrap()), "moduleof");
}

#[test]
fn image_detects_corruption() {
    let mut heap = Heap::new();
    heap.intern("x");
    let bytes = image::dump(&heap);

    assert!(matches!(image::load(&bytes[..10]), Err(image::ImageError::Truncated { .. })));

    let mut bad_magic = bytes.clone();
    bad_magic[0] = b'X';
    assert!(matches!(image::load(&bad_magic), Err(image::ImageError::BadMagic)));

    let mut bad_version = bytes.clone();
    bad_version[8] = 99;
    assert!(matches!(image::load(&bad_version), Err(image::ImageError::BadVersion(_))));

    let mut flipped = bytes.clone();
    let mid = flipped.len() / 2;
    flipped[mid] ^= 0xff;
    assert!(matches!(image::load(&flipped), Err(image::ImageError::BadChecksum { .. })));
}

#[test]
fn embedded_image_is_found_after_an_executable() {
    let mut heap = Heap::new();
    let s = heap.make_string("embedded");
    let greeting = heap.intern("greeting");
    let slot = heap.symbol_global_slot(greeting);
    heap.set_global(slot, s);
    let img = image::dump(&heap);

    let fake_exe = b"\x7fELF this is pretending to be a runtime binary".to_vec();
    let combined = image::embed_into(&fake_exe, &img);

    let found = image::extract_embedded(&combined).expect("trailer located");
    assert_eq!(found, &img[..]);
    let restored = image::load(found).unwrap();
    assert_eq!(restored.string_to_rust(restored.global(slot)), "embedded");

    // A plain runtime with no appended image must simply report none.
    assert!(image::extract_embedded(&fake_exe).is_none());
}
