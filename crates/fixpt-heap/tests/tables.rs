//! The globals and the symbol table, tables in the code area (`TODO.md`
//! §264): what a global holds, young or old, kept through every kind of
//! collection by the cards of its cell, not by a collection looking at
//! every slot; the tables longer than a chunk; and an image, which carries
//! them as lists, read back whole, beside a heap's own too.

use fixpt_heap::{Heap, Value, image};

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

/// The value of global `name`.
fn global(h: &mut Heap, name: &str) -> Value {
    let sym = h.intern(name);
    let slot = h.symbol_global_slot(sym);
    h.global(slot)
}

/// The sum of the list global `name` holds.
fn gsum(h: &mut Heap, name: &str) -> i64 {
    let l = global(h, name);
    sum(h, l)
}

fn set(h: &mut Heap, name: &str, v: Value) {
    let sym = h.intern(name);
    let slot = h.symbol_global_slot(sym);
    h.set_global(slot, v);
}

/// Enough symbols that each table spans three chunks.
const MANY: usize = 2500;

#[test]
fn a_global_keeps_what_it_holds_through_every_collection() {
    let mut h = heap();
    for i in 0..MANY {
        h.intern(&format!("g{i}"));
    }
    // Young, held only by a global past the first chunk, and by one in the
    // last: found by their cells' cards.
    let young = list(&mut h, 100);
    set(&mut h, "g1500", young);
    let other = list(&mut h, 10);
    set(&mut h, &format!("g{}", MANY - 1), other);
    let _garbage = list(&mut h, 1000);
    h.collect_young(&mut []);
    h.verify().unwrap();
    h.verify_remembered().unwrap();
    assert_eq!(gsum(&mut h, "g1500"), 5050);
    // Old now: moved by each collection of the old space, the cell found by
    // its card in the second table each time.
    for _ in 0..3 {
        let _garbage = list(&mut h, 1000);
        h.collect_old(&mut []);
        h.verify().unwrap();
        h.verify_remembered().unwrap();
        assert_eq!(gsum(&mut h, "g1500"), 5050);
        assert_eq!(gsum(&mut h, &format!("g{}", MANY - 1)), 55);
    }
    // And by a full one, which traces the tables' chunks.
    h.collect(&mut []);
    h.verify().unwrap();
    h.verify_remembered().unwrap();
    assert_eq!(gsum(&mut h, "g1500"), 5050);
    // A young value put over an old one, then collected minor.
    let young = list(&mut h, 20);
    set(&mut h, "g1500", young);
    h.collect_young(&mut []);
    assert_eq!(gsum(&mut h, "g1500"), 210);
    // Every symbol still itself, found by its name, in its place.
    for i in 0..MANY {
        let sym = h.intern(&format!("g{i}"));
        assert_eq!(h.symbol_at(i), sym, "symbol {i}");
        assert_eq!(h.symbol_name(sym), format!("g{i}"));
    }
    assert_eq!((h.symbol_count(), h.global_count()), (MANY, MANY));
    // No image, so nothing in the tables area: every chunk the heap's own.
    assert_eq!(h.tables_area_words(), (0, 0));
    h.verify().unwrap();
}

#[test]
fn a_symbol_interned_in_a_region_outlives_it() {
    let mut h = heap();
    let r = h.region_enter();
    // Its symbols, their names and the tables' chunks: none in the region.
    let syms: Vec<Value> = h.in_region(r, |h| (0..600).map(|i| h.intern(&format!("r{i}"))).collect());
    let l = list(&mut h, 5);
    set(&mut h, "r599", l);
    h.region_exit(r);
    let _garbage = list(&mut h, 1000);
    h.collect(&mut []);
    h.verify().unwrap();
    for i in 0..syms.len() {
        let again = h.intern(&format!("r{i}"));
        assert_eq!(h.symbol_name(again), format!("r{i}"));
        assert_eq!(h.symbol_at(i), again);
    }
    assert_eq!(gsum(&mut h, "r599"), 15);
}

#[test]
fn a_minor_collection_looks_at_no_global_it_need_not() {
    // As many globals as the front end's, none young: a minor collection
    // costs what it did with none.
    let time = |n: usize| {
        let mut h = heap();
        // Not the barrier's check, which walks the whole heap each time.
        h.verify_barrier = false;
        for i in 0..n {
            let s = h.intern(&format!("s{i}"));
            let slot = h.symbol_global_slot(s);
            h.set_global(slot, Value::fixnum(i as i64));
        }
        h.collect_young(&mut []);
        let started = std::time::Instant::now();
        for _ in 0..2000 {
            let _ = list(&mut h, 4);
            h.collect_young(&mut []);
        }
        started.elapsed()
    };
    let (few, many) = (time(10), time(20_000));
    assert!(many < few * 3 + std::time::Duration::from_millis(20), "{few:?} with 10 globals, {many:?} with 20,000");
}

#[test]
fn an_image_carries_the_tables() {
    for static_image in [false, true] {
        let mut h = heap();
        for i in 0..MANY {
            h.intern(&format!("g{i}"));
        }
        let l = list(&mut h, 100);
        set(&mut h, "g7", l);
        set(&mut h, "g2000", Value::fixnum(42));
        h.collect(&mut []);
        let bytes = if static_image { image::dump_static(&h) } else { image::dump_packed(&h) };
        let mut loaded = image::load(&bytes).expect("loads");
        loaded.verify().unwrap();
        assert_eq!((loaded.symbol_count(), loaded.global_count()), (MANY, MANY));
        assert_eq!(gsum(&mut loaded, "g7"), 5050);
        assert_eq!(global(&mut loaded, "g2000"), Value::fixnum(42));
        for i in [0, 255, 256, MANY - 1] {
            assert_eq!(loaded.symbol_name(loaded.symbol_at(i)), format!("g{i}"));
        }
        // Its own chunks, not the image's: an image of it is no larger. (A
        // heap read from a static image is not made one again.)
        if !static_image {
            let again = image::dump_packed(&loaded);
            assert!(again.len() <= bytes.len() + 64, "{} bytes, then {}", bytes.len(), again.len());
        }
        // The image's tables in the tables area, one chunk after another;
        // a symbol made since in a chunk of the heap's own.
        let (words, chunks) = loaded.tables_area_words();
        assert_eq!(chunks, 2 * MANY.div_ceil(256), "{words} words");
        for i in 0..300 {
            loaded.intern(&format!("new{i}"));
        }
        assert_eq!(loaded.tables_area_words(), (words, chunks));
        assert_eq!(loaded.symbol_name(loaded.symbol_at(MANY + 299)), "new299");
        // Still collected as any heap's.
        let young = list(&mut loaded, 10);
        set(&mut loaded, "g7", young);
        loaded.collect_young(&mut []);
        loaded.collect(&mut []);
        assert_eq!(gsum(&mut loaded, "g7"), 55);
        loaded.verify().unwrap();
    }
}

#[test]
fn an_image_spliced_beside_a_heaps_own_tables() {
    let mut img = heap();
    for i in 0..1500 {
        img.intern(&format!("i{i}"));
    }
    let shared = img.intern("shared");
    let slot = img.symbol_global_slot(shared);
    img.set_global(slot, Value::fixnum(7));
    let l = list(&mut img, 30);
    img.push_root(l);
    img.collect(&mut []);
    let bytes = image::dump_static(&img);
    // A heap with tables of its own, past a chunk.
    let mut h = heap();
    for i in 0..1100 {
        h.intern(&format!("h{i}"));
    }
    h.intern("shared");
    let mine = list(&mut h, 4);
    set(&mut h, "h1099", mine);
    let parts = image::parts(&bytes, true).expect("parts");
    let roots = h.splice_image(&parts, &[]).expect("spliced");
    h.verify().unwrap();
    h.verify_remembered().unwrap();
    assert_eq!(sum(&h, roots[0]), 465);
    // The image's symbols this heap's, one of them the same as one here.
    assert_eq!(h.symbol_count(), 1100 + 1 + 1500);
    for i in [0, 1499] {
        let sym = h.intern(&format!("i{i}"));
        assert_eq!(h.symbol_name(sym), format!("i{i}"));
    }
    assert_eq!(gsum(&mut h, "h1099"), 10);
    // The image's new symbols in the tables area; this heap's, not.
    assert_eq!(h.tables_area_words().1, 2 * 1500usize.div_ceil(256));
    // Collected, every kind, with what both brought.
    let mut roots = roots;
    h.collect_young(&mut [&mut roots]);
    h.collect_old(&mut [&mut roots]);
    h.collect(&mut [&mut roots]);
    h.verify().unwrap();
    assert_eq!(sum(&h, roots[0]), 465);
    assert_eq!(gsum(&mut h, "h1099"), 10);
}
