//! The code area (`docs/object-model.md`, "A collected code area"): its
//! bloblets never move, are traced as the collector meets them, and are
//! reclaimed when nothing refers to them.

use fixpt_heap::{Heap, Value, layout};

fn raw() -> u8 {
    layout::kind("bloblet")
}

/// A code bloblet of two fields and `bytes` of suffix.
fn code(heap: &mut Heap, bytes: usize) -> Value {
    heap.make_code_bloblet(raw(), 2, bytes, false)
}

fn collect(heap: &mut Heap) {
    heap.collect(&mut []);
    heap.verify().unwrap_or_else(|e| panic!("after a collection: {e}"));
}

/// A rooted code bloblet stays where it is; what its fields refer to in the
/// heap moves, and the fields are updated to follow; one not rooted is
/// freed, and its room reused.
#[test]
fn a_code_bloblet_stays_and_its_fields_follow() {
    let mut heap = Heap::new();
    let kept = code(&mut heap, 64);
    assert!(heap.is_code_bloblet(kept));
    let pair = heap.cons(Value::fixnum(1), Value::fixnum(2));
    heap.set_bloblet_slot(kept, 1, pair);
    heap.set_bloblet_slot(kept, 2, Value::fixnum(7));
    let dropped = code(&mut heap, 64);
    heap.set_bloblet_slot(dropped, 1, pair);
    let root = heap.push_root(kept);
    let (used, span) = heap.code_words();
    assert_eq!(used, span);
    collect(&mut heap);
    assert_eq!(heap.root_at(root), kept, "a code bloblet does not move");
    let moved = heap.bloblet_slot(kept, 1);
    assert_ne!(moved, pair, "the pair moved, and the field followed it");
    assert_eq!((heap.car(moved), heap.cdr(moved)), (Value::fixnum(1), Value::fixnum(2)));
    assert_eq!(heap.bloblet_slot(kept, 2), Value::fixnum(7));
    let (after, _) = heap.code_words();
    assert!(after < used, "the one nothing refers to was freed: {after} of {used}");
    // Its room is given back (it was last, so the area's end moves down),
    // and reused: the area spans no more than it did.
    assert_eq!(heap.code_words().1, span / 2, "the freed room at the end given back");
    let again = code(&mut heap, 64);
    assert!(heap.is_code_bloblet(again));
    assert_eq!(heap.code_words().1, span, "allocated into the freed room");
    heap.pop_roots_to(root);
}

/// Liveness runs through the heap and back: a code bloblet kept only by a
/// heap object that a code bloblet keeps lives, with its fields followed.
#[test]
fn liveness_runs_through_the_heap_into_the_code_area() {
    let mut heap = Heap::new();
    let outer = code(&mut heap, 16);
    let inner = code(&mut heap, 16);
    let payload = heap.cons(Value::fixnum(42), Value::NULL);
    heap.set_bloblet_slot(inner, 1, payload);
    let middle = heap.cons(inner, Value::NULL);
    heap.set_bloblet_slot(outer, 1, middle);
    let root = heap.push_root(outer);
    for _ in 0..5 {
        collect(&mut heap);
    }
    let middle = heap.bloblet_slot(outer, 1);
    let inner2 = heap.car(middle);
    assert_eq!(inner2, inner, "the inner code bloblet did not move");
    assert_eq!(heap.car(heap.bloblet_slot(inner, 1)), Value::fixnum(42));
    heap.pop_roots_to(root);
    collect(&mut heap);
    assert_eq!(heap.code_words(), (0, 0), "all of it freed, and the area empty again");
}

/// Generating code bloblets and dropping them, over and over, takes no more
/// room than a major collection's budget (code counts toward it) and what
/// is live at a time: the area does not grow with the rounds, over three
/// major collections and more.
#[test]
fn code_dropped_over_and_over_takes_bounded_room() {
    let mut heap = Heap::new();
    let mut widest = 0;
    let mut round = 0;
    while heap.gc_count < 3 {
        let c = code(&mut heap, 8 * (1 + round % 97));
        heap.set_bloblet_slot(c, 1, Value::fixnum(round as i64));
        heap.maybe_collect(&mut []);
        widest = widest.max(heap.code_words().1);
        round += 1;
    }
    // Some fragmentation is allowed; growth with the rounds is not.
    let bound = heap.major_budget() + 200_000;
    assert!(widest < bound, "the code area spread to {widest} words over {round} rounds, past {bound}");
}

/// The same, collecting at every safepoint, as the bug-finding policy does.
#[test]
fn under_collection_at_every_safepoint() {
    let mut heap = Heap::new();
    heap.gc_every = 1;
    let keep = code(&mut heap, 32);
    let root = heap.push_root(keep);
    for round in 0..2_000i64 {
        let c = code(&mut heap, 8 * (1 + round as usize % 13));
        let p = heap.cons(Value::fixnum(round), Value::NULL);
        heap.set_bloblet_slot(c, 1, p);
        let k = heap.root_at(root);
        heap.set_bloblet_slot(k, 1, c);
        heap.maybe_collect(&mut []);
        heap.verify().unwrap_or_else(|e| panic!("round {round}: {e}"));
        let c = heap.bloblet_slot(heap.root_at(root), 1);
        assert_eq!(heap.car(heap.bloblet_slot(c, 1)), Value::fixnum(round));
    }
    heap.pop_roots_to(root);
}

/// A bloblet freed between two live ones leaves a hole, which the next
/// allocation that fits takes, through the free list.
#[test]
fn a_hole_in_the_middle_is_reused() {
    let mut heap = Heap::new();
    let a = code(&mut heap, 64);
    let _b = code(&mut heap, 64);
    let c = code(&mut heap, 64);
    let ra = heap.push_root(a);
    heap.push_root(c);
    collect(&mut heap);
    let (used, span) = heap.code_words();
    assert_eq!(used * 3, span * 2, "one of three freed, in the middle");
    let d = code(&mut heap, 64);
    assert!(heap.is_code_bloblet(d));
    assert_eq!(heap.code_words(), (span, span), "the hole taken: nothing free, the area no wider");
    let e = code(&mut heap, 8);
    assert!(heap.code_words().1 > span, "no hole left for another: {e:?} goes past the end");
    heap.pop_roots_to(ra);
}

/// A weak reference to a code bloblet: kept while the bloblet lives, which
/// never moves; dead once a collection frees it (not left pointing at the
/// room it was in, which the area gives again).
#[test]
fn a_weak_reference_to_code_dies_with_it() {
    let mut heap = Heap::new();
    let kept = code(&mut heap, 32);
    let dropped = code(&mut heap, 32);
    let (wk, wd) = (heap.weak_add(kept), heap.weak_add(dropped));
    let root = heap.push_root(kept);
    collect(&mut heap);
    assert_eq!(heap.weak_get(wk), Some(kept), "the live one, where it was");
    assert_eq!(heap.weak_get(wd), None, "the freed one, dead");
    heap.pop_roots_to(root);
    collect(&mut heap);
    assert_eq!(heap.weak_get(wk), None);
}

/// A word is made in the code area's stubbed part, below native code, its
/// suffix the stub that enters `foreign` (`docs/research/code-stubs.md`);
/// a closure of the bytecode VM holds the stub every such procedure
/// shares. A word nothing refers to is freed.
#[test]
fn words_are_made_below_native_code_with_their_stub() {
    use fixpt_heap::CodePart;
    let mut heap = Heap::new();
    let name = heap.intern("w");
    let exit = Value::fixnum(layout::cellular::routine("exit") as i64);
    let word = heap.make_cellular_word(name, &[exit]).expect("a word");
    assert_eq!(heap.code_part(word), Some(CodePart::Stubbed));
    let native = code(&mut heap, 8);
    assert_eq!(heap.code_part(native), Some(CodePart::Native));
    assert!(8 * word.index() < heap.native_code_address(), "below `code-lo`");
    assert_eq!(heap.bloblet_bytes(word), layout::stub::BYTES);
    let c = heap.make_closure(Value::NULL, &[]);
    let stub = heap.bloblet_slot(c, layout::closure::CLOSURE_STUB);
    assert_eq!(stub, heap.foreign_stub());
    assert_eq!(heap.code_part(stub), Some(CodePart::Stubbed));
    let root = heap.push_root(c);
    let (before, _) = heap.code_words_in(CodePart::Stubbed);
    collect(&mut heap);
    let (after, _) = heap.code_words_in(CodePart::Stubbed);
    assert!(after < before, "the word nothing refers to freed: {after} of {before}");
    assert_eq!(heap.bloblet_slot(heap.root_at(root), layout::closure::CLOSURE_STUB), stub, "the stub kept, by its global");
    heap.pop_roots_to(root);
}

/// An image carries the code area: a word, kept by a global, is a word of
/// the stubbed part again once loaded, its stub there, and the shared stub
/// found again.
#[test]
fn an_image_carries_the_code_area() {
    use fixpt_heap::CodePart;
    let mut heap = Heap::new();
    let name = heap.intern("w");
    let exit = Value::fixnum(layout::cellular::routine("exit") as i64);
    let word = heap.make_cellular_word(name, &[exit]).expect("a word");
    let pair = heap.cons(word, Value::fixnum(3));
    let c = heap.make_closure(pair, &[]);
    let slot = heap.symbol_global_slot(name);
    heap.set_global(slot, c);
    heap.collect(&mut []);
    let mut back = fixpt_heap::image::load(&fixpt_heap::image::dump(&heap)).expect("loads");
    let name = back.intern("w");
    let c = back.global(back.symbol_global_slot(name));
    let word = back.car(back.closure_code(c));
    assert_eq!(back.code_part(word), Some(CodePart::Stubbed));
    assert!(back.is_cellular_word(word));
    assert_eq!(back.bloblet_bytes(word), layout::stub::BYTES);
    let stub = back.bloblet_slot(c, layout::closure::CLOSURE_STUB);
    assert_eq!(back.foreign_stub(), stub, "the shared stub found again, not made anew");
}
