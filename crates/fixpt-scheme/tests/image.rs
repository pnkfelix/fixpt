//! A dumped heap can be loaded back and its procedures called.
//!
//! This is the property the whole "Core IR in the heap" arrangement exists for,
//! so it is worth testing directly rather than inferring. A closure is
//! `[code, env]`; `code` is a heap object holding a flat vector of nodes; the
//! nodes hold their constants inline. Nothing the engine executes lives in
//! Rust, so writing the heap out and reading it back is enough to carry a
//! running program across process boundaries — which is what `fixpt build` will
//! turn into a single binary.

use fixpt_engine::{Interp, Prepared};
use fixpt_heap::{Value, image};
use fixpt_runtime::{Runtime, display_value};
use fixpt_scheme::Session;

/// Find a global by name in a heap that was loaded from an image.
fn global(rt: &Runtime, name: &str) -> Value {
    let sym = rt
        .heap
        .intern_existing(name)
        .unwrap_or_else(|| panic!("{name} is interned"));
    rt.heap.global(rt.heap.symbol_global_slot(sym))
}

#[test]
fn a_dumped_heap_still_runs() {
    let mut session = Session::new();
    session
        .eval_str(
            "<setup>",
            include_str!("programs/image/setup.scm"),
        )
        .expect("setup runs");

    // Collect first, so the image holds only what is live — and so the test
    // exercises a heap that has actually been compacted.
    session.rt.heap.collect(&mut []);
    session.rt.heap.verify().expect("sound before dumping");
    let bytes = image::dump(&session.rt.heap);

    // A fresh runtime over the loaded heap. No expander, no interner, no
    // Rust-side program: only what the image carried.
    let heap = image::load(&bytes).expect("image loads");
    heap.verify().expect("sound after loading");
    let mut rt = Runtime::from_heap(heap);
    let mut interp = Interp::new();
    let mut prepared = Prepared::resumed();

    // A procedure defined before the dump, called after it.
    let twice = global(&rt, "twice");
    let r = interp
        .call(&mut rt, &mut prepared, twice, &[Value::fixnum(21)])
        .expect("twice runs");
    assert_eq!(display_value(&rt.heap, r), "42");

    // A closure that captured *another* closure: the environment chain crossed
    // the image too.
    let quadruple = global(&rt, "quadruple");
    let r = interp
        .call(&mut rt, &mut prepared, quadruple, &[Value::fixnum(5)])
        .expect("quadruple runs");
    assert_eq!(display_value(&rt.heap, r), "20");

    // Constants embedded in the code, not in a Rust-side pool.
    assert_eq!(display_value(&rt.heap, global(&rt, "greeting")), "hello");
    assert_eq!(display_value(&rt.heap, global(&rt, "numbers")), "(1 2 3)");

    // Mutable global state survives, and `set!` still works against it.
    let bump = global(&rt, "bump!");
    for expected in ["1", "2", "3"] {
        let r = interp
            .call(&mut rt, &mut prepared, bump, &[])
            .expect("bump! runs");
        assert_eq!(display_value(&rt.heap, r), expected);
    }
}

#[test]
fn a_resumed_heap_can_be_dumped_again() {
    // Round-tripping twice catches anything that survives one pass by accident
    // — a root that happens to still be reachable, say.
    let mut session = Session::new();
    session
        .eval_str(
            "<setup>",
            "(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))",
        )
        .unwrap();
    session.rt.heap.collect(&mut []);

    let first = image::dump(&session.rt.heap);
    let mut rt = Runtime::from_heap(image::load(&first).expect("loads"));
    let second = image::dump(&rt.heap);
    let mut rt2 = Runtime::from_heap(image::load(&second).expect("reloads"));

    let mut interp = Interp::new();
    let mut prepared = Prepared::resumed();
    let fact = global(&rt2, "fact");
    let r = interp
        .call(&mut rt2, &mut prepared, fact, &[Value::fixnum(10)])
        .expect("fact runs");
    assert_eq!(display_value(&rt2.heap, r), "3628800");
    let _ = &mut rt;
}

/// The same property for the compiled engine.
///
/// The bytecode is a `Bytevector` and the constants a `Vector`, both ordinary
/// heap objects, so a compiled heap travels exactly as the interpreted one
/// does. This is the half that `fixpt build` actually needs: a shipped binary
/// carries compiled code, and it has to come back as something the VM can enter
/// without recompiling — or indeed without the compiler being present at all.
#[test]
fn a_dumped_compiled_heap_still_runs() {
    let mut session = Session::compiled();
    session
        .eval_str(
            "<setup>",
            include_str!("programs/image/compiled-setup.scm"),
        )
        .expect("setup runs");

    session.rt.heap.collect(&mut []);
    session.rt.heap.verify().expect("sound before dumping");
    let bytes = image::dump(&session.rt.heap);

    let heap = image::load(&bytes).expect("image loads");
    heap.verify().expect("sound after loading");
    let mut rt = Runtime::from_heap(heap);
    let mut vm = fixpt_engine::Vm::new();
    let mut prepared = Prepared::resumed_with(fixpt_engine::Backend::Bytecode);

    // A flat closure that captured two other closures.
    let quadruple = global(&rt, "quadruple");
    let r = vm
        .call(&mut rt, &mut prepared, quadruple, &[Value::fixnum(5)])
        .expect("runs");
    assert_eq!(display_value(&rt.heap, r), "20");

    // A boxed global mutated after the round trip.
    let bump = global(&rt, "bump!");
    vm.call(&mut rt, &mut prepared, bump, &[]).expect("runs");
    let r = vm.call(&mut rt, &mut prepared, bump, &[]).expect("runs");
    assert_eq!(display_value(&rt.heap, r), "2");

    // A tail-recursive loop, which is where the frame layout would show up if
    // the image had disturbed it.
    let sum = global(&rt, "sum-to");
    let r = vm
        .call(&mut rt, &mut prepared, sum, &[Value::fixnum(100)])
        .expect("runs");
    assert_eq!(display_value(&rt.heap, r), "5050");

    // And the prelude survived: `map` is a compiled closure like any other.
    let map = global(&rt, "map");
    let list = rt
        .heap
        .list_from(&[Value::fixnum(1), Value::fixnum(2), Value::fixnum(3)]);
    let twice = global(&rt, "twice");
    let r = vm
        .call(&mut rt, &mut prepared, map, &[twice, list])
        .expect("runs");
    assert_eq!(display_value(&rt.heap, r), "(2 4 6)");
}
