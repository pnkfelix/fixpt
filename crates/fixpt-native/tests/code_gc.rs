//! Code that is no longer reachable is reclaimed (`docs/object-model.md`,
//! "A collected code area"): a program that generates words, compiles them
//! to machine code, runs them and drops them, over and over, must not run
//! out of room for code, however long it goes on.

use fixpt_engine::cellular::WordBuilder;
use fixpt_heap::Value;
use fixpt_native::cellular::NativeMachine;
use fixpt_runtime::Runtime;

const FUEL: u64 = 10_000_000;

/// A fresh word that pushes `n` after `pairs` pushes and drops: large
/// enough machine code that a few hundred of them fill a 32 MiB space.
fn fresh_word(rt: &mut Runtime, n: i64, pairs: usize) -> Value {
    let mut b = WordBuilder::new();
    for i in 0..pairs {
        b.lit(Value::fixnum(i as i64)).prim("drop");
    }
    b.lit(Value::fixnum(n)).ret();
    b.build(&mut rt.heap, "fresh")
}

/// Generate, compile, run and drop a word, many times over, with
/// collections between: several times what one code space holds, so that
/// it passes only if dead words' machine code is reclaimed.
#[test]
fn generated_code_that_is_dropped_is_reclaimed() {
    let mut rt = Runtime::new();
    let mut m = NativeMachine::new();
    for round in 0..3000i64 {
        let w = fresh_word(&mut rt, round, 2000);
        m.compile_reachable(&mut rt.heap, w).unwrap_or_else(|e| panic!("round {round}: {e}"));
        let out = m.run_in_runtime(&mut rt, w, &[], FUEL).unwrap_or_else(|t| panic!("round {round}: {t:?}"));
        assert_eq!(out, [Value::fixnum(round)]);
        if round % 16 == 15 {
            rt.heap.collect(&mut []);
        }
    }
}

/// Code placed from elsewhere (`install`, as the compiler written in FX-26
/// places what it assembles), then words run as they are, compiling
/// nothing: once the code is due to be collected, the first run collects
/// the heap and the code, and the runs after it neither. It was the heap
/// alone, at every run, the code staying due: a major collection per run,
/// which made the bootstrap test take six minutes (TODO §31).
#[test]
fn running_placed_code_does_not_collect_at_every_run() {
    let mut rt = Runtime::new();
    // More than the code collection's threshold (8 MB), placed.
    let mut placed = 0;
    while placed < 9 << 20 {
        let w = fresh_word(&mut rt, 0, 2000);
        let (code, _) = fixpt_native::cellular::assemble_word(&rt.heap, w, [0, 0]).expect("assembles");
        fixpt_native::cellular::with_machine(|m| {
            let (at, far) = m.reserve(code.len()).expect("room");
            let (code, starts) = fixpt_native::cellular::assemble_word(&rt.heap, w, far).expect("assembles");
            m.install(&mut rt.heap, w, at, &code, &starts).expect("installs");
        });
        placed += 4 * code.len();
    }
    assert!(fixpt_native::cellular::with_machine(|m| m.code_collection_due()));
    let w = fresh_word(&mut rt, 7, 1);
    let (code, _) = fixpt_native::cellular::assemble_word(&rt.heap, w, [0, 0]).expect("assembles");
    fixpt_native::cellular::with_machine(|m| {
        let (at, far) = m.reserve(code.len()).expect("room");
        let (code, starts) = fixpt_native::cellular::assemble_word(&rt.heap, w, far).expect("assembles");
        m.install(&mut rt.heap, w, at, &code, &starts).expect("installs");
    });
    let at = rt.heap.push_root(w);
    let before = rt.heap.gc_count;
    for _ in 0..100 {
        let w = rt.heap.root_at(at);
        assert_eq!(fixpt_native::cellular::run_word_as_is(&mut rt, w, &[]), Ok(Value::fixnum(7)));
    }
    assert!(rt.heap.gc_count - before <= 1, "{} major collections in 100 runs", rt.heap.gc_count - before);
    assert!(!fixpt_native::cellular::with_machine(|m| m.code_collection_due()));
}
