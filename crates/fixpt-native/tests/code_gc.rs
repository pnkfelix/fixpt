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
