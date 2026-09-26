//! The threaded machines against each other on the same words: the Rust
//! inner interpreter, the hand-encoded native machine, and the stencil
//! machine at each optimisation level its stencils were compiled at.
//!
//!     cargo run --release -p fixpt-native --example threaded_bench
//!
//! The Rust machine's time depends on how *this* program was built, so run
//! it both ways to see that (`--release`, and without); the native machines'
//! code does not.

use fixpt_engine::threaded::{Machine, examples};
use fixpt_heap::{Heap, Value};
use fixpt_native::stencil::{StencilMachine, opt_levels};
use fixpt_native::threaded::NativeMachine;
use std::time::Instant;

const FUEL: u64 = 1 << 40;
const RUNS: usize = 3;

/// Best of `RUNS`.
fn best(mut f: impl FnMut() -> Vec<Value>) -> (Vec<Value>, f64) {
    let mut best = f64::INFINITY;
    let mut out = Vec::new();
    for _ in 0..RUNS {
        let t = Instant::now();
        out = f();
        best = best.min(t.elapsed().as_secs_f64());
    }
    (out, best)
}

fn bench(label: &str, make: fn(&mut Heap) -> Value, args: &[i64]) {
    let mut heap = Heap::new();
    let w = make(&mut heap);
    let root = heap.push_root(w);
    let args: Vec<Value> = args.iter().map(|a| Value::fixnum(*a)).collect();

    let mut cells = 0;
    let (expect, rust_s) = best(|| {
        let mut m = Machine::with_fuel(FUEL);
        m.ds.extend_from_slice(&args);
        let w = heap.root_at(root);
        m.run(&mut heap, w).expect("runs");
        cells = m.steps;
        m.ds
    });
    let profile = if cfg!(debug_assertions) { "debug" } else { "release" };
    println!("{label}: {cells} cells");
    let row = |name: &str, s: f64| {
        println!("  {name:<22} {s:>8.4} s  {:>6.2} ns/cell  {:>6.1}x the Rust machine", 1e9 * s / cells as f64, rust_s / s);
    };
    row(&format!("Rust machine ({profile})"), rust_s);

    let mut n = NativeMachine::new();
    let (out, s) = best(|| {
        let w = heap.root_at(root);
        n.run(&mut heap, w, &args, FUEL).expect("runs")
    });
    assert_eq!(out, expect);
    row("hand-encoded", s);

    for opt in opt_levels() {
        let mut m = StencilMachine::new(opt).expect("built");
        let (out, s) = best(|| {
            let w = heap.root_at(root);
            m.run(&mut heap, w, &args, FUEL).expect("runs")
        });
        assert_eq!(out, expect);
        row(&format!("stencils -O{opt} ({} B)", m.code_bytes), s);
    }
}

fn main() {
    bench("fib 27", examples::fib, &[27]);
    bench("sum-to 10M (loop)", examples::sum_to, &[0, 10_000_000]);
    bench("sum-by-list 60k (cons)", examples::sum_by_list, &[60_000]);
}
