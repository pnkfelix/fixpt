//! The threaded machines against each other, and against the bytecode VM,
//! on the same work: `fib`, a loop, and consing a list and summing it.
//!
//!     cargo run --release -p fixpt-native --example threaded_bench

use fixpt_engine::threaded::{Machine, examples};
use fixpt_heap::{Heap, Value};
use fixpt_native::threaded::NativeMachine;
use std::time::Instant;

const FUEL: u64 = 1 << 40;

fn time<T>(f: impl FnOnce() -> T) -> (T, f64) {
    let t = Instant::now();
    let r = f();
    (r, t.elapsed().as_secs_f64())
}

fn bench(label: &str, make: fn(&mut Heap) -> Value, args: &[i64]) {
    let mut heap = Heap::new();
    let w = make(&mut heap);
    let root = heap.push_root(w);
    let args: Vec<Value> = args.iter().map(|a| Value::fixnum(*a)).collect();

    let mut m = Machine::with_fuel(FUEL);
    m.ds.extend_from_slice(&args);
    let w = heap.root_at(root);
    let (r, rust_s) = time(|| m.run(&mut heap, w));
    r.expect("runs");
    let rust_out = m.ds.clone();

    let mut n = NativeMachine::new();
    let w = heap.root_at(root);
    let (out, native_s) = time(|| n.run(&mut heap, w, &args, FUEL));
    assert_eq!(out.expect("runs"), rust_out);
    let entries = FUEL - n.fuel_left;
    println!(
        "{label:<22} cells {:>11}  rust {:>7.3} s ({:>5.1} ns/cell)  native {:>7.3} s ({:>5.2} ns/cell)  {:>5.1}x   [{entries} entries+branches, {} collections]",
        m.steps,
        rust_s,
        1e9 * rust_s / m.steps as f64,
        native_s,
        1e9 * native_s / m.steps as f64,
        rust_s / native_s,
        heap.gc_count,
    );
}

fn main() {
    bench("fib 25", examples::fib, &[25]);
    bench("fib 27", examples::fib, &[27]);
    bench("sum-to 10M (loop)", examples::sum_to, &[0, 10_000_000]);
    bench("sum-by-list 60k (cons)", examples::sum_by_list, &[60_000]);
}
