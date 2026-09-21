//! Time the same programs on both engines.
//!
//! Not a benchmark suite — it is a sanity check that "compiled" means
//! something, and a place to notice if a change to the compiler quietly gives
//! the speedup back. Run it with `cargo run --release --example engines`;
//! a debug build measures mostly `Vec` bounds checks.

use fixpt_engine::Backend;
use fixpt_scheme::Session;
use std::time::Instant;

const PROGRAMS: &[(&str, &str)] = &[
    (
        "fib 25",
        "(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))) (fib 25)",
    ),
    (
        "tak",
        "(define (tak x y z)
               (if (not (< y x)) z
                   (tak (tak (- x 1) y z) (tak (- y 1) z x) (tak (- z 1) x y))))
             (tak 18 12 6)",
    ),
    (
        "loop 3e6",
        "(define (loop i acc) (if (= i 0) acc (loop (- i 1) (+ acc 1)))) (loop 3000000 0)",
    ),
    (
        "list build",
        "(define (build n acc) (if (= n 0) acc (build (- n 1) (cons n acc))))
                    (length (build 300000 '()))",
    ),
    (
        "closures",
        "(define (adder n) (lambda (x) (+ x n)))
                  (define (sum i acc) (if (= i 0) acc (sum (- i 1) ((adder i) acc))))
                  (sum 400000 0)",
    ),
    (
        "counter set!",
        "(define (make) (let ((n 0)) (lambda () (set! n (+ n 1)) n)))
                      (define c (make))
                      (define (spin i) (if (= i 0) (c) (begin (c) (spin (- i 1)))))
                      (spin 400000)",
    ),
];

fn time(backend: Backend, src: &str) -> (f64, String) {
    let mut s = Session::with_backend(backend);
    s.engine.set_step_limit(None);
    let start = Instant::now();
    let out = s
        .eval_to_string("<bench>", src)
        .unwrap_or_else(|e| format!("!{e}"));
    (start.elapsed().as_secs_f64(), out)
}

fn main() {
    println!(
        "{:<14} {:>10} {:>10} {:>8}   result",
        "program", "ast", "bytecode", "speedup"
    );
    let mut total_ast = 0.0;
    let mut total_vm = 0.0;
    for (name, src) in PROGRAMS {
        let (ast, a) = time(Backend::Ast, src);
        let (vm, b) = time(Backend::Bytecode, src);
        assert_eq!(a, b, "{name}: engines disagree");
        total_ast += ast;
        total_vm += vm;
        println!("{name:<14} {ast:>9.3}s {vm:>9.3}s {:>7.2}x   {a}", ast / vm);
    }
    println!(
        "{:<14} {total_ast:>9.3}s {total_vm:>9.3}s {:>7.2}x",
        "total",
        total_ast / total_vm
    );
}
