//! Does the metadata actually make FX-87 code faster?
//!
//! The disassembly says fewer instructions. That is not the same claim, and
//! having already been wrong once about what a disassembly meant in practice,
//! this measures the thing itself: the same checked FX-87 program, erased with
//! and without the annotations, run on the same engine.
//!
//! `cargo run --release --example measure -p fixpt-fx87`

use fixpt_engine::Backend;
use fixpt_fx87::erase::{erase, erase_with, Purity};
use fixpt_fx87::{Fx87Session, Parser};
use fixpt_read::{Reader, SourceMap, SyntaxProfile};
use std::time::Instant;

struct PurityOf<'a>(&'a fixpt_fx87::check::Checker);
impl Purity for PurityOf<'_> {
    fn is_pure(&self, e: fixpt_fx87::ExpId) -> bool {
        self.0.is_pure(e)
    }
    fn effect_text(&self, e: fixpt_fx87::ExpId) -> Option<String> {
        self.0.effect_text(e)
    }
}

/// Check one FX-87 form and return `(annotated, plain)` Scheme for it.
fn erase_both(src: &str) -> (String, String) {
    let mut fx = Fx87Session::new().expect("loads");
    let mut sources = SourceMap::new();
    let file = sources.add("<b>", src);
    let mut i = std::mem::take(&mut fx.checker.p.interner);
    let forms = Reader::new(src, file, SyntaxProfile::FX87, &mut i).read_all().expect("reads");
    fx.checker.p.interner = i;

    let env = fx.checker.env.clone();
    let exp = fx.checker.p.parse_exp(&forms[0], &Default::default()).expect("parses");
    fx.checker.check(exp, &env).expect("checks");

    let standard: std::collections::HashSet<_> = env.value_names().collect();
    let purity = PurityOf(&fx.checker);
    let annotated =
        erase_with(&fx.checker.p.arena, &fx.checker.p.interner, exp, &standard, Some(&purity));
    let plain = erase(&fx.checker.p.arena, &fx.checker.p.interner, exp);
    let _ = Parser::new();
    (annotated, plain)
}

/// Best of several runs.
///
/// A single timing is not worth reporting: two runs of the same program
/// differed by 25% while this was being written, which is enough to invent or
/// erase the whole effect being measured. The minimum is the least noisy
/// summary — it is the run that was interfered with least.
const REPEATS: usize = 5;

fn run_on(backend: Backend, code: &str, label: &str) -> f64 {
    let mut best = f64::INFINITY;
    let mut answer = String::new();
    for _ in 0..REPEATS {
        let mut s = fixpt_scheme::Session::with_backend(backend);
        s.eval_str("<rt>", fixpt_fx87::session::RUNTIME).expect("runtime loads");
        s.engine.set_step_limit(None);
        let start = Instant::now();
        answer = s.eval_to_string("<b>", code).unwrap_or_else(|e| panic!("{label}: {e}"));
        best = best.min(start.elapsed().as_secs_f64());
    }
    println!("  {label:<22} {best:>8.4}s   = {answer}");
    best
}

const PROGRAMS: &[(&str, &str)] = &[
    (
        "loop 1e6",
        "(letrec ((loop (lambda ((i int) (acc int))
                          (the pure int (if (= i 0) acc (loop (- i 1) (+ acc i)))))))
           (loop 1000000 0))",
    ),
    (
        "fib 24",
        "(letrec ((fib (lambda ((n int))
                         (the pure int (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))))
           (fib 24))",
    ),
    (
        "sum of squares",
        "(letrec ((go (lambda ((i int) (acc int))
                        (the pure int (if (= i 0) acc (go (- i 1) (+ acc (* i i))))))))
           (go 400000 0))",
    ),
];

fn main() {
    let mut total_a = 0.0;
    let mut total_p = 0.0;
    let mut total_b = 0.0;
    for (name, src) in PROGRAMS {
        let (annotated, plain) = erase_both(src);
        println!("{name}:");
        // Three points, not two: the AST engine is where this started.
        let base = run_on(Backend::Ast, &plain, "ast, no metadata");
        let p = run_on(Backend::Bytecode, &plain, "bytecode, no metadata");
        let a = run_on(Backend::Bytecode, &annotated, "bytecode + metadata");
        println!(
            "  metadata alone {:>5.2}x    whole stack {:>5.2}x",
            p / a,
            base / a
        );
        total_p += p;
        total_a += a;
        total_b += base;
    }
    println!(
        "\ntotal   ast {total_b:.3}s   bytecode {total_p:.3}s   +metadata {total_a:.3}s"
    );
    println!(
        "        metadata alone {:.2}x over the compiled engine, {:.2}x over where this started",
        total_p / total_a,
        total_b / total_a
    );
}
