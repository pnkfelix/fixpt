//! I-cells (docs/research/recursion-and-initialization.md): written once,
//! read after. The misuses, a read of an empty cell and a second write, are
//! errors in every way FX-26 runs: lowered to Scheme, by the evaluator
//! written in FX-26, and compiled to threaded code by the compiler written
//! in FX-26. `tests/programs/run/icells.fx` is the use that works.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

fn every_way(program: &str) -> Vec<(&'static str, String)> {
    let session = || Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let lowered = match session().run_program(program).expect("checks") {
        Ok(v) => v,
        Err(e) => format!("!! {e}"),
    };
    let evaluated = session().eval_with_own_evaluator(program).expect("checks");
    let compiled = session().compile_with_own_compiler(program).expect("checks");
    vec![("lowered", lowered), ("evaluated", evaluated), ("compiled", compiled)]
}

fn fails_everywhere(program: &str, message: &str) {
    for (how, out) in every_way(program) {
        assert!(out.starts_with("!! ") && out.contains(message), "{how}: {out}");
    }
}

#[test]
fn a_cell_is_read_after_its_write() {
    let program = "(define c (icell int @g) (make-icell)) (icell-put! c 42) (icell-get c)";
    for (how, out) in every_way(program) {
        assert_eq!(out, "42", "{how}");
    }
}

#[test]
fn reading_an_empty_cell_is_an_error() {
    fails_everywhere("(define c (icell int @g) (make-icell)) (icell-get c)", "an i-cell read before it was written");
}

#[test]
fn a_second_write_is_an_error() {
    fails_everywhere(
        "(define c (icell int @g) (make-icell)) (icell-put! c 1) (icell-put! c 2)",
        "an i-cell written twice",
    );
}

/// A procedure called through a cell before the cell is filled: the knot
/// used too early, which a `letrec` would report as a call before the
/// definition.
#[test]
fn calling_through_an_empty_cell_is_an_error() {
    fails_everywhere(
        "(define f (icell (subr pure (int) int) @g) (make-icell)) ((icell-get f) 1)",
        "an i-cell read before it was written",
    );
}
