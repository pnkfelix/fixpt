//! Redefinition at the REPL: a global's uses always refer to what it is
//! now, as in Larceny; a redefinition every use can take changes only the
//! value; one they cannot runs its users again, breaking those that no
//! longer check, or, as the driver decides, is refused (`Fx26Session::run`,
//! `Redefine`).

use fixpt_engine::Backend;
use fixpt_fx26::session::{Fx26Session, Redefine, Strategy};
use fixpt_read::FileId;

/// Each form's value, or its error, and what the REPL said about it.
fn run(s: &mut Fx26Session, text: &str) -> Vec<String> {
    let forms = s.checker.read_in(FileId(0), text).expect("reads");
    forms
        .iter()
        .map(|f| match s.run(f) {
            Ok(out) => format!("{}{}", out.printed, out.value.map(|v| v.unwrap_or_default()).unwrap_or_else(|e| format!("!! {e}"))),
            Err(e) => format!("error: {}", e.message),
        })
        .collect()
}

fn session() -> Fx26Session {
    Fx26Session::with_backend(Backend::Bytecode).expect("starts")
}

/// A redefinition of a type its users can take (a subtype of the old)
/// keeps the global: every use sees the new value, before and after.
#[test]
fn a_compatible_redefinition_is_seen_by_every_use() {
    let mut s = session();
    let out = run(&mut s, include_str!("programs/redefine/compatible.fx"));
    assert_eq!(out[2], "4");
    assert!(out[3].contains("redefined: every use sees the new one"), "{out:?}");
    assert_eq!(out[4], "202");
}

/// One they cannot take: those that still check run again; the others are
/// broken, and say so when used, until they are defined again.
#[test]
fn an_incompatible_redefinition_runs_its_users_again_or_breaks_them() {
    let mut s = session();
    let out = run(&mut s, include_str!("programs/redefine/incompatible.fx"));
    assert!(out[3].contains("run again, as they use it: `p`") && out[3].contains("broken until defined again: `m`"), "{out:?}");
    assert!(out[4].contains("`m` is broken, since `n` was redefined"), "{out:?}");
    assert_eq!(out[5], "#t");
    assert_eq!(out[7], "4", "defined again, `m` works: {out:?}");
}

/// A value kept as it was is bound: `(let ((n n)) …)` reads `n` once,
/// when the definition runs. Told to refuse, nothing changes.
#[test]
fn keeping_a_value_and_refusing() {
    let mut s = session();
    let out = run(&mut s, "(define n int 5)\n(define m int (let ((n n)) (+ n 1)))\n(define n int 50)\nm");
    assert_eq!(out[3], "6", "`m` ran once, and is not run again: {out:?}");
    let mut s = session();
    run(&mut s, "(define n int 5)\n(define m int (+ n 1))\n");
    s.next_redefine = Some(Redefine::Refuse);
    let out = run(&mut s, "(define n string \"five\")\nn\nm");
    assert!(out[0].starts_with("error: `n` not redefined: it would break `m`"), "{out:?}");
    assert_eq!(out[1..], ["5", "6"]);
}

/// The same through the pieces written in FX-26, each form compiled alone
/// against the globals' cells.
#[test]
fn the_same_compiled() {
    let mut s = session();
    s.strategy = Strategy::Cellular;
    let out = run(&mut s, include_str!("programs/redefine/compatible.fx"));
    assert_eq!(out[4], "202", "{out:?}");
    let out = run(&mut s, "(define f (subr pure (string) int) (lambda (s) (string-length s)))\n(g 1)\n(f \"abc\")");
    assert!(out[0].contains("broken until defined again: `g`"), "{out:?}");
    assert!(out[1].contains("`g` is broken"), "{out:?}");
    assert_eq!(out[2], "3");
}

/// A redefinition that reaches itself through a procedure kept as it was
/// is refused: calling it reads `f`, since calling the kept `h` does, and
/// it does not say `spin` (`Checker::no_reaching_itself`).
#[test]
fn a_knot_through_a_kept_procedure_is_refused() {
    let mut s = session();
    let out = run(&mut s, include_str!("programs/redefine/knot-kept.fx"));
    assert!(out[2].contains("calling `f` reads `f`, so `f` may reach itself through a global"), "{out:?}");
}

/// Redefining a procedure over and over at the REPL, as reloading a file
/// does, compiled to native code as `fixpt --fx26-run cellular
/// --cellular-machine registers --calling-convention native repl` runs it:
/// what the old definitions made dies. Neither the session's explicit roots
/// (handles a form made and kept) nor the live words (the compiler written
/// in FX-26 keeping every lambda made, or every global ever made for a
/// name) grow with the number of redefinitions.
#[test]
fn redefining_lets_the_old_definitions_die() {
    use fixpt_heap::{SroKind, layout::cellular::KIND};
    let mut s = session();
    s.strategy = Strategy::Cellular;
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_registers);
    s.scheme.runtime_unrooted().front_end_run_word = Some(fixpt_native::cellular::run_word_registers);
    s.front_end_compiled = true;
    s.set_native_convention(true);
    s.native_runner = Some(run_native);
    s.native_compiler = Some(fixpt_native::direct::compile_closure);
    s.register_code = true;
    s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
    s.scheme.runtime_unrooted().adapt = Some(fixpt_native::direct::adapt);
    let text = "(define f (subr pure (int) (subr pure (int) int)) (lambda (x) (lambda (y) (+ x y))))\n((f 1) 2)\n";
    let mut seen = Vec::new();
    for round in 0..24 {
        let out = run(&mut s, text);
        assert_eq!(out.last().map(|o| o.ends_with('3')), Some(true), "round {round}: {out:?}");
        let rt = s.scheme.runtime_unrooted();
        rt.heap.collect(&mut []);
        let words = rt.heap.sro(SroKind::Kind(KIND), None, &[]).len();
        seen.push((rt.heap.root_count(), words));
    }
    // After the first few rounds (the front end compiled, the standard
    // procedures used), nothing grows.
    let settled = seen[8];
    assert!(seen[8..].iter().all(|x| *x == settled), "roots and live words, round by round: {seen:?}");
}

fn run_native(rt: &mut fixpt_runtime::Runtime, closure: fixpt_heap::Value, fuel: u64) -> fixpt_fx26::session::NativeRun {
    use fixpt_fx26::session::NativeRun;
    fixpt_native::direct::with_machine(|m| match m.compile(&mut rt.heap, closure) {
        Err(why) => NativeRun::Declined(why),
        Ok(procs) => NativeRun::Ran(m.call(rt, procs[0].1, &[], fuel).map_err(|t| t.what)),
    })
    .unwrap_or_else(|e| NativeRun::Ran(Err(e)))
}
