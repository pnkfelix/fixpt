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
/// is refused: its type does not say it uses `h`, but its definition does,
/// and `h` uses `f` (`Checker::no_knot_through_globals`).
#[test]
fn a_knot_through_a_kept_procedure_is_refused() {
    let mut s = session();
    let out = run(&mut s, include_str!("programs/redefine/knot-kept.fx"));
    assert!(out[2].contains("`f` cannot be redefined so: it uses `h`, which use `f` in turn"), "{out:?}");
}
