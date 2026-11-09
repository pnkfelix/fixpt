//! Macros at the REPL (`docs/research/typed-macros.md`): every entry is
//! read into the session's one text, past those before
//! (`Fx26Session::read_entry`), so a place says which entry it is in, a
//! template's the one that defined its macro.

use std::io::Write as _;
use std::process::{Command, Stdio};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// What the REPL prints, out and error, given `input`.
fn repl(input: &str) -> String {
    let mut child = Command::new(FIXPT).arg("repl").stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().expect("starts");
    child.stdin.take().expect("piped").write_all(input.as_bytes()).expect("writes");
    let out = child.wait_with_output().expect("finishes");
    format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
}

/// A use in a later entry than its macro's definition runs (it once took
/// the entry's text by the template's place, past its end), and an error in
/// what its template made is said in the entry that defined it.
#[test]
fn a_macro_is_used_in_a_later_entry() {
    let def = "(define-syntax foo ((bvar expr) (import expr (rho (AA var)))) (syntax-rules () ((_ (x e) body) (let ((x e)) body))))\n";
    let out = repl(&format!("{def}(foo (hey \"dude\") hey)\n(define-syntax bad (expr) (syntax-rules () ((_ e) (+ e #t))))\n(bad 3)\n"));
    assert!(out.contains("\"dude\" : string"), "{out}");
    assert!(out.contains("<fx26:3>:1:56: argument 2 is a bool") && !out.contains("panicked"), "{out}");
    assert!(out.contains("  in the expansion of `bad` at <fx26:4>:1:1"), "{out}");
}

/// A macro that makes definitions, used in later entries: each use's
/// definitions shown, its template's own made fresh for each use.
#[test]
fn a_macro_makes_definitions_in_later_entries() {
    let def = "(define-syntax define-counter (-> (bvar) defn) (syntax-rules () ((_ name) (begin (define count (new 0)) (define name (lambda () (begin (set count (+ (get count) 1)) (get count))))))))\n";
    let out = repl(&format!("{def}(define-counter tick)\n(define-counter tock)\n(tick)\n(+ (tick) (tock))\n"));
    assert!(out.contains("tick : (subr") && out.contains("tock : (subr"), "{out}");
    assert!(out.contains("%count:1 : (ref int") && out.contains("%count:2 : (ref int"), "{out}");
    assert!(out.contains("3 : int") && !out.contains("panicked"), "{out}");
}
