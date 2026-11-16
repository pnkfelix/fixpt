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
    let def = "(define-syntax foo (macro (_ (x @ bvar e @ expr) body @ expr) expr (bind x in body)) (syntax-rules ((_ (x e) body) (let ((x e)) body))))\n";
    let out = repl(&format!("{def}(foo (hey \"dude\") hey)\n(define-syntax bad (macro (_ expr) expr) (syntax-rules ((_ e) (+ e #t))))\n(bad 3)\n"));
    assert!(out.contains("\"dude\" : string"), "{out}");
    assert!(out.contains("<fx26:3>:1:68: argument 2 is a bool") && !out.contains("panicked"), "{out}");
    assert!(out.contains("  in the expansion of `bad` at <fx26:4>:1:1"), "{out}");
}

/// A macro that makes definitions, used in later entries: each use's
/// definitions shown, its template's own made fresh for each use.
#[test]
fn a_macro_makes_definitions_in_later_entries() {
    let def = "(define-syntax define-counter (macro (_ bvar) defn) (syntax-rules ((_ name) (begin (define count (new 0)) (define name (lambda () (begin (set count (+ (get count) 1)) (get count))))))))\n";
    let out = repl(&format!("{def}(define-counter tick)\n(define-counter tock)\n(tick)\n(+ (tick) (tock))\n"));
    assert!(out.contains("tick : (subr") && out.contains("tock : (subr"), "{out}");
    // Each use's own, named by its form's key (`Macros::form_begin`).
    let counts: Vec<&str> = out.lines().filter_map(|l| l.split(" : (ref int").next().filter(|_| l.contains(" : (ref int"))?.rsplit(' ').next()).collect();
    assert!(counts.len() >= 2 && counts.iter().all(|c| c.starts_with("%count:") && c.ends_with(".1")) && counts[0] != counts[1], "{out}");
    assert!(out.contains("3 : int") && !out.contains("panicked"), "{out}");
}

/// A module file's own expansion that made a macro (`own.fx`'s
/// `(define-clamper clamp)`) leaves nothing to the entry that loads it: an
/// earlier entry's global `clamp` stays the session's, the load not refused
/// "`clamp` is defined already" (the macros an expansion made, none at each
/// form's start: `Macros::form_begin`, FX-26's `form-begun!`).
#[test]
fn a_files_own_made_macro_is_not_the_loaders() {
    let own = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/import-with-syntax/own.fx");
    let out = repl(&format!("(define clamp 7)\n(define lib (load-module \"{own}\"))\n(with lib clamped)\nclamp\n"));
    assert!(!out.contains("defined already") && out.contains("10 : int") && out.contains("7 : int ! (read (globals clamp))"), "{out}");
}
