//! Macros at the REPL (`docs/research/typed-macros.md`): each entry is a
//! text of its own, its places from 0, so a template's places are in the
//! entry that defined its macro, not the one that uses it.

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
/// what its template made is said in the definition's text.
#[test]
fn a_macro_is_used_in_a_later_entry() {
    let def = "(define-syntax foo ((bvar expr) (import expr (rho (AA var)))) ((_ (x e) body) (let ((x e)) body)))\n";
    let out = repl(&format!("{def}(foo (hey \"dude\") hey)\n(define-syntax bad (expr) ((_ e) (+ e #t)))\n(bad 3)\n"));
    assert!(out.contains("\"dude\" : string"), "{out}");
    assert!(out.contains("`bad`'s definition:1:39: argument 2 is a bool") && !out.contains("panicked"), "{out}");
}
