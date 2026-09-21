//! `--dialect` selects a language, and the FX-91 one actually type-checks.
//!
//! The thing being guarded here is a trap the CLI used to have: `--dialect`
//! once set only the *reader*, so `--dialect fx91` read FX-91 tokens and then
//! handed them to the Scheme expander. It looked wired up and was not. These
//! tests assert that the checker really runs — by requiring an inferred type
//! and effect on the output, and by requiring an ill-typed program to fail.

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

fn fx91(args: &[&str], stdin: &str) -> (bool, String, String) {
    use std::io::Write as _;
    let mut child = Command::new(FIXPT)
        .args(["--dialect", "fx91"])
        .args(args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt starts");
    child.stdin.take().expect("stdin is piped").write_all(stdin.as_bytes()).expect("can write");
    let out = child.wait_with_output().expect("fixpt finishes");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

#[test]
fn the_repl_infers_types_and_effects() {
    let (ok, out, err) = fx91(&["repl"], "(+ 3 4)\n");
    assert!(ok, "the FX-91 repl failed: {err}");
    // The reference's own notation: `:` type, `!` effect, `=` value.
    assert!(out.contains(": int"), "no inferred type in:\n{out}");
    assert!(out.contains("! (maxeff)"), "no inferred effect in:\n{out}");
    assert!(out.contains("= 7"), "no value in:\n{out}");
}

#[test]
fn effects_are_inferred_not_merely_parsed() {
    // Reading, writing and allocating a reference each contribute an effect.
    // A Scheme expander handed this text could not produce these lines, which
    // is exactly what makes them worth asserting.
    let (_, out, _) =
        fx91(&["eval", "(let ((r (new 0))) (begin (set! r 5) (^ r)))"], "");
    assert!(out.contains(": int"), "{out}");
    for effect in ["write", "read", "init"] {
        assert!(out.contains(effect), "expected the {effect} effect in:\n{out}");
    }

    // A lambda is itself pure; the effect of its body is *latent* in its type.
    let (_, out, _) = fx91(&["eval", "(lambda ((r (refof int))) (^ r))"], "");
    assert!(out.contains("(-> read ((r (refof int))) int)"), "wrong latent effect:\n{out}");
    assert!(out.contains("! (maxeff)"), "the lambda itself should be pure:\n{out}");
}

#[test]
fn an_ill_typed_program_is_rejected() {
    let (ok, _, err) = fx91(&["eval", "(+ 1 #t)"], "");
    assert!(!ok, "an ill-typed program should fail");
    assert!(!err.is_empty(), "a rejection should say why");
}

#[test]
fn polymorphism_and_projection_work() {
    let (ok, out, err) =
        fx91(&["eval", "([ (plambda ((t type)) (lambda ((x t)) x)) int ] 42)"], "");
    assert!(ok, "{err}");
    assert!(out.contains(": int") && out.contains("= 42"), "{out}");
}

#[test]
fn fx87_says_it_is_not_ready_rather_than_misbehaving() {
    let out = Command::new(FIXPT)
        .args(["--dialect", "fx87", "eval", "1"])
        .output()
        .expect("fixpt runs");
    assert!(!out.status.success());
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("not implemented yet"), "unclear message: {err}");
}

#[test]
fn a_file_runs_and_its_output_reaches_stdout() {
    let dir = std::env::temp_dir().join("fixpt-fx91-run");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("can make a directory");
    let path = dir.join("demo.fx");
    std::fs::write(
        &path,
        "(with (module (define (fact (n int)) (if (= n 0) 1 (* n (fact (- n 1))))))
           (stream-write-sexp standard-output (int->sexp (fact 10))))",
    )
    .expect("can write");
    let (ok, out, err) = fx91(&["run", path.to_str().expect("utf-8")], "");
    assert!(ok, "{err}");
    assert_eq!(out.trim(), "3628800");
}
