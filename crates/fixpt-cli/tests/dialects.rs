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

fn fx87(args: &[&str], stdin: &str) -> (bool, String, String) {
    use std::io::Write as _;
    let mut child = Command::new(FIXPT)
        .args(["--dialect", "fx87"])
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

/// FX-87 reports in its own reference's layout — value first, then
/// ` : type ! effect` — which is not FX-91's, and the difference is kept.
#[test]
fn fx87_checks_types_and_effects() {
    let (ok, out, err) = fx87(&["eval", "(+ 1 2)"], "");
    assert!(ok, "{err}");
    assert_eq!(out.trim(), "3 : int ! pure");

    // A latent effect: the lambda is pure, the `read` is in its type.
    let (_, out, _) = fx87(&["eval", "(lambda ((r (ref int @!))) (get r))"], "");
    assert!(out.contains("(subr (read @!) ((ref int @!)) int) ! pure"), "{out}");

    // And masking: a private mutable cell costs nothing observable.
    let (_, out, _) = fx87(&["eval", "(let ((x 3 @!)) (set! x 4))"], "");
    assert!(out.contains("unit ! pure"), "{out}");
}

/// The rule that licenses compiling FX more aggressively than Scheme.
#[test]
fn fx87_rejects_assigning_a_standard_binding() {
    let (ok, _, err) = fx87(&["eval", "(set! + -)"], "");
    assert!(!ok, "assigning a standard binding should fail");
    assert!(err.contains("mutable variable"), "{err}");
}

/// `,code` shows the erased Scheme *with* the metadata the checker proved —
/// which is the point of carrying it as inert data: it is inspectable.
#[test]
fn fx87_shows_the_metadata_it_emits() {
    let (ok, out, err) = fx87(&["repl"], ",code\n(+ 1 2)\n");
    assert!(ok, "{err}");
    assert!(out.contains("%fx-note"), "no metadata in the erased code:\n{out}");
    assert!(out.contains("integrable"), "{out}");
    assert!(out.contains("basis checked"), "the basis should be recorded:\n{out}");
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

#[test]
fn fx26_runs_cellular_on_each_machine() {
    // The same answer from each machine the compiled words can run on; the
    // stencils only where this build found a nightly compiler.
    let src = "(letrec ((f (subr spin (int) int) (lambda (n) (if (< n 2) n (+ (f (- n 1)) (f (- n 2))))))) (f 15))";
    let stencils = !fixpt_native::stencil::opt_levels().is_empty();
    for machine in ["rust", "native", "stencils"].into_iter().filter(|m| stencils || *m != "stencils") {
        let out = Command::new(FIXPT)
            .args(["--dialect", "fx26", "--fx26-run", "cellular", "--cellular-machine", machine, "eval", src])
            .output()
            .expect("fixpt runs");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(stdout.contains("610 : int"), "{machine}: {stdout}{}", String::from_utf8_lossy(&out.stderr));
    }
    let out = Command::new(FIXPT).args(["--cellular-machine", "forth", "eval", "1"]).output().expect("fixpt runs");
    assert!(!out.status.success(), "an unknown machine is refused");
}

#[test]
fn the_fx26_repl_shows_cellular_code() {
    use std::io::Write as _;
    let mut child = Command::new(FIXPT)
        .args(["--dialect", "fx26", "--fx26-run", "cellular", "repl"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt starts");
    let input = "(define f (subr spin (int) int) (lambda (n) (if (< n 2) n (+ (f (- n 1)) (f (- n 2))))))\n(f 10)\n,disassemble f\n";
    child.stdin.take().expect("piped").write_all(input.as_bytes()).expect("writes");
    let out = child.wait_with_output().expect("finishes");
    let out = String::from_utf8_lossy(&out.stdout);
    assert!(out.contains("55 : int"), "{out}");
    for line in ["0branch", "global f", "call 1", "return"] {
        assert!(out.contains(line), "no `{line}` in:\n{out}");
    }
}

/// `--calling-convention native`: procedure types are native unless they
/// say otherwise, and `,native` shows a procedure's code in that convention
/// and calls it; what it cannot compile yet it says.
#[test]
fn the_fx26_repl_compiles_in_the_native_convention() {
    use std::io::Write as _;
    let mut child = Command::new(FIXPT)
        .args(["--dialect", "fx26", "--fx26-run", "cellular", "--calling-convention", "native", "repl"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt starts");
    let input = include_str!("programs/native-convention.fx");
    child.stdin.take().expect("piped").write_all(input.as_bytes()).expect("writes");
    let done = child.wait_with_output().expect("finishes");
    let out = String::from_utf8_lossy(&done.stdout);
    for want in [
        "; id (lambda@",
        "2 instructions",
        "mov x0, x1",
        "\n7\n",
        "832040",
        // Expressions, run as machine code: a call, closures made and passed,
        // and a closure as the value.
        "75025 : int",
        "42 : int",
        "#<native-closure",
        "adds x0, x1, #8",
    ] {
        assert!(out.contains(want), "no `{want}` in:\n{out}");
    }
    assert!(!out.contains("not in the native convention yet"), "{out}");
    // A cellular procedure cannot be called from native code: an error.
    let err = String::from_utf8_lossy(&done.stderr);
    assert!(err.contains("a `cellular` procedure cannot be called from `native` code yet"), "{err}");
    let out = Command::new(FIXPT).args(["--calling-convention", "fast", "eval", "1"]).output().expect("fixpt runs");
    assert!(!out.status.success(), "an unknown convention is refused");
}

/// `--step-limit`: a count stops a long run, `none` lets it finish, and
/// anything else is refused; `,step-limit` shows and sets it in the REPL.
#[test]
fn the_step_limit_can_be_set_or_lifted() {
    let long = "(letrec ((f (subr spin (int) int) (lambda (n) (if (< n 1) 0 (f (- n 1)))))) (f 30000000))";
    let run = |args: &[&str]| {
        let out = Command::new(FIXPT).args(args).output().expect("runs");
        (out.status.code(), String::from_utf8_lossy(&out.stdout).to_string(), String::from_utf8_lossy(&out.stderr).to_string())
    };
    let (code, _, err) = run(&["eval", "--dialect", "fx26", "--step-limit", "1000", long]);
    assert!(code != Some(0) && err.contains("step limit"), "{err}");
    let (code, out, err) = run(&["eval", "--dialect", "fx26", "--step-limit", "none", long]);
    assert!(code == Some(0) && out.starts_with('0'), "{out}{err}");
    let (code, _, err) = run(&["eval", "--step-limit", "lots", "1"]);
    assert!(code == Some(2) && err.contains("--step-limit"), "{err}");
    let (_, out, _) = fx91(&["repl", "--dialect", "fx26"], ",step-limit\n,step-limit none\n,step-limit\n");
    assert!(out.contains("step limit: 20000000") && out.contains("step limit: none"), "{out}");
}
