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
    let input = "(define* f (subr spin (int) int) (lambda (n) (if (< n 2) n (+ (f (- n 1)) (f (- n 2))))))\n(f 10)\n,disassemble f\n";
    child.stdin.take().expect("piped").write_all(input.as_bytes()).expect("writes");
    let out = child.wait_with_output().expect("finishes");
    let out = String::from_utf8_lossy(&out.stdout);
    assert!(out.contains("55 : int"), "{out}");
    for line in ["0branch", "global f", "call 1", "return"] {
        assert!(out.contains(line), "no `{line}` in:\n{out}");
    }
}

/// `,disassemble` of a polymorphic value projects it first, any description
/// standing in for each binder (`proj` compiles to nothing), a place made
/// for one by `letrena`: no `proj` to write to see `cons`'s code.
#[test]
fn the_fx26_repl_disassembles_a_polymorphic_value_projected() {
    use std::io::Write as _;
    let mut child = Command::new(FIXPT)
        .args(["--dialect", "fx26", "--fx26-run", "cellular", "repl"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt starts");
    let app = "(define app (poly ((p place) (r region p) (e effect) (f (=> (type) type))) \
               (subr e ((subr e ((f int)) int) (f int)) int)) \
               (plambda ((p place) (r region p) (e effect) (f (=> (type) type))) (lambda (g x) (g x))))";
    let input = format!(",disassemble cons\n{app}\n,disassemble app\n");
    child.stdin.take().expect("piped").write_all(input.as_bytes()).expect("writes");
    let out = child.wait_with_output().expect("finishes");
    let (out, err) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    for line in [
        "; as (proj (proj cons @heap) unit unit)",
        "word cons",
        "; as (proj app %p1 %p1 pure (dlambda ((a1 type)) unit))",
        "word app",
    ] {
        assert!(out.contains(line), "no `{line}` in:\n{out}\n{err}");
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
        // Defined in the native convention, `id` is native code already.
        "a native closure over 0 value(s)",
        "2 instructions",
        "mov x0, x1",
        "\n7\n",
        "832040",
        // Expressions, run as machine code: a call, closures made and passed,
        // and a closure as the value.
        "75025 : int",
        "42 : int",
        "#<native-closure",
        // A lambda applied at once is a `let`: `(+ 41 1)`, folded.
        "movz x0, #0x150",
        // State kept from form to form: each is compiled alone, against
        // the globals the ones before made.
        "1041 : int",
        // `,disassemble` shows what a native procedure was compiled from,
        // `,disassemble-asm` its machine code.
        "compiled from the register code below",
        "cells of register code):",
        "a native closure over 0 value(s):",
    ] {
        assert!(out.contains(want), "no `{want}` in:\n{out}");
    }
    assert!(!out.contains("not in the native convention yet"), "{out}");
    // A cellular procedure is called from native code, and a native one
    // given where a cellular one is expected is converted: an adapter.
    assert!(out.contains("2001 : int"), "{out}");
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

/// `fixpt ARGS` with `stdin`, no dialect given: whether it succeeded, and
/// its standard output.
fn fixpt(args: &[&str], stdin: &str) -> (bool, String) {
    use std::io::Write as _;
    let mut child = Command::new(FIXPT)
        .args(args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt starts");
    child.stdin.take().expect("stdin is piped").write_all(stdin.as_bytes()).expect("can write");
    let out = child.wait_with_output().expect("fixpt finishes");
    (out.status.success(), String::from_utf8_lossy(&out.stdout).into_owned())
}

#[test]
fn fx26_checks_compiles_and_evaluates_a_file_or_text() {
    let file = concat!(env!("CARGO_MANIFEST_DIR"), "/../fixpt-fx26/tests/programs/run/acyclic-in-a-place.fx");
    // Both checkers, and both compilers; `check` and `compile` imply FX-26.
    let (ok, out) = fixpt(&["check", file], "");
    assert!(ok && out.contains("int ! (read (globals len))") && out.ends_with("; both checkers agree\n"), "{out}");
    let (ok, out) = fixpt(&["--check", "(+ 1 #t)"], "");
    assert!(!ok && out.contains("! <argument>:1:6:"), "{out}");
    let (ok, out) = fixpt(&["compile", "-"], "(define f (subr pure (int) int) (lambda (x) (+ x 1))) (f 2)");
    assert!(ok && out.contains("its register code") && out.ends_with("; both compilers made this\n"), "{out}");
    // A `.fx` file is FX-26, and a whole program.
    let (ok, out) = fixpt(&["eval", file], "");
    assert!(ok && out.contains("3 : int"), "{out}");
    let (ok, out) = fixpt(&["--dialect", "fx26", "--fx26-run", "cellular", "--eval", "(+ 1 2)"], "");
    assert!(ok && out.contains("3 : "), "{out}");
}

/// `car` of `nil`, whose type (a list) allows it, traps on every machine
/// instead of reading below address 0: machine code used to load from the
/// pair without a look at it, and crashed.
#[test]
fn car_of_nil_traps_on_every_machine() {
    for (m, text) in on_every_machine("(define xs (listof int @heap) nil)\n(car xs)\n") {
        assert!(text.contains("pair-car") || text.contains("car or cdr of nil") || text.contains("expected a pair"), "{m:?}: {text}");
    }
}

/// A standard operation as a value, of any runtime primitive's
/// (`char-downcase`), on every machine; `parse-nat` of a bad radix fails
/// there, instead of panicking (`programs/standard-values.fx`).
#[test]
fn standard_values_and_parse_nat_on_every_machine() {
    for (m, text) in on_every_machine(include_str!("programs/standard-values.fx")) {
        assert!(text.contains("\"hello\" : string"), "{m:?}: {text}");
        assert!(text.contains("254 : int"), "{m:?}: {text}");
        assert!(text.contains("a radix is from 2 to 36"), "{m:?}: {text}");
    }
}

/// Past a fixnum, an `int` is a bignum alike on every machine, the lowered
/// program too (`programs/overflow.fx`).
#[test]
fn ints_are_bignums_on_every_machine() {
    for (m, text) in on_every_machine(include_str!("programs/overflow.fx")) {
        assert!(text.contains("1180591620717411303424 : int"), "{m:?}: {text}");
    }
}

/// The fixed-width integers wrap alike on every machine
/// (`programs/fixed-width.fx`).
#[test]
fn fixed_width_integers_on_every_machine() {
    for (m, text) in on_every_machine(include_str!("programs/fixed-width.fx")) {
        let values: Vec<&str> = text.lines().filter(|l| !l.starts_with("fnv") && !l.starts_with(';')).map(|l| l.split(" : ").next().unwrap_or("")).collect();
        assert_eq!(values, ["1335831723", "-2147483648", "1", "(-4 1073741820 -1)"], "{m:?}: {text}");
    }
}

/// Unions' shape predicates and `typecase` alike on every machine, no
/// shape taken for another (`programs/unions.fx`).
#[test]
fn union_shapes_on_every_machine() {
    for (m, text) in on_every_machine(include_str!("programs/unions.fx")) {
        let values: Vec<&str> = text.lines().filter(|l| l.starts_with('(')).map(|l| l.split(" : ").next().unwrap_or("")).collect();
        assert_eq!(values, ["(1 2 1 2 3 9 500 -1 7)", "(2 50 -1 7)", "(0 0 0 1 0 1 1 0)", "(0 42)"], "{m:?}: {text}");
    }
}

/// The bits of `int`s alike on every machine, bignums too
/// (`programs/bitwise.fx`).
#[test]
fn bitwise_on_every_machine() {
    for (m, text) in on_every_machine(include_str!("programs/bitwise.fx")) {
        assert!(
            text.contains("(8 14 6 -6 48 -5 1180591620717411303424 1180591620717411303424 255 -18446744073709551617) : "),
            "{m:?}: {text}"
        );
    }
}

/// `program` run by `fixpt eval` on every machine, all at once (each
/// loads the front end): each machine's options and what it printed, none
/// killed by a signal.
fn on_every_machine(program: &str) -> Vec<(&'static [&'static str], String)> {
    let machines: [&'static [&'static str]; 6] = [
        &[],
        &["--fx26-run", "cellular"],
        &["--fx26-run", "cellular", "--cellular-machine", "native"],
        &["--fx26-run", "cellular", "--cellular-machine", "native-compiled"],
        &["--fx26-run", "cellular", "--cellular-machine", "registers"],
        &["--fx26-run", "cellular", "--calling-convention", "native"],
    ];
    let children: Vec<_> = machines
        .iter()
        .map(|m| {
            let mut child = Command::new(FIXPT)
                .args(["--dialect", "fx26"])
                .args(*m)
                .args(["eval", "-"])
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .expect("fixpt starts");
            use std::io::Write as _;
            child.stdin.take().expect("piped").write_all(program.as_bytes()).expect("writes");
            (*m, child)
        })
        .collect();
    children
        .into_iter()
        .map(|(m, child)| {
            let out = child.wait_with_output().expect("finishes");
            let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
            assert!(out.status.code().is_some(), "{m:?}: killed by a signal: {text}");
            (m, text)
        })
        .collect()
}

/// `--emacs` (`editors/emacs/fx26-mode.el`): no continuation prompt, and
/// `,at FILE LINE COL` makes the next form's errors name where it was
/// sent from; the form after it is the REPL's own again.
#[test]
fn the_fx26_repl_for_emacs_places_errors_where_forms_were_sent_from() {
    use std::io::Write as _;
    let mut child = Command::new(FIXPT)
        .args(["--dialect", "fx26", "--emacs", "repl"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt starts");
    let input = include_str!("programs/emacs-at.repl");
    child.stdin.take().expect("piped").write_all(input.as_bytes()).expect("writes");
    let out = child.wait_with_output().expect("finishes");
    let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    assert!(!stdout.contains("     | "), "a continuation prompt:\n{stdout}");
    assert!(stdout.contains("fx26> 3 : "), "{stdout}");
    assert!(stderr.contains("/some dir/f.fx:41:8: argument 1 is a int"), "{stderr}");
    assert!(stderr.contains("<fx26:3>:1:6: argument 1 is a int"), "{stderr}");
}

/// At the REPL, a redefinition at another type leaves the definitions that
/// use the name out of date, as they were, until `,rerun-outdated` (TODO
/// §29): `g` keeps the old `f`, and so `h` works; run again while `f`
/// takes a string, `g` does not check and stays as it was; once `f` takes
/// an int again, it runs again, and `h` sees it. In the native convention,
/// so that both checkers defer.
#[test]
fn the_fx26_repl_reruns_outdated_definitions_when_asked() {
    use std::io::Write as _;
    let mut child = Command::new(FIXPT)
        .args(["--dialect", "fx26", "--fx26-run", "cellular", "--cellular-machine", "registers", "--calling-convention", "native", "repl"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt starts");
    let input = include_str!("programs/rerun-outdated.repl");
    child.stdin.take().expect("piped").write_all(input.as_bytes()).expect("writes");
    let out = child.wait_with_output().expect("finishes");
    let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    let said = |s: &str| assert!(stdout.contains(s), "not said: {s}\n{stdout}\n{stderr}");
    said("; out of date (1), using what was defined again: `g`; `,rerun-outdated` runs them again");
    said("fx26> 3 : int");
    said("; `g` uses `f`, defined again since at another type");
    said("; `g` stays out of date: argument 1 is a int, where a string is expected");
    said("; `g` redefined: every use sees the new one");
    said("fx26> 200 : int");
    said("fx26> ; nothing is out of date");
    assert!(!stdout.contains("run again, as they use it"), "{stdout}");
}

/// A word too long for a conditional branch to reach its end (PLAN.md B1):
/// `ocaml/boyer`'s largest register word is over 441,000 instructions,
/// and its branches to the trap stubs placed at its end panicked, "does
/// not fit 19 signed bits". Such a word is assembled again with long
/// branches; native code too long is refused and runs as cellular code.
#[test]
fn a_word_too_long_for_its_branches_runs() {
    let boyer = concat!(env!("CARGO_MANIFEST_DIR"), "/../../mllang-bench/fx/ocaml/boyer.fx");
    for convention in ["cellular", "native"] {
        let out = Command::new(FIXPT)
            .args(["--dialect", "fx26", "--step-limit", "none", "--fx26-run", "cellular", "--cellular-machine", "registers", "--calling-convention", convention, "eval", boyer])
            .output()
            .expect("fixpt runs");
        let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        assert!(stdout.lines().last().is_some_and(|l| l.starts_with("30 : int")), "{convention}:\n{stdout}\n{stderr}");
    }
}

/// `fixpt front-end-files`: the front end's files in the order it joins
/// them, each with its lines and path, then the bootstrap's driver.
#[test]
fn front_end_files_lists_what_the_front_end_is_made_of() {
    let out = Command::new(FIXPT).arg("front-end-files").output().expect("fixpt runs");
    let text = String::from_utf8_lossy(&out.stdout);
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), fixpt_fx26::FRONT_END_FILES.len() + 1, "{text}");
    assert!(lines[0].ends_with("/eager-reader.fx"), "{text}");
    assert!(lines.last().is_some_and(|l| l.contains("/bootstrap.fx")), "{text}");
    for l in &lines {
        let path = l.split_whitespace().nth(1).expect("a path");
        assert!(std::path::Path::new(path).is_file(), "{path} is not a file");
    }
}
