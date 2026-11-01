//! `stage` (`docs/research/eval.md`), as `fixpt run` performs it: code a
//! program gives as a datum, checked against a module's type, an effect
//! and a type as the program runs, and made a procedure, or refused with a
//! value saying why and where (`programs/stage/`), on every machine: those
//! that compile with the compilers written in FX-26, the lowering's
//! (`rs-scheme-vm`, the code checked and lowered by the Rust front end, and
//! given Scheme's `eval`), and the evaluator's (`fx-ast-eval`, the code
//! checked by the checker written in Rust and run by the evaluator).
use std::process::{Command, Stdio};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// The machines: the lowering's, the evaluator's, cellular words,
/// interpreted and compiled, register code, and native code where it runs.
const STAGING: &[&str] = &[
    "rs-scheme-vm",
    "fx-ast-eval",
    "fx-cells-rsinterp",
    "fx-cells-asminterp",
    "fx-cells-rsjit-cellcc",
    "fx-cells-fxjit-cellcc",
    "fx-regs-rsjit-cellcc",
    "fx-regs-fxjit-cellcc",
    "fx-cells-rsinterp-nativecc",
    "fx-regs-rsjit-nativecc",
    "fx-regs-fxjit-nativecc",
];

/// `program` run on `machine`: its status, standard output and error.
fn run(machine: &'static str, program: &str) -> (Option<i32>, String, String) {
    run_sliced(machine, program, None)
}

/// The same, at time slices of `slice` polls, if given (`FIXPT_SLICE`).
fn run_sliced(machine: &'static str, program: &str, slice: Option<u32>) -> (Option<i32>, String, String) {
    let path = format!("{}/tests/programs/stage/{program}", env!("CARGO_MANIFEST_DIR"));
    let mut cmd = Command::new(FIXPT);
    if let Some(n) = slice {
        cmd.env("FIXPT_SLICE", n.to_string());
    }
    let out = cmd.args(["--fx26-machine", machine, "run", &path]).stdin(Stdio::null()).output().expect("runs");
    (out.status.code(), String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned())
}

/// Whether `machine` runs here: the native convention's only where it
/// does, and a machine of machine code only where there is one.
fn runs_here(machine: &str) -> bool {
    let native = machine.ends_with("nativecc") && machine != "fx-cells-rsinterp-nativecc";
    let code = machine.contains("jit") || machine.contains("asm");
    (!native || fixpt_native::NATIVE_CONVENTION_AVAILABLE) && (!code || fixpt_native::CELLULAR_AVAILABLE)
}

const STAGED: &str = "42
43
refused 6 10: argument 1 is a string, where a int is expected
refused 6 7: unbound variable `z`
refused 0 20: a (subr pure () int) is expected here, and this is a (subr (io stdout) () int)
  beyond what is expected, it has (io stdout)
refused 1 7: unbound variable `define`
made
said
111111111111111111111111111111
84
";

#[test]
fn code_is_staged_or_refused() {
    let runs: Vec<_> = STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run(m, "stage.fx")))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        assert_eq!((status, out.as_str()), (Some(0), STAGED), "{m}: {err}");
    }
}

/// What a stage binds, refused or made, is gone for the next, though the
/// front end that checks them keeps the standard environment between
/// them (`check-staged`).
#[test]
fn a_stage_leaves_nothing_bound_for_the_next() {
    let want = "refused: a int is expected here, and this is a string\nrefused: unbound variable `y`\n3\nrefused: unbound variable `y`\n\
                refused: a int is expected here, and this is a (moduleof (val x int) (val bump (subr pure (int) int)))\n42\n";
    let runs: Vec<_> = STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run(m, "kept.fx")))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        assert_eq!((status, out.as_str()), (Some(0), want), "{m}: {err}");
    }
}

/// A stage against a module whose type names the program's own generative
/// types: the stage's checker makes each from the definition its rep
/// carries (`TODO.md` §206); refused, by text, before.
#[test]
fn a_stage_takes_the_programs_generative_types() {
    let want = "41\n6\nrefused: argument 1 is a int, where a id is expected\n10\n";
    let runs: Vec<_> = STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run(m, "generative.fx")))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        assert_eq!((status, out.as_str()), (Some(0), want), "{m}: {err}");
    }
}

/// A process stages code while another runs, at tiny time slices: the
/// checker is not the program, and no poll in it switches to the program's
/// tasks (`TODO.md` §187: on native code, it ran them on a machine that
/// could not).
#[test]
fn a_process_stages_while_another_runs() {
    let runs: Vec<_> =
        STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run_sliced(m, "in-a-process.fx", Some(7))))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        assert_eq!((status, out.as_str()), (Some(0), "210 4501507\n"), "{m}: {err}");
    }
}

/// Staged code changes the program's state through `m`: a reference it
/// holds, and a global one of its procedures names; the program sees both.
#[test]
fn staged_code_changes_what_the_module_reaches() {
    let runs: Vec<_> = STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run(m, "state.fx")))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        assert_eq!((status, out.as_str()), (Some(0), "made\n2 15\n"), "{m}: {err}");
    }
}

/// What `stage` refuses before the program runs, both checkers alike: a
/// module not given by its name, and what is not a module.
#[test]
fn a_module_is_named() {
    for (program, why) in [("unnamed.fx", "4:21: `stage` takes a module by its name"), ("not-a-module.fx", "4:21: `stage` takes a module, not a int")] {
        let path = format!("{}/tests/programs/stage/{program}", env!("CARGO_MANIFEST_DIR"));
        let out = Command::new(FIXPT).args(["check", &path]).output().expect("runs");
        let out = String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr);
        assert!(out.contains(why) && out.contains("both checkers agree"), "{program}: {out}");
    }
}

/// The output of `programs/stage/session.fx` where a session is kept.
const SESSION: &str = "defined a
33
defined f
120
defined g
a: int to string, used by g
fresh
not defined: `a` is defined already, and the redefinition was refused
12
defined a
101
defined twice
3
not defined: the session changed since this definition was checked: check it again
refused: a int is expected here, and this is a string
refused: argument 1 is a int, where a (union nil (pairof ? ? r)) is expected
defined a
refused: `g` is broken, since `a` was redefined (a int is expected here, and this is a string): define it again to use it
";

/// Evidence (`docs/research/eval.md`, "Evidence"): `stage` within a
/// `plambda`, checked against its effect, type and region parameters as
/// they were instantiated, given their evidence; a session's steps too; a
/// bound standing for a larger effect.
/// Alike on every machine.
#[test]
fn staged_code_is_checked_against_what_a_variable_was_given() {
    for (program, want) in [("evidence.fx", EVIDENCE), ("evidence-region.fx", EVIDENCE_REGION), ("evidence-session.fx", EVIDENCE_SESSION), ("evidence-bound.fx", EVIDENCE_BOUND)] {
        let runs: Vec<_> = STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run(m, program)))).collect();
        for (m, t) in runs {
            let (status, out, err) = t.join().expect("ran");
            assert_eq!((status, out.as_str()), (Some(0), want), "{program} on {m}: {err}");
        }
    }
}

/// Evidence missing, a bound where its variable is taken, or in a list a
/// region variable names, and exact evidence made of a bound: each refused
/// as the program is checked, by either checker.
#[test]
fn staging_without_evidence_is_refused() {
    let refusals = [
        ("evidence-missing.fx", "a variable: give it its evidence, a `(effectrep e)`"),
        ("evidence-bound-taken.fx", "may stand only where less is safe"),
        ("evidence-bound-reify.fx", "makes exact evidence, so it is given exact evidence"),
        ("evidence-bound-region.fx", "a bound of `t`, which may be of less than `t` is"),
    ];
    for (program, said) in refusals {
        for m in ["rs-scheme-vm", "fx-cells-rsinterp"] {
            let (status, _, err) = run(m, program);
            assert_ne!(status, Some(0), "{program} on {m}");
            assert!(err.contains(said), "{program} on {m}: {err}");
        }
    }
}

const EVIDENCE: &str = "42
refused: a (subr pure () int) is expected here, and this is a (subr (io stdout) () int)
  beyond what is expected, it has (io stdout)
out
41
joined
41
82
text
refused: a string is expected here, and this is a int
";

const EVIDENCE_REGION: &str = "5
refused: a (subr (read %region-1) () int) is expected here, and this is a (subr (maxeff (read %region-1) (write %region-1)) () int)
  beyond what is expected, it has (write %region-1)
7
refused: a (subr (read @a) () int) is expected here, and this is a (subr (maxeff (read @a) (write @a)) () int)
  beyond what is expected, it has (write @a)
";

const EVIDENCE_BOUND: &str = "42
refused: a (subr pure () int) is expected here, and this is a (subr (io stdout) () int)
  beyond what is expected, it has (io stdout)
out
41
called
41
3
";

const EVIDENCE_SESSION: &str = "defined a
12
refused: a (subr pure () int) is expected here, and this is a (subr (io stdout) () int)
  beyond what is expected, it has (io stdout)
out
11
b
defined b
13
";

/// Sessions in the condition-raising style (`fx26:session-conditions.fx`):
/// a redefinition raised to the handler, which answers, refuses or
/// escapes; a fresh definition raising nothing. Alike on every machine.
#[test]
fn a_redefinition_is_raised_to_the_handler() {
    let runs: Vec<_> = STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run(m, "session-conditions.fx")))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        assert_eq!((status, out.as_str()), (Some(0), RAISED), "{m}: {err}");
    }
}

const RAISED: &str = "defined a
11
redefines a: int to int
not defined: `a` is defined already, and the redefinition was refused
11
redefines a: int to int
defined a
30
escaped, redefining a
30
defined b
32
";

/// A commit's initializer runs as the program calls `go`, the procedure
/// readying it gives, not as it is readied: alike on every machine.
#[test]
fn a_commit_runs_as_the_program_calls_it() {
    let runs: Vec<_> = STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run(m, "commit.fx")))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        assert_eq!((status, out.as_str()), (Some(0), "readied\ninitializer\ndefined k\n"), "{m}: {err}");
    }
}

/// Staged code and the program's call each other in tail position on every
/// machine (Heist's request, `TODO.md` §201): a staged loop of a million
/// steps through a procedure of the program runs in constant space. On the
/// native-convention machines only if staged code is native code, as the
/// program's is: a call between native and cellular code is no tail call.
#[test]
fn a_staged_loop_through_the_programs_procedure_runs_in_constant_space() {
    let runs: Vec<_> = STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run(m, "tail-across.fx")))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        assert_eq!((status, out.as_str()), (Some(0), "42\n"), "{m}: {err}");
    }
}

/// A stage against a module a global seals, its abstract type read back by
/// the staged checker, on every machine (Heist's request, `TODO.md` §201).
#[test]
fn a_stage_against_a_sealed_module_is_checked() {
    let runs: Vec<_> = STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run(m, "sealed.fx")))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        assert_eq!((status, out.as_str()), (Some(0), "2\n"), "{m}: {err}");
    }
}

/// Knots through a session's own globals refused as at the top level, at
/// their first definitions: a procedure kept in what a global holds that
/// reads any global, and a procedure that does (`Checker::no_reaching_itself`).
#[test]
fn a_session_refuses_knots_through_its_globals() {
    const WANT: &str = "refused: `tbl` keeps a procedure that reads `@globals`, so it could reach itself through a \
                        global: it must say `spin`, and it is a (subr (read @globals) () int)\nrefused: calling `g` may \
                        read any global, `g` too, so `g` may reach itself through a global: its type must say `spin`\n\
                        defined g\nrunning\n";
    let runs: Vec<_> = STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run(m, "session-knot.fx")))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        assert_eq!((status, out.as_str()), (Some(0), WANT), "{m}: {err}");
    }
}

/// A session (`docs/research/eval.md`, "Sessions"): forms checked in it, an
/// expression's procedure called, a definition committed as the program
/// decides; redefinitions
/// reported, refused, assigned, shadowing a host's name, and one whose
/// users run again, one broken; a pending one gone stale. Alike on every
/// machine.
#[test]
fn a_session_keeps_definitions() {
    let runs: Vec<_> = STAGING.iter().filter(|m| runs_here(m)).map(|m| (*m, std::thread::spawn(move || run(m, "session.fx")))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        assert_eq!((status, out.as_str()), (Some(0), SESSION), "{m}: {err}");
    }
}

