//! `stage` (`docs/research/eval.md`), as `fixpt run` performs it: code a
//! program gives as a datum, checked against a module's type, an effect
//! and a type as the program runs, and made a procedure, or refused with a
//! value saying why and where (`programs/stage/`). On every machine that
//! compiles with the compilers written in FX-26; the lowering's and the
//! evaluator's refuse all code, saying they cannot stage it.
use std::process::{Command, Stdio};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// The machines that stage code: cellular words, interpreted and compiled,
/// register code, and native code where it runs.
const STAGING: &[&str] = &[
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

/// Where code is not compiled by the compilers written in FX-26, every
/// `stage` is refused, as a value the program sees.
#[test]
fn a_machine_that_cannot_stage_says_so() {
    for m in ["rs-scheme-vm", "fx-ast-eval"] {
        let (status, out, err) = run(m, "stage.fx");
        assert_eq!(status, Some(0), "{m}: {err}");
        assert!(out.lines().filter(|l| l.contains("cannot stage code")).count() == 9, "{m}: {out}");
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
