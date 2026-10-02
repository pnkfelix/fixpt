//! First-class modules run the same way in every run mode
//! (`docs/research/first-class-modules.md`): lowered (the default), by the
//! evaluator written in FX-26, and compiled by the compiler written in FX-26
//! to cellular words run on each cellular machine (compiled to machine code
//! by the compiler written in Rust, or by `native.fx`), with each calling
//! convention. Each program, given whole to `fixpt eval` and typed form by
//! form at the REPL, gives the lowered answer its first line says.

use std::process::{Command, Stdio};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// The programs, in `crates/fixpt-fx26/tests/programs/modules`: a module
/// read from a file (`load-module`), a functor (a dependent procedure), a
/// module reshaped where fewer values are wanted, and a module made in a
/// procedure over a region; and those also typed at the REPL.
const PROGRAMS: [&str; 4] = ["load", "functor-max", "width", "region-parameter"];
const AT_THE_REPL: [&str; 2] = ["load", "functor-max"];

/// Each run mode, as options.
const MODES: [&[&str]; 10] = [
    &[],
    &["--fx26-run", "evaluate"],
    &["--fx26-run", "cellular"],
    &["--fx26-run", "cellular", "--cellular-machine", "native"],
    &["--fx26-run", "cellular", "--cellular-machine", "native-compiled"],
    &["--fx26-run", "cellular", "--cellular-machine", "fx-compiled"],
    &["--fx26-run", "cellular", "--cellular-machine", "registers"],
    &["--fx26-run", "cellular", "--cellular-machine", "stencils"],
    &["--fx26-run", "cellular", "--calling-convention", "native"],
    &["--fx26-run", "cellular", "--cellular-machine", "registers", "--calling-convention", "native"],
];

fn dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../fixpt-fx26/tests/programs/modules")
}

/// `fixpt` with `args`, `stdin` given it, run in `cwd`: its output, or why
/// it failed.
fn fixpt(args: &[&str], stdin: &str, cwd: &std::path::Path) -> Result<String, String> {
    use std::io::Write as _;
    let mut child = Command::new(FIXPT)
        .args(args)
        .current_dir(cwd)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("fixpt starts");
    child.stdin.take().expect("stdin is piped").write_all(stdin.as_bytes()).expect("can write");
    let out = child.wait_with_output().expect("fixpt finishes");
    let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned());
    if out.status.success() { Ok(stdout) } else { Err(format!("{stdout}{stderr}")) }
}

/// Whether this build runs the stencils machine (it needs nightly).
fn stencils_built() -> bool {
    fixpt(&["--dialect", "fx26", "--fx26-run", "cellular", "--cellular-machine", "stencils", "eval", "(+ 1 2)"], "", &dir()).is_ok()
}

#[test]
fn module_programs_run_alike_in_every_mode() {
    let stencils = stencils_built();
    let mut runs = Vec::new();
    for p in PROGRAMS {
        let text = std::fs::read_to_string(dir().join(format!("{p}.fx"))).unwrap();
        let want = text.lines().next().and_then(|l| l.strip_prefix(";; => ")).expect("a program that runs").to_string();
        let forms: String = text.lines().filter(|l| !l.starts_with(";;")).collect::<Vec<_>>().join("\n") + "\n";
        for mode in MODES {
            if mode.contains(&"stencils") && !stencils {
                continue;
            }
            runs.push((p, mode, want.clone(), forms.clone()));
        }
    }
    // In parallel: each run starts the front end afresh.
    let wrong: Vec<String> = std::thread::scope(|s| {
        let handles: Vec<_> = runs
            .iter()
            .map(|(p, mode, want, forms)| {
                s.spawn(move || {
                    let mut wrong = Vec::new();
                    let file = format!("{p}.fx");
                    let eval: Vec<&str> = mode.iter().copied().chain(["eval", file.as_str()]).collect();
                    match fixpt(&eval, "", &dir()) {
                        Ok(out) if out.lines().filter(|l| !l.is_empty()).last().is_some_and(|l| l.starts_with(&format!("{want} :"))) => {}
                        got => wrong.push(format!("{p} {mode:?}, eval: {got:?}, want {want}")),
                    }
                    if !AT_THE_REPL.contains(p) {
                        return wrong;
                    }
                    let repl: Vec<&str> = ["--dialect", "fx26"].into_iter().chain(mode.iter().copied()).chain(["repl"]).collect();
                    match fixpt(&repl, forms, &dir()) {
                        Ok(out) if out.contains(&format!(" {want} : ")) => {}
                        got => wrong.push(format!("{p} {mode:?}, repl: {got:?}, want {want}")),
                    }
                    wrong
                })
            })
            .collect();
        handles.into_iter().flat_map(|h| h.join().expect("a run")).collect()
    });
    assert!(runs.len() >= 32, "only {} runs", runs.len());
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
