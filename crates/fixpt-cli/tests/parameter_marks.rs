//! A module parameter's mark (the user's, 2026-11-26; `docs/fx26.md`,
//! "Marked, qualified or not"): `#:unqualified`, its names the file's own;
//! `#:qualified`, reached as `m::name`; none, included as before and warned
//! of, a future version making it qualified; and `qualified`, the mark's
//! spelling before keywords, refused saying so. Alike by the Rust checker
//! (`eval`) and on a machine of the front end written in FX-26.
use std::path::{Path, PathBuf};
use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("marks-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("made");
    dir
}

/// `main.fx` run in a directory where `b.fx` is a file over `a.fx` with the
/// parameter `binder` and the body `body`, by `args`: whether it succeeded,
/// its output and its errors.
fn run(name: &str, binder: &str, body: &str, args: &[&str]) -> (bool, String, String) {
    let dir = scratch(name);
    std::fs::write(dir.join("a.fx"), "(define x int 1)\n").expect("written");
    std::fs::write(dir.join("b.fx"), format!("(module-parameters ({binder}))\n{body}\n")).expect("written");
    std::fs::write(dir.join("main.fx"), "(define a (load-module \"a.fx\"))\n(define b ((load-module \"b.fx\") a))\n(write-out (int->string (with b y)))\n").expect("written");
    let out = Command::new(FIXPT).args(args).arg("main.fx").current_dir(&dir).env("FIXPT_NO_FASL", "1").output().expect("runs");
    (out.status.success(), String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned())
}

const WAYS: [&[&str]; 2] = [&["run"], &["--fx26-machine", "fx-cells-rsinterp", "run"]];

#[test]
fn an_unqualified_parameters_names_are_the_files() {
    for (i, w) in WAYS.iter().enumerate() {
        let (ok, out, err) = run(&format!("unq{i}"), "(m-a (load-moduleof \"a.fx\") #:unqualified)", "(define y int (+ 1 x))", w);
        assert!(ok && out == "2" && !err.contains("warning"), "{w:?}: {out}{err}");
    }
}

#[test]
fn a_qualified_parameters_names_are_reached_by_path() {
    for (i, w) in WAYS.iter().enumerate() {
        let (ok, out, err) = run(&format!("q{i}"), "(m-a (load-moduleof \"a.fx\") #:qualified)", "(define y int (+ 1 m-a::x))", w);
        assert!(ok && out == "2" && !err.contains("warning"), "{w:?}: {out}{err}");
        let (ok, _, err) = run(&format!("qbare{i}"), "(m-a (load-moduleof \"a.fx\") #:qualified)", "(define y int (+ 1 x))", w);
        assert!(!ok && err.contains("unbound variable `x`"), "{w:?}: {err}");
    }
}

/// No mark: included, as before, and warned of once, at the parameter.
#[test]
fn an_unmarked_parameter_is_included_and_warned_of() {
    for (i, w) in WAYS.iter().enumerate() {
        let (ok, out, err) = run(&format!("none{i}"), "(m-a (load-moduleof \"a.fx\"))", "(define y int (+ 1 x))", w);
        assert!(ok && out == "2", "{w:?}: {out}{err}");
        let warned = "fixpt: warning: in `b.fx`, 1:22: module parameter `m-a` has no mark, so its names are this file's own, as `#:unqualified` says: write `#:unqualified` to keep them so; a future version will make a parameter with no mark qualified, `#:qualified`, its names reached as `m-a::name`, which will likely break this file";
        assert_eq!(err.matches(warned).count(), 1, "{w:?}: {err}");
    }
}

#[test]
fn the_old_mark_is_refused_saying_so() {
    for (i, w) in WAYS.iter().enumerate() {
        let (ok, _, err) = run(&format!("old{i}"), "(m-a (load-moduleof \"a.fx\") qualified)", "(define y int 2)", w);
        assert!(!ok && err.contains("in `b.fx`, 1:49: a module parameter's mark is a keyword now: `#:qualified`"), "{w:?}: {err}");
    }
}
