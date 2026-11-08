//! `(import-with-syntax lib)` (`typed-macros.md`, "Decided: macros come
//! with a file"): the file `lib` loads, its names and its macros, each
//! macro meaning what it meant in its file, on every machine.

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

const MACHINES: &[&str] = &["rs-scheme-vm", "fx-ast-eval", "fx-cells-rsinterp", "fx-regs-rsjit-cellcc"];

/// `fixpt eval` of program `name` on `machine`: what it printed, and said.
fn eval(machine: &str, name: &str) -> (String, String) {
    let path = format!("{}/tests/programs/import-with-syntax/{name}", env!("CARGO_MANIFEST_DIR"));
    let out = Command::new(FIXPT).args(["--machine", machine, "eval", &path]).output().expect("runs");
    (String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned())
}

#[test]
fn a_files_macros_mean_what_they_meant_there() {
    for m in MACHINES {
        let (out, err) = eval(m, "main.fx");
        assert!(out.lines().last().is_some_and(|l| l.starts_with("2099 : int")), "{m}: {out}{err}");
    }
}

#[test]
fn a_files_macros_types_are_its_own() {
    for m in MACHINES {
        let (out, err) = eval(m, "main-types.fx");
        assert!(out.lines().last().is_some_and(|l| l.starts_with("12 : int")), "{m}: {out}{err}");
    }
}

#[test]
fn a_files_macro_makes_definitions() {
    for m in MACHINES {
        let (out, err) = eval(m, "main-defn.fx");
        assert!(out.lines().last().is_some_and(|l| l.starts_with("18 : int")), "{m}: {out}{err}");
    }
}

#[test]
fn only_and_except_take_macros_and_names_alike() {
    for (name, want) in [("main-only.fx", "1020 : int"), ("main-except.fx", "1030 : int"), ("main-except-all.fx", "2 : int")] {
        for m in MACHINES {
            let (out, err) = eval(m, name);
            assert!(out.lines().last().is_some_and(|l| l.starts_with(want)), "{name} on {m}: {out}{err}");
        }
    }
}

#[test]
fn what_cannot_be_imported_is_refused() {
    let cases = [
        ("main-secret.fx", "`hidden` is neither a value the file's module shows nor a standard binding"),
        ("main-within.fx", "`one` is a macro of this file"),
        ("main-not-load.fx", "takes a name defined as `(load-module \"path\")`"),
        ("main-only-not-given.fx", "unbound variable `limit`"),
        ("main-only-hidden.fx", "`twice` is nothing `lib` gives"),
        ("main-poly.fx", "a file's macro's description with a binder of its own or a part a use gives in it: not yet"),
    ];
    for (name, why) in cases {
        let (out, err) = eval("rs-scheme-vm", name);
        assert!(err.contains(why) || out.contains(why), "{name}: {out}{err}");
    }
}
