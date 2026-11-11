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

/// A module file's own macros, used in it (`binding-shapes.md`, step 3;
/// Heist's (a)): their templates' free names the file's items, hidden or
/// not, a binder around a use that would capture one renamed; and where
/// the file is imported, as before.
#[test]
fn a_file_uses_its_own_macros() {
    for (name, want) in [("main-own.fx", "(3 10 8 8) : "), ("main-within.fx", "32 : int"), ("main-procedural.fx", "66 : int")] {
        for m in MACHINES {
            let (out, err) = eval(m, name);
            assert!(out.lines().last().is_some_and(|l| l.starts_with(want)), "{name} on {m}: {out}{err}");
        }
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
        ("main-own-before.fx", "`one` is a macro of this file used before the file defines it"),
        ("main-own-with.fx", "where a `with` or `include` around its use may give it: not yet"),
        ("main-own-typed.fx", "a typed hole in a macro a file uses itself, not yet"),
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
