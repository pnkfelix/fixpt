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

/// A file's macro that defines a macro: the defined macro's free names the
/// file's, where the macro that defines it is defined.
#[test]
fn a_files_macro_defines_a_macro_of_its_names() {
    for m in MACHINES {
        let (out, err) = eval(m, "main-defines-macro.fx");
        assert!(out.lines().last().is_some_and(|l| l.starts_with("13 : int")), "{m}: {out}{err}");
    }
}

/// A module file's own macros, used in it (`binding-shapes.md`, step 3;
/// Heist's (a)): their templates' free names the file's items, hidden or
/// not, a binder around a use that would capture one renamed; and where
/// the file is imported, as before.
#[test]
fn a_file_uses_its_own_macros() {
    for (name, want) in [("main-own.fx", "(3 10 8 8 10) : "), ("main-within.fx", "32 : int"), ("main-procedural.fx", "66 : int")] {
        for m in MACHINES {
            let (out, err) = eval(m, name);
            assert!(out.lines().last().is_some_and(|l| l.starts_with(want)), "{name} on {m}: {out}{err}");
        }
    }
}

/// A file's phase-1 forms (`begin-for-syntax`) are its own macros': its
/// `scale` for its macro, the importer's own `scale` for the importer's.
#[test]
fn a_files_phase_1_is_its_own() {
    for m in MACHINES {
        let (out, err) = eval(m, "main-for-syntax.fx");
        assert!(out.lines().last().is_some_and(|l| l.starts_with("1044 : ")), "{m}: {out}{err}");
    }
}

/// A file's trailmark (`typed-macros.md`, "Trailmarks"): a use
/// writes it by the name the importer has it by, and the file's templates
/// write it whatever the importer takes.
#[test]
fn a_files_trailmark_is_its_own() {
    for (name, want) in [("main-marks.fx", "(9 7) : "), ("main-marks-only.fx", "7 : int")] {
        for m in MACHINES {
            let (out, err) = eval(m, name);
            assert!(out.lines().last().is_some_and(|l| l.starts_with(want)), "{name} on {m}: {out}{err}");
        }
    }
}

#[test]
fn only_and_except_take_macros_and_names_alike() {
    // A file of macros alone: its `include` gives nothing, and is nothing
    // (Heist's).
    for (name, want) in [("main-only.fx", "1020 : int"), ("main-except.fx", "1030 : int"), ("main-except-all.fx", "2 : int"), ("main-macros-only.fx", "10 : int")] {
        for m in MACHINES {
            let (out, err) = eval(m, name);
            assert!(out.lines().last().is_some_and(|l| l.starts_with(want)), "{name} on {m}: {out}{err}");
        }
    }
}

/// A file's macro's descriptions with a binder of their own or a part a
/// use gives in them: each name the template writes free read as the file
/// has it, one at a time, its binders renamed, the use's parts as they are
/// where it is used (`typed-macros.md`, "Decided: macros come with a file").
#[test]
fn a_files_macros_descriptions_hold_their_binders_and_a_uses_parts() {
    for (name, want) in [("main-poly.fx", "4 : int"), ("main-pairs.fx", "16 : int")] {
        for m in MACHINES {
            let (out, err) = eval(m, name);
            assert!(out.lines().last().is_some_and(|l| l.starts_with(want)), "{name} on {m}: {out}{err}");
        }
    }
}

/// A module file's `import-with-syntax` (`binding-shapes.md`, step 4;
/// Heist's (b)): the macros it takes used in the file, each as its own file
/// means it, and given on unless the import is hidden, as the file's own
/// are; `only` taking of them alike.
#[test]
fn a_module_file_imports_a_files_macros() {
    for (name, want) in [("main-imports-in-file.fx", "(6 10 10) : "), ("main-imports-hidden.fx", "(4 12 0) : "), ("main-imports-only.fx", "10 : int")] {
        for m in MACHINES {
            let (out, err) = eval(m, name);
            assert!(out.lines().last().is_some_and(|l| l.starts_with(want)), "{name} on {m}: {out}{err}");
        }
    }
}

/// A macro a module file's own use of a macro that defines one makes (TODO
/// §287): given on as a written one is, its names the file's.
#[test]
fn a_files_made_macro_is_given_on() {
    for m in MACHINES {
        let (out, err) = eval(m, "main-makes.fx");
        assert!(out.lines().last().is_some_and(|l| l.starts_with("(10 3 10) : ")), "{m}: {out}{err}");
    }
}

/// The macros of instances of a file with module parameters
/// (`binding-shapes.md`, step 4 (c)): each names its own instance, by its
/// name, which a binder at a use does not capture; two instances' macros,
/// written or made, apart.
#[test]
fn an_instances_macros_name_it() {
    for m in MACHINES {
        let (out, err) = eval(m, "main-instances.fx");
        assert!(out.lines().last().is_some_and(|l| l.starts_with("(206 12 5) : ")), "{m}: {out}{err}");
    }
}

#[test]
fn what_cannot_be_imported_is_refused() {
    let cases = [
        ("main-secret.fx", "`nowhere` is neither a value the file defines nor a standard binding"),
        ("main-own-before.fx", "`one` is a macro of this file used before the file defines it"),
        ("main-own-with.fx", "where a `with` or `include` around its use may give it: not yet"),
        ("main-own-typed.fx", "a typed hole in a macro a file uses itself, not yet"),
        ("main-not-load.fx", "takes a name defined as `(load-module \"path\")`"),
        ("main-only-not-given.fx", "unbound variable `limit`"),
        ("main-only-hidden.fx", "`twice` is nothing `lib` gives"),
        ("main-imports-hidden-not-given.fx", "unbound variable `twice`"),
        ("main-imports-twice.fx", "`twice` is a macro this file gives twice"),
        ("main-makes-hidden.fx", "unbound variable `cap`"),
        ("main-imports-global-before.fx", "`clamp` is defined already: a macro may not take its name"),
        ("main-makes-global-before.fx", "`clamp` is defined already: a macro may not take its name"),
        ("main-instance-plain.fx", "`counter.fx` takes module parameters: import the macros of an instance of it"),
        ("main-instance-with.fx", "`a`, the instance an imported macro names, where a `with` or `include` around its use may give it: not yet"),
        ("main-instance-module.fx", "`a`, which an expansion here names as its macro has it, is bound inside a `module` around the use"),
        ("main-own-module.fx", "`limit`, which an expansion here names as its macro has it, is bound inside a `module` around the use"),
        ("main-instance-in-file.fx", "`a` is an instance of a file with module parameters: a module file cannot import its macros, not yet"),
    ];
    for (name, why) in cases {
        let (out, err) = eval("rs-scheme-vm", name);
        assert!(err.contains(why) || out.contains(why), "{name}: {out}{err}");
    }
}

/// A program's `import-with-syntax` reads its file from the program's
/// directory, not the working directory (Heist's report, 2026-11-18: `fixpt
/// run prog/main.fx` read `lib.fx` from where it was run, its forms read,
/// and their macros expanded, before the directory was set): run, and its
/// file compiled, from the directory above it.
#[test]
fn a_programs_import_reads_from_its_directory() {
    let dir = std::env::temp_dir().join(format!("fixpt-iws-dir-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("prog")).expect("made");
    std::fs::write(dir.join("prog/lib.fx"), "(define-syntax twice (macro (_ expr) expr) (syntax-rules ((_ e) (let ((x e)) (+ x x)))))\n").expect("written");
    std::fs::write(
        dir.join("prog/main.fx"),
        "(define lib (load-module \"lib.fx\"))\n(import-with-syntax lib)\n(define main (subr pure () int) (lambda () (twice 21)))\n",
    )
    .expect("written");
    for m in MACHINES {
        let out = Command::new(FIXPT).args(["--machine", m, "run", "prog/main.fx"]).current_dir(&dir).output().expect("runs");
        assert_eq!(out.status.code(), Some(42), "{m}: {}", String::from_utf8_lossy(&out.stderr));
    }
    let out = Command::new(FIXPT).args(["compile-file", "prog/main.fx"]).current_dir(&dir).output().expect("runs");
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let _ = std::fs::remove_dir_all(&dir);
}

/// A file's macro whose expansion uses another of its file's, a procedural
/// one, which the importer has only by the name it gives it (Heist's report,
/// 2026-11-18): a `syntax-rules` template's use of it in a module file (the
/// expander written in FX-26 took it for a `syntax-rules` macro of no
/// clauses), and a transformer's renamed name of it, at a program's top
/// level and in a module file (it was taken for a standard name). Each
/// expands to the file's macro, on every machine, both checkers agreeing.
#[test]
fn a_files_macro_expanding_to_its_procedural_one() {
    for name in ["main-via-module.fx", "main-via-er.fx", "main-via-er-module.fx"] {
        for m in MACHINES {
            let (out, err) = eval(m, name);
            assert!(out.lines().last().is_some_and(|l| l.starts_with("7 : int")), "{name} on {m}: {out}{err}");
        }
        let path = format!("{}/tests/programs/import-with-syntax/{name}", env!("CARGO_MANIFEST_DIR"));
        let out = Command::new(FIXPT).args(["check", &path]).output().expect("runs");
        let said = String::from_utf8_lossy(&out.stdout);
        assert!(said.contains("both checkers agree"), "{name}: {said}{}", String::from_utf8_lossy(&out.stderr));
    }
}

/// A module file that defines macros has a frame (`TODO.md` §300), a shown
/// member of its own name, `%frame:…`, holding the values its expansions may
/// reach that it does not show: its `hide`n ones and those its module
/// parameters bring. Those its `syntax-rules` templates name, if its macros
/// are all such; every one, if one is procedural. A file of no macros has
/// none. Both checkers agree, and each file's frame is the same read from
/// its `.fasl` (`programs/import-with-syntax/frame`, copied, as `.fasl`s are
/// written beside them).
#[test]
fn a_module_files_frame_holds_what_its_macros_may_reach() {
    let dir = std::env::temp_dir().join(format!("fixpt-iws-frame-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("made");
    let from = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs/import-with-syntax/frame");
    for name in ["core.fx", "rules.fx", "er.fx", "plain.fx", "param.fx", "main.fx"] {
        std::fs::copy(from.join(name), dir.join(name)).expect("copied");
    }
    let frame = |l: &str| l.split("(val %frame:").nth(1).map(|r| r.split_once(' ').map(|(_, f)| f.to_string()).unwrap_or_default());
    for round in ["source", "fasl"] {
        if round == "fasl" {
            for name in ["rules.fx", "er.fx", "plain.fx", "core.fx", "param.fx"] {
                let out = Command::new(FIXPT).args(["compile-file", name]).current_dir(&dir).output().expect("runs");
                assert!(out.status.success(), "{name}: {}", String::from_utf8_lossy(&out.stderr));
            }
        }
        let out = Command::new(FIXPT).args(["check", "main.fx"]).current_dir(&dir).output().expect("runs");
        let said = String::from_utf8_lossy(&out.stdout).to_string();
        assert!(said.contains("both checkers agree"), "{round}: {said}{}", String::from_utf8_lossy(&out.stderr));
        let shapes: Vec<&str> = said.lines().filter(|l| l.starts_with("(moduleof")).collect();
        assert_eq!(shapes.len(), 4, "{round}: {said}");
        assert_eq!(frame(shapes[0]).as_deref(), Some("(moduleof (val named int)))) ! (read (globals rules))"), "{round}: {}", shapes[0]);
        assert!(frame(shapes[1]).is_some_and(|f| f.starts_with("(moduleof (val a int) (val b int))")), "{round}: {}", shapes[1]);
        assert_eq!(frame(shapes[2]), None, "{round}: {}", shapes[2]);
        assert!(frame(shapes[3]).is_some_and(|f| f.starts_with("(moduleof (val own int) (val core-helper (subr pure (int) int)))")), "{round}: {}", shapes[3]);
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// A file's macro's expansion reaches a value the file hides, through its
/// frame (`TODO.md` §300): a `syntax-rules` template's name of it; a
/// procedural transformer that passes `rename` to a helper, which renames
/// it (what a name means is the renaming's own, wherever it is called); and
/// a hidden value of a standard binding's name, which is the file's, not
/// the standard one (it was taken for the standard one). On every machine,
/// both checkers agreeing.
#[test]
fn a_files_macro_reaches_what_the_file_hides() {
    for (name, want) in [("main-frame-rules.fx", "42 : int"), ("main-frame-er.fx", "5 : int"), ("main-frame-shadow.fx", "99 : int")] {
        for m in MACHINES {
            let (out, err) = eval(m, name);
            assert!(out.lines().last().is_some_and(|l| l.starts_with(want)), "{name} on {m}: {out}{err}");
        }
        let path = format!("{}/tests/programs/import-with-syntax/{name}", env!("CARGO_MANIFEST_DIR"));
        let out = Command::new(FIXPT).args(["check", &path]).output().expect("runs");
        let said = String::from_utf8_lossy(&out.stdout);
        assert!(said.contains("both checkers agree"), "{name}: {said}{}", String::from_utf8_lossy(&out.stderr));
    }
}
