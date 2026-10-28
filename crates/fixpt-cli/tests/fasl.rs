//! `.fasl` files (`docs/research/fasl.md`; the user's, 2026-10-28): a
//! module file compiled by `fixpt compile-file`, whose loads read the
//! `.fasl` beside it while it is fresh. Each program of
//! `tests/programs/modules` gives the same with its module files compiled
//! as without, a stale `.fasl` is said and its source loaded, and a
//! program's `(compile-file "path")` makes one.

use std::path::{Path, PathBuf};
use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");
const PROGRAMS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../fixpt-fx26/tests/programs");

/// A directory of this test's own, empty.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("fasl-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("made");
    dir
}

/// `fixpt ARGS…` in `dir`, with `envs`: whether it succeeded, its output and
/// its errors.
fn fixpt(dir: &Path, args: &[&str], envs: &[(&str, &str)]) -> (bool, String, String) {
    let mut c = Command::new(FIXPT);
    c.args(args).current_dir(dir).env_remove("FIXPT_NO_FASL").env_remove("FIXPT_FASL_SAY");
    for (k, v) in envs {
        c.env(k, v);
    }
    let out = c.output().expect("fixpt runs");
    (out.status.success(), String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned())
}

/// Each `.fx` file in `dir`, by name.
fn fx_files(dir: &Path) -> Vec<PathBuf> {
    let mut fs: Vec<PathBuf> = std::fs::read_dir(dir).expect("a directory").flatten().map(|e| e.path()).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
    fs.sort();
    fs
}

/// `tests/programs/modules` and `module-files` copied into `dir`.
fn copy_suite(dir: &Path) {
    for sub in ["modules", "module-files"] {
        std::fs::create_dir_all(dir.join(sub)).expect("made");
        for f in fx_files(&Path::new(PROGRAMS).join(sub)) {
            std::fs::copy(&f, dir.join(sub).join(f.file_name().expect("a name"))).expect("copied");
        }
    }
}

#[test]
fn every_module_program_gives_the_same_from_fasls() {
    let dir = scratch("suite");
    copy_suite(&dir);
    // Each module file that compiles alone (some are made to be refused).
    let mut compiled = 0;
    for f in fx_files(&dir.join("module-files")) {
        let name = format!("module-files/{}", f.file_name().expect("a name").to_string_lossy());
        if fixpt(&dir, &["compile-file", &name], &[]).0 {
            compiled += 1;
        }
    }
    assert!(compiled >= 40, "only {compiled} module files compiled");
    let programs = fx_files(&dir.join("modules"));
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get()).min(8);
    let chunks: Vec<Vec<PathBuf>> = (0..threads).map(|i| programs.iter().skip(i).step_by(threads).cloned().collect()).collect();
    let runs: Vec<_> = chunks
        .into_iter()
        .map(|chunk| {
            let dir = dir.clone();
            std::thread::spawn(move || {
                let (mut wrong, mut read) = (Vec::new(), 0);
                for p in chunk {
                    let name = format!("modules/{}", p.file_name().expect("a name").to_string_lossy());
                    let (_, out, err) = fixpt(&dir, &["eval", &name], &[("FIXPT_NO_FASL", "1")]);
                    let (_, fout, ferr) = fixpt(&dir, &["eval", &name], &[("FIXPT_FASL_SAY", "1")]);
                    read += ferr.lines().filter(|l| l.contains("is read from")).count();
                    let ferr: String = ferr.lines().filter(|l| !l.contains("is read from")).map(|l| format!("{l}\n")).collect();
                    if (out.as_str(), err.as_str()) != (fout.as_str(), ferr.as_str()) {
                        wrong.push(format!("{name}:\n  from sources: {out}{err}\n  from fasls:   {fout}{ferr}"));
                    }
                }
                (wrong, read)
            })
        })
        .collect();
    let (mut wrong, mut read) = (Vec::new(), 0);
    for r in runs {
        let (w, n) = r.join().expect("ran");
        wrong.extend(w);
        read += n;
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    assert!(read >= 45, "only {read} loads read a `.fasl`");
}

/// A small library: `a.fx`, and `b.fx`, which loads it, and a program of
/// both.
fn library(dir: &Path) {
    std::fs::create_dir_all(dir.join("lib")).expect("made");
    std::fs::write(dir.join("lib/a.fx"), "(define-generative t int)\n(define zero t (up-t 0))\n(define value (subr pure (t) int) (lambda (v) (down-t v)))\n").expect("written");
    std::fs::write(
        dir.join("lib/b.fx"),
        "(define a (load-module \"a.fx\"))\n(define bump (subr pure ((select a t)) int) (lambda (v) (+ 41 ((with a value) v))))\n",
    )
    .expect("written");
    std::fs::write(dir.join("main.fx"), "(define a (load-module \"lib/a.fx\"))\n(define b (load-module \"lib/b.fx\"))\n((with b bump) (with a zero))\n").expect("written");
}

#[test]
fn a_stale_fasl_is_said_and_its_source_loaded() {
    let dir = scratch("stale");
    library(&dir);
    let (ok, out, err) = fixpt(&dir, &["compile-file", "lib/a.fx", "lib/b.fx"], &[]);
    assert!(ok, "{out}{err}");
    assert!(out.contains("; compiled `lib/a.fx` to `lib/a.fasl`") && out.contains("; compiled `lib/b.fx` to `lib/b.fasl`"), "{out}");
    let (ok, out, err) = fixpt(&dir, &["eval", "main.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ok && out.contains("41 : int"), "{out}{err}");
    assert_eq!(err.lines().filter(|l| l.contains("is read from")).count(), 2, "{err}");
    // `a.fx` changed: both stale, `b`'s as `a` is below it.
    std::fs::write(dir.join("lib/a.fx"), "(define-generative t int)\n(define zero t (up-t 1))\n(define value (subr pure (t) int) (lambda (v) (down-t v)))\n").expect("written");
    let (ok, out, err) = fixpt(&dir, &["eval", "main.fx"], &[]);
    assert!(ok && out.contains("42 : int"), "{out}{err}");
    assert!(err.contains("`lib/a.fasl` is stale (its source changed): `lib/a.fx` is loaded from its source"), "{err}");
    assert!(err.contains("`lib/b.fasl` is stale (`a.fx` changed): `lib/b.fx` is loaded from its source"), "{err}");
    // `a` compiled again: `b` still stale, made against the `a` before.
    assert!(fixpt(&dir, &["compile-file", "lib/a.fx"], &[]).0);
    let (_, out, err) = fixpt(&dir, &["eval", "main.fx"], &[]);
    assert!(out.contains("42 : int") && !err.contains("a.fasl") && err.contains("`lib/b.fasl` is stale (`a.fx` changed)"), "{out}{err}");
    // Made for one convention, stale in the other.
    let (_, out, err) = fixpt(&dir, &["--machine", "fx-cells-rsinterp", "eval", "main.fx"], &[]);
    assert!(out.contains("42 : int") && err.contains("is stale (it is for the "), "{out}{err}");
}

#[test]
fn a_program_compiles_a_file_and_another_machine_reads_its_own() {
    let dir = scratch("form");
    library(&dir);
    std::fs::write(dir.join("make.fx"), "(compile-file \"lib/a.fx\")\n(compile-file \"lib/b.fx\")\n").expect("written");
    // On the cellular machine written in Rust, its `.fasl`s that machine's.
    let machine = ["--machine", "fx-cells-rsinterp"];
    let (ok, out, err) = fixpt(&dir, &[&machine[..], &["run", "make.fx"]].concat(), &[]);
    assert!(ok && out.contains("; compiled `lib/b.fx` to `"), "{out}{err}");
    assert!(dir.join("lib/a.fasl").exists() && dir.join("lib/b.fasl").exists());
    let (ok, out, err) = fixpt(&dir, &[&machine[..], &["eval", "main.fx"]].concat(), &[("FIXPT_FASL_SAY", "1")]);
    assert!(ok && out.contains("41 : int"), "{out}{err}");
    assert_eq!(err.lines().filter(|l| l.contains("is read from")).count(), 2, "{err}");
}
