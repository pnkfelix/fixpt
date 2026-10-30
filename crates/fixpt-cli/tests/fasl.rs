//! `.fasl` files (`docs/research/fasl.md`; the user's, 2026-10-28): a
//! file compiled by `fixpt compile-file`, whose loads (or, a program's
//! file's, `fixpt eval` and `,load`) read the `.fasl` beside it while it is
//! fresh. Each program of `tests/programs/modules` gives the same with its
//! module files compiled as without, and programs of other directories the
//! same compiled as programs; a stale `.fasl` is said and its source
//! loaded, and a program's `(compile-file "path")` makes one.

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
    copy_dirs(dir, &["modules", "module-files"]);
}

/// The directories `subs` of `tests/programs` copied into `dir`.
fn copy_dirs(dir: &Path, subs: &[&str]) {
    for sub in subs {
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

/// Program files of `tests/programs`, each compiled as a program's
/// (`compile-file --program`): each that compiles gives the same with its
/// `.fasl` as without, and most read it.
#[test]
fn programs_give_the_same_from_fasls() {
    let dir = scratch("programs");
    let subs = ["run", "control", "higher-kinds", "recursive", "bloblet", "native", "lemmas", "regions"];
    copy_dirs(&dir, &[&subs[..], &["module-files"]].concat());
    let programs: Vec<PathBuf> = subs.iter().flat_map(|s| fx_files(&dir.join(s)).into_iter().map(move |f| Path::new(s).join(f.file_name().expect("a name")))).collect();
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get()).min(8);
    let chunks: Vec<Vec<PathBuf>> = (0..threads).map(|i| programs.iter().skip(i).step_by(threads).cloned().collect()).collect();
    let runs: Vec<_> = chunks
        .into_iter()
        .map(|chunk| {
            let dir = dir.clone();
            std::thread::spawn(move || {
                let (mut wrong, mut read) = (Vec::new(), 0);
                for p in chunk {
                    let name = p.display().to_string();
                    if !fixpt(&dir, &["compile-file", "--program", &name], &[]).0 {
                        continue;
                    }
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
    assert!(read >= 150, "only {read} programs read their `.fasl`");
}

#[test]
fn a_program_fasl_is_stale_when_what_it_uses_changed() {
    let dir = scratch("program");
    std::fs::write(dir.join("base.fx"), "(define scale (subr pure (int) int) (lambda (n) (* n 10)))\n").expect("written");
    std::fs::write(dir.join("prog.fx"), "(define* twice (subr pure (int) int) (lambda (n) (scale (scale n))))\n(write-out \"ran\\n\")\n(twice 3)\n").expect("written");
    std::fs::write(dir.join("other.fx"), "(define scale (subr pure (int) bool) (lambda (n) #t))\n").expect("written");
    // Compiled after `base.fx`, by a program that runs nothing of it.
    std::fs::write(dir.join("make.fx"), "(compile-file \"prog.fx\" program)\n").expect("written");
    let (ok, out, err) = fixpt(&dir, &["run", "base.fx", "make.fx"], &[]);
    assert!(ok && out.contains("; compiled `prog.fx` to `") && !out.contains("ran"), "{out}{err}");
    let (ok, out, err) = fixpt(&dir, &["run", "base.fx", "prog.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ok && out == "ran\n" && err.contains("`prog.fx` is read from `prog.fasl`"), "{out}{err}");
    // `scale` of another type: the code of `twice` is not right for it.
    let (_, out, err) = fixpt(&dir, &["run", "other.fx", "prog.fx"], &[]);
    assert!(err.contains("`prog.fasl` is stale (`twice` uses `scale`, which is not here at the type it was)"), "{out}{err}");
}

/// A program's `.fasl`'s image is linked before its definitions run, each
/// global its code names made ahead (`Fx26Session::splice_program`): one
/// defined again since, so not the one code after was linked to, has those
/// definitions run from their source, which give what they give without.
#[test]
fn a_program_fasl_linked_to_a_global_defined_again_runs_its_source() {
    let dir = scratch("again");
    // `x` at another type: at a new global, which `get2`'s code is linked to.
    std::fs::write(dir.join("p.fx"), include_str!("programs/defined-again.fx")).expect("written");
    let (ok, out, err) = fixpt(&dir, &["compile-file", "--program", "p.fx"], &[]);
    assert!(ok, "{out}{err}");
    let (_, out, err) = fixpt(&dir, &["eval", "p.fx"], &[("FIXPT_NO_FASL", "1")]);
    let (_, fout, ferr) = fixpt(&dir, &["eval", "p.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ferr.contains("`p.fx` is read from `p.fasl`") && ferr.contains("is defined again: `get2` and the definitions after are run from their source"), "{fout}{ferr}");
    assert!(out.contains("7 : int"), "{out}{err}");
    assert_eq!(out, fout, "{err}{ferr}");
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

/// A maker's interface names its parameters' types as its source did,
/// though a type written out the same comes first: its recursive types
/// minimized where they are printed, a name of one's own is not merged.
#[test]
fn a_maker_keeps_its_parameters_types_named() {
    let dir = scratch("named");
    std::fs::write(dir.join("a.fx"), "(module-parameters ())\n(define-type ints (listof int acyclic))\n(define none ints nil)\n").expect("written");
    std::fs::write(
        dir.join("b.fx"),
        "(module-parameters ((m-a (load-moduleof \"a.fx\"))))\n(define both (subr pure ((listof int acyclic) (select m-a ints)) (select m-a ints)) (lambda (x y) y))\n",
    )
    .expect("written");
    let (ok, out, err) = fixpt(&dir, &["compile-file", "a.fx", "b.fx"], &[]);
    assert!(ok, "{out}{err}");
    let fasl = String::from_utf8_lossy(&std::fs::read(dir.join("b.fasl")).expect("read")).to_string();
    let made = fasl.lines().find(|l| l.starts_with("made ")).expect("a maker's");
    assert!(made.contains("(subr pure ((listof int acyclic) (select m-a ints)) (select m-a ints))"), "{made}");
}

#[test]
fn a_description_function_reads_back_from_a_fasl_read_from_one() {
    // `u.fx` compiled with `t.fx` read from its `.fasl`: `tt`'s `bucket` in
    // `u`'s type is the `dlambda` it is, not the name of `t`'s, which does
    // not stand bare.
    let dir = scratch("dlambda");
    std::fs::write(dir.join("tt.fx"), "(define-type (bucket (k type)) (listof k acyclic))\n(define none (poly ((k type)) (bucket k)) nil)\n").expect("written");
    std::fs::write(dir.join("t.fx"), "(define tt (load-module \"tt.fx\"))\n(import tt (type bucket))\n(define ints (bucket int) nil)\n").expect("written");
    std::fs::write(dir.join("u.fx"), "(define t (load-module \"t.fx\"))\n(define n int 2)\n").expect("written");
    std::fs::write(dir.join("p.fx"), "(define u (load-module \"u.fx\"))\n1\n").expect("written");
    let (ok, out, err) = fixpt(&dir, &["compile-file", "tt.fx", "t.fx"], &[]);
    assert!(ok, "{out}{err}");
    let (ok, out, err) = fixpt(&dir, &["compile-file", "u.fx"], &[]);
    assert!(ok, "{out}{err}");
    let (ok, out, err) = fixpt(&dir, &["run", "p.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ok && err.contains("`u.fx` is read from `u.fasl`") && !err.contains("stale"), "{out}{err}");
}

#[test]
fn a_built_in_module_is_kept_in_the_cache() {
    // A built-in has no directory of its own: its `.fasl` is made in the
    // cache directory by the run that loads it, quietly, and read by the
    // next.
    let dir = scratch("built-in");
    let cache = dir.join("cache");
    std::fs::write(dir.join("p.fx"), "(define t (load-module \"fx26:table.fx\"))\n1\n").expect("written");
    let envs = [("XDG_CACHE_HOME", cache.to_str().expect("a path"))];
    let (ok, out, err) = fixpt(&dir, &["run", "p.fx"], &envs);
    assert!(ok && err.is_empty(), "{out}{err}");
    let (ok, out, err) = fixpt(&dir, &["run", "p.fx"], &[envs[0], ("FIXPT_FASL_SAY", "1")]);
    assert!(ok, "{out}{err}");
    assert!(err.contains("`fx26:table.fx` is read from") && err.contains("table.fasl"), "{err}");
}

#[test]
fn a_fasl_keeps_native_code_or_with_cellular_its_words_alone() {
    // Either way the module runs as from its source: its native code kept,
    // or (`--cellular`) its cellular words, compiled natively at load.
    let dir = scratch("cellular");
    std::fs::write(
        dir.join("m.fx"),
        "(define twice (subr pure ((subr pure (int) int) int) int) (lambda (f x) (f (f x))))\n\
         (define add3 (subr pure (int) int) (lambda (x) (+ x 3)))\n\
         (define go (subr pure (int) int) (lambda (n) (twice add3 n)))\n",
    )
    .expect("written");
    std::fs::write(dir.join("p.fx"), "(define m (load-module \"m.fx\"))\n(with m (go 10))\n").expect("written");
    for (flags, code) in [(&[][..], "code native"), (&["--cellular"][..], "code cellular")] {
        let args: Vec<&str> = ["compile-file"].iter().chain(flags).chain(&["m.fx"]).copied().collect();
        let (ok, out, err) = fixpt(&dir, &args, &[]);
        assert!(ok, "{out}{err}");
        let fasl = String::from_utf8_lossy(&std::fs::read(dir.join("m.fasl")).expect("read")).to_string();
        assert!(fasl.lines().any(|l| l == code), "{code}");
        let (ok, out, err) = fixpt(&dir, &["eval", "p.fx"], &[("FIXPT_FASL_SAY", "1")]);
        assert!(ok && err.contains("`m.fx` is read from `m.fasl`") && out.contains("16 : int"), "{out}{err}");
    }
}

#[test]
fn a_definition_changed_at_the_same_type_is_seen_through_a_fasl() {
    // `b.fx`'s `.fasl` is fresh after `a.fx`'s `scale` changes but keeps its
    // type: what its code assumed of `scale` is guarded by the definition's
    // stamp, which changed, so the new one is called (2 · 2 · 5 was 20).
    let dir = scratch("stamps");
    std::fs::write(dir.join("b.fx"), "(define twice (subr (read (globals scale)) (int) int) (lambda (x) (scale (scale x))))\n").expect("written");
    std::fs::write(
        dir.join("c.fx"),
        "(define main (subr (maxeff (io stdout) (read (globals twice scale))) () unit) (lambda () (begin (write-out (int->string (twice 5))) #u)))\n",
    )
    .expect("written");
    for flags in [&[][..], &["--cellular"][..]] {
        std::fs::write(dir.join("a.fx"), "(define scale (subr pure (int) int) (lambda (x) (* 2 x)))\n").expect("written");
        let args: Vec<&str> = ["compile-file", "--program"].iter().chain(flags).chain(&["a.fx", "b.fx"]).copied().collect();
        let (ok, out, err) = fixpt(&dir, &args, &[]);
        assert!(ok, "{out}{err}");
        std::fs::write(dir.join("a.fx"), "(define scale (subr pure (int) int) (lambda (x) (* 3 x)))\n").expect("written");
        let (ok, out, err) = fixpt(&dir, &["run", "a.fx", "b.fx", "c.fx"], &[("FIXPT_FASL_SAY", "1")]);
        assert!(ok && err.contains("`b.fx` is read from `b.fasl`") && out == "45", "{flags:?}: {out}{err}");
    }
}
