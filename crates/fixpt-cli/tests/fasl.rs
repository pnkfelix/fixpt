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
                    // Verified: its definitions checked by their text, and
                    // the stamps it keeps the ones a run from source makes
                    // (`FIXPT_FASL_VERIFY`, `heap-types.md`, step 5).
                    let (_, vout, verr) = fixpt(&dir, &["eval", &name], &[("FIXPT_FASL_VERIFY", "1")]);
                    if (out.as_str(), err.as_str()) != (vout.as_str(), verr.as_str()) {
                        wrong.push(format!("{name}:\n  from sources:        {out}{err}\n  from fasls, verified: {vout}{verr}"));
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

/// A program's `.fasl` keeps its definitions' types as one rep, what they
/// share there once (an abbreviation's type, here), each definition its
/// place in it and what its stamp is made of; loaded, they are entered by
/// it, and verified, as a run from source enters them
/// (`docs/research/heap-types.md`, step 5).
#[test]
fn a_program_fasl_keeps_its_types_as_one_rep() {
    let dir = scratch("reps");
    let prog = concat!(
        "(define-type pt (productof (x int) (y int)))\n",
        "(define* get-x (subr pure (pt) int) (lambda (p) (extract p x)))\n",
        "(define* get-y (subr pure (pt) int) (lambda (p) (extract p y)))\n",
        "(define-rec (ev? (subr (maxeff spin (read (globals ev? od?))) (int) bool) (lambda (n) (if (= n 0) #t (od? (- n 1)))))\n",
        "            (od? (subr (maxeff spin (read (globals ev? od?))) (int) bool) (lambda (n) (if (= n 0) #f (ev? (- n 1))))))\n",
        "(define same (poly ((t type)) (subr pure (t) t)) (plambda ((t type)) (lambda (v) v)))\n",
        "(write-out (int->string (+ (get-x (product (x 1) (y 2))) ((proj same int) (get-y (product (x 3) (y 4)))))))\n",
        "(write-out (if (ev? 10) \" even\\n\" \" odd\\n\"))\n",
    );
    std::fs::write(dir.join("prog.fx"), prog).expect("written");
    let (ok, out, err) = fixpt(&dir, &["compile-file", "--program", "prog.fx"], &[]);
    assert!(ok, "{out}{err}");
    let fasl = std::fs::read(dir.join("prog.fasl")).expect("made");
    let header = String::from_utf8_lossy(&fasl[..fasl.windows(7).position(|w| w == b"\nimage ").expect("an image")]).into_owned();
    let count = |w: &str| header.lines().filter(|l| l.starts_with(w)).count();
    assert_eq!((count("reps "), count("repof "), count("stampof ")), (1, 5, 5), "{header}");
    for envs in [&[("FIXPT_FASL_SAY", "1")][..], &[("FIXPT_FASL_SAY", "1"), ("FIXPT_FASL_VERIFY", "1")][..]] {
        let (ok, out, err) = fixpt(&dir, &["eval", "prog.fx"], envs);
        // The abbreviation named as a run from source names it.
        let named = out.contains("get-x : (subr pure (pt) int)") && out.contains("same : (poly ((t type)) (subr pure (t) t))");
        assert!(ok && out.starts_with("5 even\n") && named && err.contains("`prog.fx` is read from `prog.fasl`"), "{envs:?}: {out}{err}");
    }
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

/// An abbreviation a program's `.fasl` names, compared by its type's digest
/// first (`Checker::fasl_alias_is`): one defined otherwise where it is
/// loaded makes it stale.
#[test]
fn a_program_fasl_is_stale_when_an_abbreviation_it_names_changed() {
    let dir = scratch("alias");
    std::fs::write(dir.join("base.fx"), "(define-type pt (productof (x int) (y int)))\n").expect("written");
    std::fs::write(dir.join("other.fx"), "(define-type pt (productof (x int) (y bool)))\n").expect("written");
    std::fs::write(dir.join("prog.fx"), "(define* get-x (subr pure (pt) int) (lambda (p) (extract p x)))\n(write-out \"ran\\n\")\n").expect("written");
    std::fs::write(dir.join("make.fx"), "(compile-file \"prog.fx\" program)\n").expect("written");
    let (ok, out, err) = fixpt(&dir, &["run", "base.fx", "make.fx"], &[]);
    assert!(ok && out.contains("; compiled `prog.fx` to `"), "{out}{err}");
    let (ok, out, err) = fixpt(&dir, &["run", "base.fx", "prog.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ok && out == "ran\n" && err.contains("`prog.fx` is read from `prog.fasl`"), "{out}{err}");
    let (ok, out, err) = fixpt(&dir, &["run", "other.fx", "prog.fx"], &[]);
    assert!(ok && out == "ran\n" && err.contains("`prog.fasl` is stale (the type `pt` is not what it was)"), "{out}{err}");
}

/// A use's type compared by its digest first (`Checker::fasl_use_digest`):
/// an abstract type by the `select` that names it, so that one of another
/// module of the same name is not taken for it.
#[test]
fn a_program_fasl_tells_apart_abstract_types_of_the_same_name() {
    let dir = scratch("selects");
    // Two files of the same name, whose abstract types are named alike.
    let module = "(define-generative t int #:seal up-t #:unseal down-t)\n(define zero t (up-t 0))\n(define value (subr pure (t) int) (lambda (v) (down-t v)))\n";
    for m in ["a", "c"] {
        std::fs::create_dir_all(dir.join(m)).expect("made");
        std::fs::write(dir.join(format!("{m}/m.fx")), module).expect("written");
    }
    let base = |m: &str| format!("(define a (load-module \"a/m.fx\"))\n(define c (load-module \"c/m.fx\"))\n(define use-t (subr pure ((select {m} t)) int) (lambda (v) 0))\n");
    std::fs::write(dir.join("base-a.fx"), base("a")).expect("written");
    std::fs::write(dir.join("base-c.fx"), base("c")).expect("written");
    std::fs::write(dir.join("prog.fx"), "(define* get (subr (read (globals use-t a c)) () int) (lambda () (use-t (with a zero))))\n(write-out \"ran\\n\")\n").expect("written");
    std::fs::write(dir.join("make.fx"), "(compile-file \"prog.fx\" program)\n").expect("written");
    let (ok, out, err) = fixpt(&dir, &["run", "base-a.fx", "make.fx"], &[]);
    assert!(ok && out.contains("; compiled `prog.fx` to `"), "{out}{err}");
    let (ok, out, err) = fixpt(&dir, &["run", "base-a.fx", "prog.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ok && out == "ran\n" && err.contains("`prog.fx` is read from `prog.fasl`"), "{out}{err}");
    // `use-t` of `c`'s `t`, named as `a`'s is, but another type: only
    // that differs (its effect is the same, as its body reads neither).
    let (_, out, err) = fixpt(&dir, &["run", "base-c.fx", "prog.fx"], &[]);
    assert!(err.contains("`prog.fasl` is stale"), "{out}{err}");
}

/// A region made up has one name whether its file is checked from source
/// or a `.fasl` kept its type (TODO §305): `dep.fx`'s `g` allocates at one,
/// and `user.fx`'s `peek`, which calls `g`, says so. `user.fx` read from
/// its `.fasl` and `dep.fx` from source, the two were one name, uninterned
/// in `g`'s type and interned in `peek`'s, and so two regions, taken not
/// to overlap (`regions_distinct`), each atom of the effect said twice;
/// and the name was a session's count, another in each.
#[test]
fn a_region_made_up_is_one_from_source_or_a_fasl() {
    let dir = scratch("made-up");
    std::fs::write(dir.join("other.fx"), "(define o (lambda () (get (new #t))))\n(define o2 (lambda () (product (#:c (new 1)))))\n").expect("written");
    std::fs::write(dir.join("dep.fx"), "(define f (lambda () (get (new 5))))\n(define g (lambda () (product (#:c (new 5)))))\n").expect("written");
    std::fs::write(dir.join("user.fx"), "(define d (load-module \"dep.fx\"))\n(define peek (lambda () (with d (get (extract (g) #:c)))))\n").expect("written");
    let main = "(define x (load-module \"other.fx\"))\n(define u (load-module \"user.fx\"))\n(define d (load-module \"dep.fx\"))\n(+ (with u (peek)) (with d (get (extract (g) #:c))))\n";
    std::fs::write(dir.join("main.fx"), main).expect("written");
    let (_, out, err) = fixpt(&dir, &["eval", "main.fx"], &[("FIXPT_NO_FASL", "1")]);
    assert!(out.contains("10 : int ! (maxeff (read @r.%shared:dep.fx.2) (alloc @r.%shared:dep.fx.2) (read (globals d u)))"), "{out}{err}");
    for f in ["other.fx", "dep.fx", "user.fx"] {
        let (ok, fout, ferr) = fixpt(&dir, &["compile-file", f], &[]);
        assert!(ok, "{fout}{ferr}");
    }
    let (_, fout, ferr) = fixpt(&dir, &["eval", "main.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ferr.contains("`user.fx` is read from `user.fasl`") && ferr.contains("`dep.fx` is read from `dep.fasl`"), "{fout}{ferr}");
    assert_eq!(out, fout, "{err}{ferr}");
    std::fs::remove_file(dir.join("dep.fasl")).expect("removed");
    let (_, fout, ferr) = fixpt(&dir, &["eval", "main.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ferr.contains("`user.fx` is read from `user.fasl`") && !ferr.contains("`dep.fx` is read"), "{fout}{ferr}");
    assert_eq!(out, fout, "{err}{ferr}");
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

/// A keyword a module's `.fasl` holds is the loader's keyword of that
/// name (`fasl::Link::Keyword`), spliced or copied in: one object for each
/// name, as from source.
#[test]
fn a_fasls_keywords_are_the_loaders() {
    let dir = scratch("keywords");
    std::fs::write(dir.join("k.fx"), "(define k #:shared)\n").expect("written");
    std::fs::write(dir.join("main.fx"), "(define m (load-module \"k.fx\"))\n(eq? (with m k) #:shared)\n").expect("written");
    let (ok, out, err) = fixpt(&dir, &["compile-file", "k.fx"], &[]);
    assert!(ok, "{out}{err}");
    for envs in [&[("FIXPT_FASL_SAY", "1")][..], &[("FIXPT_FASL_SAY", "1"), ("FIXPT_IMAGE_COPY", "1")][..]] {
        let (ok, out, err) = fixpt(&dir, &["eval", "main.fx"], envs);
        assert!(ok && err.contains("`k.fx` is read from `k.fasl`") && out.contains("#t : bool"), "{envs:?}: {out}{err}");
    }
}

/// A `utf8` a module's `.fasl` holds (`#utf8"…"`, `TODO.md` §306), and a
/// bytevector (`#u8"…"`), each as a global's value and as a constant in its
/// code, is the text or bytes written,
/// read from the `.fasl` as from its source, its image copied or not.
#[test]
fn a_fasls_utf8_text_is_as_written() {
    let dir = scratch("utf8");
    let u = "(define u #utf8\"a\\xE9;z\")\n(define f (subr pure () utf8) (lambda () #utf8\"in code\"))\n\
             (define b #u8\"by\\xFF;\")\n(define g (subr pure () bytevector) (lambda () #u8\"\\x01;in code\"))\n";
    std::fs::write(dir.join("u.fx"), u).expect("written");
    let main = "(define m (load-module \"u.fx\"))\n(list (utf8-length (with m u)) (utf8-byte-length (with m u)))\n(utf8=? ((with m f)) #utf8\"in code\")\n\
                (cons (with m u) (cons (with m b) ((with m g))))\n";
    std::fs::write(dir.join("main.fx"), main).expect("written");
    let (ok, out, err) = fixpt(&dir, &["eval", "main.fx"], &[]);
    let values = |out: &str| out.contains("(3 4) :") && out.contains("#t : bool") && out.contains("(#utf8\"aéz\" #u8(98 121 255) . #u8(1 105 110 32 99 111 100 101)) :");
    assert!(ok && values(&out), "{out}{err}");
    let (ok, out, err) = fixpt(&dir, &["compile-file", "u.fx"], &[]);
    assert!(ok, "{out}{err}");
    for envs in [&[("FIXPT_FASL_SAY", "1")][..], &[("FIXPT_FASL_SAY", "1"), ("FIXPT_IMAGE_COPY", "1")][..]] {
        let (ok, out, err) = fixpt(&dir, &["eval", "main.fx"], envs);
        assert!(ok && err.contains("`u.fx` is read from `u.fasl`"), "{envs:?}: {out}{err}");
        assert!(values(&out), "{envs:?}: {out}{err}");
    }
}

/// A small library: `a.fx`, and `b.fx`, which loads it, and a program of
/// both.
fn library(dir: &Path) {
    std::fs::create_dir_all(dir.join("lib")).expect("made");
    std::fs::write(dir.join("lib/a.fx"), "(define-generative t int #:seal up-t #:unseal down-t)\n(define zero t (up-t 0))\n(define value (subr pure (t) int) (lambda (v) (down-t v)))\n").expect("written");
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
    std::fs::write(dir.join("lib/a.fx"), "(define-generative t int #:seal up-t #:unseal down-t)\n(define zero t (up-t 1))\n(define value (subr pure (t) int) (lambda (v) (down-t v)))\n").expect("written");
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
        "(module-parameters ((m-a (load-moduleof \"a.fx\") #:qualified)))\n(define both (subr pure ((listof int acyclic) (select m-a ints)) (select m-a ints)) (lambda (x y) y))\n",
    )
    .expect("written");
    let (ok, out, err) = fixpt(&dir, &["compile-file", "a.fx", "b.fx"], &[]);
    assert!(ok, "{out}{err}");
    let fasl = String::from_utf8_lossy(&std::fs::read(dir.join("b.fasl")).expect("read")).to_string();
    let made = fasl.lines().find(|l| l.starts_with("made ")).expect("a maker's");
    assert!(made.contains("(subr pure ((listof int acyclic) (select m-a ints)) (select m-a ints))"), "{made}");
}

/// A file's `.fasl` keeps its maker and its loads whatever the same
/// `compile-file` compiled before it (Heist's report, TODO §294):
/// `together-b.fx`'s maker kept, its type not written out whole, though
/// `together-a.fx`, compiled first, has a macro `loop` that
/// `together-b.fx`'s own macro binds as a name; and its loads its own,
/// whether `together-a.fx` was read from source or from its `.fasl`.
#[test]
fn a_fasl_keeps_its_maker_whatever_was_compiled_before_it() {
    let top = scratch("together");
    copy_dirs(&top, &["module-files"]);
    let dir = top.join("module-files");
    let (ok, out, err) = fixpt(&dir, &["compile-file", "together-c.fx"], &[]);
    assert!(ok, "{out}{err}");
    // Its header: what it says of its type and maker.
    let header = || -> Vec<String> {
        let fasl = String::from_utf8_lossy(&std::fs::read(dir.join("together-b.fasl")).expect("read")).to_string();
        fasl.lines().filter(|l| ["dep ", "type ", "made "].iter().any(|k| l.starts_with(k))).map(str::to_string).collect()
    };
    let (ok, out, err) = fixpt(&dir, &["compile-file", "together-a.fx", "together-b.fx"], &[]);
    assert!(ok, "{out}{err}");
    let together = header();
    assert!(together.iter().any(|l| l.starts_with("made (")), "{together:?}");
    assert!(together.iter().any(|l| l == "type "), "{together:?}");
    std::fs::remove_file(dir.join("together-b.fasl")).expect("removed");
    let (ok, out, err) = fixpt(&dir, &["compile-file", "together-b.fx"], &[]);
    assert!(ok, "{out}{err}");
    assert_eq!(header(), together);
}

/// A type that names a load's load (`layer3.fx`'s names `layer1.fx`'s,
/// which `layer2.fx` loads) names it by its route, `%fasl-dep:0.0`, never
/// by its key where it was compiled (TODO §294): `layer3.fasl` the same
/// compiled alone or after the files it loads, and the program that loads
/// it, read from it, the same.
#[test]
fn a_load_of_a_load_is_named_by_its_route() {
    let top = scratch("routes");
    copy_dirs(&top, &["module-files", "modules"]);
    let dir = top.join("module-files");
    let header = || -> Vec<String> {
        let fasl = String::from_utf8_lossy(&std::fs::read(dir.join("layer3.fasl")).expect("read")).to_string();
        fasl.lines().filter(|l| ["dep ", "type ", "made "].iter().any(|k| l.starts_with(k))).map(str::to_string).collect()
    };
    let (ok, out, err) = fixpt(&dir, &["compile-file", "layer3.fx"], &[]);
    assert!(ok, "{out}{err}");
    let alone = header();
    assert!(alone.iter().any(|l| l.starts_with("type ") && l.contains("%fasl-dep:0.0")), "{alone:?}");
    assert!(!alone.iter().any(|l| l.contains("%shared:")), "{alone:?}");
    for f in ["layer3.fasl"] {
        std::fs::remove_file(dir.join(f)).expect("removed");
    }
    let (ok, out, err) = fixpt(&dir, &["compile-file", "layer1.fx", "layer2.fx", "layer3.fx"], &[]);
    assert!(ok, "{out}{err}");
    assert_eq!(header(), alone);
    let (ok, out, err) = fixpt(&top.join("modules"), &["eval", "load-layers.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ok && out.lines().last().is_some_and(|l| l.starts_with("6 : int")) && err.contains("is read from") && !err.contains("stale"), "{out}{err}");
}

/// A chain of module files, each taking those before it as module
/// parameters and importing a file's macros (Heist's report, 2026-11-18):
/// compiled in time about its length, not doubling with each file. The
/// parser written in FX-26 was handed the forms of each file made before,
/// for a file that imports macros, again at each file that loads it: 10
/// files took 2.6 s, each two more twice as long; 18 now under a second in
/// a release build.
#[test]
fn a_parameter_chain_importing_macros_compiles_in_its_length() {
    let dir = scratch("chain");
    let n = 18;
    std::fs::write(dir.join("macros.fx"), "(define-syntax twice (macro (_ expr) expr) (syntax-rules ((_ e) (let ((x e)) (+ x x)))))\n").expect("written");
    for k in 0..=n {
        let params: Vec<String> = (0..k).map(|i| format!("(m{i} (load-moduleof \"f{i}.fx\"{}) #:unqualified)", (0..i).map(|j| format!(" m{j}")).collect::<String>())).collect();
        let text = format!("(module-parameters ({}))\n(define mac{k} (load-module \"macros.fx\"))\n(import-with-syntax mac{k})\n(define v{k} int (twice {k}))\n", params.join(" "));
        std::fs::write(dir.join(format!("f{k}.fx")), text).expect("written");
    }
    let start = std::time::Instant::now();
    let (ok, out, err) = fixpt(&dir, &["compile-file", &format!("f{n}.fx")], &[]);
    assert!(ok, "{out}{err}");
    let took = start.elapsed();
    assert!(took < std::time::Duration::from_secs(60), "{n} files took {took:?}");
}

/// A `.fasl` that says it makes a load it cannot make from its directory
/// (as a bug wrote one, its loads another file's spelling, Heist's report,
/// 2026-11-18) is not as a build left it: its load refused, saying so and
/// what to do (the user's, 2026-11-18: a suspicious one an error), not a
/// file it cannot read; or, `FIXPT_STALE_FASL=source`, stale, its file read
/// from source.
#[test]
fn a_fasl_whose_load_cannot_be_made_is_refused() {
    let dir = scratch("bad-load");
    let (kit, editor) = (dir.join("kit"), dir.join("editor"));
    std::fs::create_dir_all(&kit).expect("made");
    std::fs::create_dir_all(&editor).expect("made");
    std::fs::write(kit.join("lists.fx"), "(define four int 4)\n").expect("written");
    std::fs::write(editor.join("buffer.fx"), "(define lists (load-module \"../kit/lists.fx\"))\n(define eight int (* 2 (with lists four)))\n").expect("written");
    std::fs::write(editor.join("main.fx"), "(define buffer (load-module \"buffer.fx\"))\n(with buffer eight)\n").expect("written");
    let (ok, out, err) = fixpt(&editor, &["compile-file", "buffer.fx"], &[]);
    assert!(ok, "{out}{err}");
    // A load in another file's spelling, as the bug wrote one.
    let fasl = editor.join("buffer.fasl");
    let mut bytes = std::fs::read(&fasl).expect("read");
    let at = bytes.windows(4).position(|w| w == b"dep ").expect("a load");
    bytes.splice(at..at, b"dep module 0000000000000001 macros.fx\n".iter().copied());
    std::fs::write(&fasl, bytes).expect("written");
    let (ok, out, err) = fixpt(&editor, &["eval", "main.fx"], &[]);
    assert!(!ok && err.contains("`buffer.fasl` is not as a build left it (a load it makes cannot be made here") && err.contains("FIXPT_STALE_FASL=source"), "{out}{err}");
    let (ok, out, err) = fixpt(&editor, &["eval", "main.fx"], &[("FIXPT_STALE_FASL", "source")]);
    assert!(ok && out.lines().last().is_some_and(|l| l.starts_with("8 : int")), "{out}{err}");
    assert!(err.contains("`buffer.fasl` is stale (a load it makes cannot be made here"), "{err}");
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

/// The cache directory `cache` (an `XDG_CACHE_HOME`) given the front end's
/// kept files from this user's, linked (else copied), where there are any:
/// a test of what else is kept there then waits on no front end made anew,
/// a minute in a debug build. Each is keyed by its build, so another's is
/// never read; and the cache replaces a file, never writes into one, so
/// the link is never changed through.
fn seed_front_end(cache: &std::path::Path) {
    let home = std::env::var_os("XDG_CACHE_HOME").map(std::path::PathBuf::from).or_else(|| std::env::var_os("HOME").map(|h| std::path::Path::new(&h).join(".cache")));
    let Some(kept) = home.map(|h| h.join("fixpt")) else { return };
    let to = cache.join("fixpt");
    std::fs::create_dir_all(&to).expect("the cache's directory");
    for e in std::fs::read_dir(&kept).into_iter().flatten().flatten() {
        if e.file_name().to_string_lossy().starts_with("front-end-") {
            let at = to.join(e.file_name());
            if std::fs::hard_link(e.path(), &at).is_err() {
                let _ = std::fs::copy(e.path(), &at);
            }
        }
    }
}

#[test]
fn a_built_in_module_is_kept_in_the_cache() {
    // A built-in has no directory of its own: its `.fasl` is made in the
    // cache directory by the run that loads it, quietly, and read by the
    // next.
    let dir = scratch("built-in");
    let cache = dir.join("cache");
    seed_front_end(&cache);
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

/// A type read from a `.fasl`'s rep is the standard environment's own where
/// it is a base type, so that a `nat` is an `int` of one (Heist's report,
/// `fixpt-nat-int-from-fasl.md`): a form the `.fasl` keeps as its source
/// (`g`, defined twice), and a file run from source after it.
#[test]
fn a_nat_is_an_int_of_a_type_read_from_a_fasl() {
    let dir = scratch("nat-int");
    let f = "(define f (subr pure (int) int) (lambda (n) (+ n 1)))\n";
    let g = "(define g (subr (maxeff (read @globals) spin) () int) (lambda () (f (length (list 1 2 3)))))\n";
    let first = "(define g (subr (maxeff (read @globals) spin) () int) (lambda () 0))\n";
    std::fs::write(dir.join("a.fx"), format!("{f}{first}{g}(g)\n")).expect("written");
    std::fs::write(dir.join("f.fx"), f).expect("written");
    std::fs::write(dir.join("g.fx"), format!("{g}(write-out (int->string (g)))\n")).expect("written");
    for file in ["a.fx", "f.fx"] {
        let (ok, out, err) = fixpt(&dir, &["compile-file", "--program", file], &[]);
        assert!(ok, "{file}: {out}{err}");
    }
    let (ok, out, err) = fixpt(&dir, &["eval", "a.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ok && err.contains("`a.fx` is read from `a.fasl`") && out.contains("4 : int"), "{out}{err}");
    let (ok, out, err) = fixpt(&dir, &["run", "f.fx", "g.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ok && err.contains("`f.fx` is read from `f.fasl`") && out == "4", "{out}{err}");
}

/// A load's procedures that a client includes are linked in the client's
/// `.fasl`, not copied (TODO §304, Heist's should-work note, entry 22: a
/// two-line client of `sat.fx` 909,039 bytes): `fasl::dep_parts`. The
/// client's defines its own alone, and its procedures and the load's,
/// both read from their `.fasl`s, are one counter's: 2, then 3.
#[test]
fn a_clients_fasl_links_what_it_includes() {
    let dir = scratch("include");
    for f in ["counter.fx", "client.fx", "drive.fx"] {
        let from = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs/fasl-include").join(f);
        std::fs::copy(&from, dir.join(f)).expect("copied");
    }
    let (ok, out, err) = fixpt(&dir, &["compile-file", "counter.fx", "client.fx"], &[]);
    assert!(ok, "{out}{err}");
    let client = std::fs::read(dir.join("client.fasl")).expect("compiled");
    let copied = String::from_utf8_lossy(&client).matches("define %shared:counter.fx/").count();
    assert_eq!(copied, 0, "the client's `.fasl` copies the load's procedures");
    let (ok, out, err) = fixpt(&dir, &["eval", "--raw", "drive.fx"], &[("FIXPT_FASL_SAY", "1")]);
    assert!(ok && out.trim() == "23", "{out}{err}");
    assert_eq!(err.lines().filter(|l| l.contains("is read from")).count(), 2, "{err}");
}
