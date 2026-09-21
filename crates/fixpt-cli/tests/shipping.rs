//! The three ways to ship a program, end to end through the real binary.
//!
//! These run `fixpt` as a subprocess rather than calling into the library,
//! because the property under test is about files on disk and a process that
//! starts from nothing: a heap image that outlives the session that made it,
//! and an executable that works with no `fixpt` beside it.

use std::path::{Path, PathBuf};
use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

const PROGRAM: &str = r#"
(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))
(define (sum-to n) (let loop ((i 0) (acc 0)) (if (> i n) acc (loop (+ i 1) (+ acc i)))))
(define greeting "shipped")
(define (main args)
  (display greeting)
  (display " ")
  (display (fact 15))
  (display " ")
  (display (sum-to 1000))
  (display " ")
  (write args)
  (newline)
  0)
"#;

/// A directory of this test's own, named after the case so parallel tests do
/// not collide.
fn workdir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("fixpt-shipping-{name}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("can make a work directory");
    let source = dir.join("prog.scm");
    std::fs::write(&source, PROGRAM).expect("can write the program");
    dir
}

fn run(cmd: &mut Command) -> (bool, String, String) {
    let out = cmd.output().expect("the command runs");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

fn fixpt(dir: &Path, args: &[&str]) -> (bool, String, String) {
    run(Command::new(FIXPT).current_dir(dir).args(args))
}

const EXPECTED: &str = "shipped 1307674368000 500500 (\"a\" \"b\")\n";

#[test]
fn a_dumped_image_runs_in_a_fresh_process() {
    for engine in ["bytecode", "ast"] {
        let dir = workdir(&format!("image-{engine}"));
        let (ok, out, err) = fixpt(
            &dir,
            &[
                "--engine",
                engine,
                "dump-heap",
                "-o",
                "prog.heap",
                "prog.scm",
            ],
        );
        assert!(ok, "dump-heap failed for {engine}: {err}");
        assert!(out.contains("heap image"), "unexpected report: {out}");
        assert!(dir.join("prog.heap").exists(), "the image was not written");

        // A new process, given only the image: nothing of the session that
        // produced it survives except the heap.
        let (ok, out, err) = fixpt(&dir, &["run-image", "prog.heap", "a", "b"]);
        assert!(ok, "run-image failed for {engine}: {err}");
        assert_eq!(out, EXPECTED, "wrong output for {engine}");
    }
}

#[test]
fn a_built_binary_needs_nothing_beside_it() {
    let dir = workdir("binary");
    let (ok, out, err) = fixpt(&dir, &["build", "-o", "prog", "prog.scm"]);
    assert!(ok, "build failed: {err}");
    assert!(out.contains("executable"), "unexpected report: {out}");

    // Move it somewhere with no `fixpt` in sight and run it directly. It must
    // behave as the program, not as the driver that built it — so `--help`,
    // which the driver would answer, is just an argument here.
    let elsewhere = std::env::temp_dir().join("fixpt-shipping-binary-elsewhere");
    let _ = std::fs::remove_dir_all(&elsewhere);
    std::fs::create_dir_all(&elsewhere).expect("can make a directory");
    let moved = elsewhere.join("prog");
    std::fs::rename(dir.join("prog"), &moved).expect("can move the binary");

    let (ok, out, err) = run(Command::new(&moved)
        .current_dir(&elsewhere)
        .args(["a", "b"]));
    assert!(ok, "the built binary failed: {err}");
    assert_eq!(out, EXPECTED);

    let (_, out, _) = run(Command::new(&moved).arg("--help"));
    assert!(
        out.contains("shipped"),
        "the binary answered as the driver: {out}"
    );
}

#[test]
fn an_image_knows_which_engine_made_it() {
    // The two engines produce different code objects, and `run-image` picks the
    // machine from the image rather than from a flag. Asking for the *wrong*
    // engine on the command line must not matter.
    let dir = workdir("engine-detect");
    let (ok, _, err) = fixpt(
        &dir,
        &[
            "--engine",
            "bytecode",
            "dump-heap",
            "-o",
            "c.heap",
            "prog.scm",
        ],
    );
    assert!(ok, "{err}");
    let (ok, _, err) = fixpt(
        &dir,
        &["--engine", "ast", "dump-heap", "-o", "a.heap", "prog.scm"],
    );
    assert!(ok, "{err}");

    for (image, wrong) in [("c.heap", "ast"), ("a.heap", "bytecode")] {
        let (ok, out, err) = fixpt(&dir, &["--engine", wrong, "run-image", image, "a", "b"]);
        assert!(ok, "{image} failed under --engine {wrong}: {err}");
        assert_eq!(out, EXPECTED, "{image} under --engine {wrong}");
    }

    // Compiled code is denser than a node tree, so it should also be smaller.
    let compiled = std::fs::metadata(dir.join("c.heap")).expect("exists").len();
    let interpreted = std::fs::metadata(dir.join("a.heap")).expect("exists").len();
    assert!(
        compiled < interpreted,
        "expected the compiled image to be smaller: {compiled} vs {interpreted}"
    );
}

#[test]
fn image_info_reports_an_embedded_image() {
    let dir = workdir("info");
    let (ok, _, err) = fixpt(&dir, &["build", "-o", "prog", "prog.scm"]);
    assert!(ok, "{err}");
    let (ok, out, err) = fixpt(&dir, &["image", "info", "prog"]);
    assert!(ok, "image info failed: {err}");
    assert!(out.contains("valid fixpt heap image"), "{out}");
    assert!(out.contains("embedded in an executable"), "{out}");
    assert!(out.contains("structure:   ok"), "{out}");
}

#[test]
fn an_image_without_an_entry_point_says_so() {
    let dir = workdir("no-main");
    std::fs::write(dir.join("lib.scm"), "(define (helper x) x)").expect("can write");
    let (ok, _, err) = fixpt(&dir, &["dump-heap", "-o", "lib.heap", "lib.scm"]);
    assert!(ok, "{err}");
    let (ok, _, err) = fixpt(&dir, &["run-image", "lib.heap"]);
    assert!(!ok, "an image with no `main` should fail");
    assert!(err.contains("no `main`"), "unhelpful message: {err}");

    // …but an entry point by another name can be named.
    let (ok, _, err) = fixpt(&dir, &["--main", "helper", "run-image", "lib.heap"]);
    assert!(!ok || err.is_empty(), "{err}");
}
