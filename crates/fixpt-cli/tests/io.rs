//! FX-26's I/O (`TODO.md` §84), as `fixpt run` performs it: what a program
//! writes to its standard output and error, and the status it ends with,
//! the same on every kind of machine (`programs/io/`).

use std::process::{Command, Stdio};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// One machine of each kind: the lowering's, the evaluator written in
/// FX-26, a cellular interpreter, register code, and native code.
const MACHINES: [&str; 5] = ["rs-scheme-vm", "fx-ast-eval", "fx-cells-rsinterp", "fx-regs-rsjit-cellcc", "fx-regs-rsjit-nativecc"];

/// `program` run on `machine`: its status, standard output and error.
fn run(machine: &str, program: &str) -> (Option<i32>, String, String) {
    let path = format!("{}/tests/programs/io/{program}", env!("CARGO_MANIFEST_DIR"));
    let out = Command::new(FIXPT).args(["--fx26-machine", machine, "run", &path]).stdin(Stdio::null()).output().expect("fixpt runs");
    (out.status.code(), String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned())
}

/// Each program on each machine, at once.
fn on_every_machine(program: &'static str) -> Vec<(&'static str, (Option<i32>, String, String))> {
    let runs: Vec<_> = MACHINES.iter().map(|m| (*m, std::thread::spawn(move || run(m, program)))).collect();
    runs.into_iter().map(|(m, t)| (m, t.join().expect("ran"))).collect()
}

#[test]
fn the_standard_streams_written() {
    for (m, (status, out, err)) in on_every_machine("streams.fx") {
        assert_eq!((status, out.as_str(), err.as_str()), (Some(0), "hello, world\n", "to stderr\n"), "{m}");
    }
}

#[test]
fn main_gives_the_status() {
    for (m, (status, out, err)) in on_every_machine("main-status.fx") {
        assert_eq!((status, out.as_str(), err.as_str()), (Some(44), "in main\n", ""), "{m}");
    }
}

#[test]
fn exit_ends_the_run() {
    for (m, (status, out, err)) in on_every_machine("exit.fx") {
        assert_eq!((status, out.as_str(), err.as_str()), (Some(7), "0\n1\n2\n", ""), "{m}");
    }
}

#[test]
fn a_failed_run_exits_70() {
    for (m, (status, out, err)) in on_every_machine("trap.fx") {
        assert_eq!((status, out.as_str()), (Some(70), "before\n"), "{m}: {err}");
        assert!(!err.is_empty(), "{m}: the failure is said");
    }
}

/// A write to a pipe whose reader has gone: an `io-error` of kind
/// `broken-pipe`, which the program answers.
#[test]
fn a_failed_write_is_a_value() {
    for m in MACHINES {
        let path = format!("{}/tests/programs/io/broken-pipe.fx", env!("CARGO_MANIFEST_DIR"));
        let mut child = Command::new(FIXPT)
            .args(["--fx26-machine", m, "run", &path])
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("fixpt runs");
        drop(child.stdout.take());
        let out = child.wait_with_output().expect("ends");
        let err = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(3), "{m}: {err}");
        assert!(err.starts_with("broken pipe: "), "{m}: {err}");
    }
}

/// Files, relative to the working directory, each machine's its own: two
/// written, one replaced (no file of its left beside it), the names
/// sorted, one read back, a missing one `not-found`.
#[test]
fn files_written_listed_and_read() {
    let path = format!("{}/tests/programs/io/files.fx", env!("CARGO_MANIFEST_DIR"));
    for m in MACHINES {
        let dir = std::env::temp_dir().join(format!("fixpt-io-files-{m}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("a directory");
        let out = Command::new(FIXPT).args(["--fx26-machine", m, "run", &path]).current_dir(&dir).stdin(Stdio::null()).output().expect("fixpt runs");
        let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        assert_eq!((out.status.code(), stdout.as_ref()), (Some(5), "a.txt\nb.txt\nbee, again\n"), "{m}: {stderr}");
        let mut left: Vec<_> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().file_name().into_string().unwrap()).collect();
        left.sort();
        assert_eq!(left, ["a.txt", "b.txt"], "{m}");
        std::fs::remove_dir_all(&dir).expect("removed");
    }
}

/// The program's own arguments after `--`, an empty one too; and a sleep
/// on the clock, which the clock then shows has passed.
#[test]
fn arguments_and_the_clock() {
    let path = format!("{}/tests/programs/io/args-clock.fx", env!("CARGO_MANIFEST_DIR"));
    let runs: Vec<_> = MACHINES
        .iter()
        .map(|m| {
            let path = path.clone();
            (*m, std::thread::spawn(move || Command::new(FIXPT).args(["--fx26-machine", m, "run", &path, "--", "one", "two words", ""]).output().expect("fixpt runs")))
        })
        .collect();
    for (m, t) in runs {
        let out = t.join().expect("ran");
        let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        assert_eq!((out.status.code(), stdout.as_ref()), (Some(0), "one;two words;;"), "{m}: {stderr}");
    }
}
