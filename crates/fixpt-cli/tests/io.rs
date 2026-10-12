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
