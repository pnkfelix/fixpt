//! Preemption at fuel polls (`TODO.md` §92, Q2), on each machine FX-26
//! runs on: a process that spins for ever does not starve the one whose
//! answer the program waits for. A machine that does not preempt waits for
//! ever, so each run is a child process, killed if it takes a minute.

use std::process::Command;
use std::time::{Duration, Instant};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// `fixpt --fx26-machine machine eval path`'s output, or `None` if it did
/// not end within `limit`.
fn run(machine: &str, path: &str, limit: Duration) -> Option<String> {
    let mut child = Command::new(FIXPT)
        .args(["--fx26-machine", machine, "eval", path])
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt starts");
    let start = Instant::now();
    loop {
        if child.try_wait().expect("waits").is_some() {
            let out = child.wait_with_output().expect("finishes");
            return Some(format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr)));
        }
        if start.elapsed() > limit {
            let _ = child.kill();
            let _ = child.wait();
            return None;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

#[test]
fn a_spinning_process_is_preempted_on_each_machine() {
    let path = format!("{}/../fixpt-fx26/tests/programs/preempt/spinner.fx", env!("CARGO_MANIFEST_DIR"));
    let stencils = !fixpt_native::stencil::opt_levels().is_empty();
    let machines = [
        "rs-scheme-vm",
        "fx-ast-eval",
        "fx-cells-rsinterp",
        "fx-cells-asminterp",
        "fx-cells-rsjit-cellcc",
        "fx-cells-fxjit-cellcc",
        "fx-cells-stencils-cellcc",
    ];
    let mut wrong = Vec::new();
    for m in machines.into_iter().filter(|m| stencils || !m.contains("stencils")) {
        match run(m, &path, Duration::from_secs(60)) {
            Some(out) if out.contains("42 : int") => {}
            Some(out) => wrong.push(format!("{m}: {out}")),
            None => wrong.push(format!("{m}: still running after a minute")),
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
