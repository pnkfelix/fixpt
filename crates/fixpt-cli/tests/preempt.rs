//! Preemption at fuel polls (`TODO.md` §92, Q2), on each machine FX-26
//! runs on: a process that spins for ever does not starve the one whose
//! answer the program waits for. A machine that does not preempt waits for
//! ever, so each run is a child process, killed if it takes a minute.

use std::process::Command;
use std::time::{Duration, Instant};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// `fixpt --fx26-machine machine eval path`'s output, with time slices of
/// `slice` polls if given (`FIXPT_SLICE`), or `None` if it did not end
/// within `limit`.
fn run(machine: &str, path: &str, slice: Option<u64>, limit: Duration) -> Option<String> {
    let mut cmd = Command::new(FIXPT);
    if let Some(n) = slice {
        cmd.env("FIXPT_SLICE", n.to_string());
    }
    let mut child = cmd
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

/// The machines, the stencils only where this build found a nightly
/// compiler.
fn machines() -> Vec<&'static str> {
    let stencils = !fixpt_native::stencil::opt_levels().is_empty();
    [
        "rs-scheme-vm",
        "fx-ast-eval",
        "fx-cells-rsinterp",
        "fx-cells-asminterp",
        "fx-cells-rsjit-cellcc",
        "fx-cells-fxjit-cellcc",
        "fx-cells-stencils-cellcc",
        "fx-regs-rsjit-cellcc",
        "fx-regs-rsjit-nativecc",
    ]
    .into_iter()
    .filter(|m| stencils || !m.contains("stencils"))
    .collect()
}

/// Program `name` in `programs/preempt` on each of `machines`: as its
/// first line says, `;; => value`.
fn as_said(name: &str, machines: &[&str], slice: Option<u64>) {
    let path = format!("{}/../fixpt-fx26/tests/programs/preempt/{name}", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path).expect("readable");
    let want = format!("{} : int", text.lines().next().and_then(|l| l.strip_prefix(";; => ")).expect("says"));
    let mut wrong = Vec::new();
    for m in machines {
        match run(m, &path, slice, Duration::from_secs(60)) {
            Some(out) if out.contains(&want) => {}
            Some(out) => wrong.push(format!("{m}: {out}")),
            None => wrong.push(format!("{m}: still running after a minute")),
        }
    }
    assert!(wrong.is_empty(), "{name}, slice {slice:?}:\n{}", wrong.join("\n"));
}

#[test]
fn a_spinning_process_is_preempted_on_each_machine() {
    as_said("spinner.fx", &machines(), None);
}

/// What a preempted process keeps, in registers or frames, is there, moved
/// by the collections the other's work makes, when it goes on. Not the
/// evaluator written in FX-26, whose own recursion is too deep for 100,000
/// calls; it runs the short one.
#[test]
fn preempted_processes_keep_what_they_hold() {
    let ms: Vec<&str> = machines().into_iter().filter(|m| *m != "fx-ast-eval").collect();
    as_said("allocating.fx", &ms, None);
}

/// The same, a shorter run, preempted at nearly every poll: every 7th.
#[test]
fn preempted_at_nearly_every_poll() {
    as_said("allocating-short.fx", &machines(), Some(7));
}
