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
/// compiler, the native convention only where it runs.
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
    .filter(|m| fixpt_native::NATIVE_CONVENTION_AVAILABLE || !m.ends_with("nativecc"))
    .collect()
}

/// Program `name` in `programs/preempt` on each of `machines`: as its
/// first line says, `;; => value`.
fn as_said(name: &str, machines: &[&str], slice: Option<u64>) {
    as_said_in("preempt", name, machines, slice)
}

fn as_said_in(dir: &str, name: &str, machines: &[&str], slice: Option<u64>) {
    let path = format!("{}/../fixpt-fx26/tests/programs/{dir}/{name}", env!("CARGO_MANIFEST_DIR"));
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

/// Each test below on each machine, a test of its own for each, so that
/// they run at once (`TODO.md` §167): together, run machine after
/// machine, they were the suite's longest. A machine this build has not
/// (`machines`) runs nothing.
macro_rules! on_each_machine {
    ($($module:ident: $machine:expr;)*) => {$(
        mod $module {
            fn ms() -> Vec<&'static str> {
                super::machines().into_iter().filter(|m| *m == $machine).collect()
            }

            #[test]
            fn a_spinning_process_is_preempted() {
                super::a_spinning_process_is_preempted(&ms());
            }

            #[test]
            fn a_monitored_failure_is_a_message() {
                super::a_monitored_failure_is_a_message(&ms());
            }

            #[test]
            fn an_attempts_failure_is_caught() {
                super::an_attempts_failure_is_caught(&ms());
            }

            #[test]
            fn preempted_processes_keep_what_they_hold() {
                super::preempted_processes_keep_what_they_hold(&ms());
            }

            #[test]
            fn preempted_at_nearly_every_poll() {
                super::preempted_at_nearly_every_poll(&ms());
            }
        }
    )*};
}

on_each_machine! {
    rs_scheme_vm: "rs-scheme-vm";
    fx_ast_eval: "fx-ast-eval";
    fx_cells_rsinterp: "fx-cells-rsinterp";
    fx_cells_asminterp: "fx-cells-asminterp";
    fx_cells_rsjit_cellcc: "fx-cells-rsjit-cellcc";
    fx_cells_fxjit_cellcc: "fx-cells-fxjit-cellcc";
    fx_cells_stencils_cellcc: "fx-cells-stencils-cellcc";
    fx_regs_rsjit_cellcc: "fx-regs-rsjit-cellcc";
    fx_regs_rsjit_nativecc: "fx-regs-rsjit-nativecc";
}

/// Every machine of `machines` is one of `on_each_machine`'s.
#[test]
fn each_machine_has_its_tests() {
    let listed = [
        "rs-scheme-vm",
        "fx-ast-eval",
        "fx-cells-rsinterp",
        "fx-cells-asminterp",
        "fx-cells-rsjit-cellcc",
        "fx-cells-fxjit-cellcc",
        "fx-cells-stencils-cellcc",
        "fx-regs-rsjit-cellcc",
        "fx-regs-rsjit-nativecc",
    ];
    for m in machines() {
        assert!(listed.contains(&m), "{m} has no tests of its own");
    }
}

fn a_spinning_process_is_preempted(ms: &[&str]) {
    as_said("spinner.fx", ms, None);
    // Spinning in cellular code native code called (`TODO.md` §93).
    as_said("spinner-cellular.fx", ms, None);
}

/// A monitored process's failure is a message to its watcher, on each
/// machine (`programs/monitors`, `TODO.md` §94): a failure the machine traps
/// is caught as the runtime's primitives' are.
fn a_monitored_failure_is_a_message(ms: &[&str]) {
    for name in ["worker-fails.fx", "trap.fx", "par-branch.fx", "one-message.fx", "race-lost.fx"] {
        as_said_in("monitors", name, ms, None);
    }
}

/// `attempt` (Heist's, `FIXPT-CHANGES.md` F1) on each machine
/// (`programs/attempt`): a failure the machine traps is its on-failure's
/// value.
fn an_attempts_failure_is_caught(ms: &[&str]) {
    for name in ["trap.fx", "error.fx", "nested.fx", "own-region.fx", "in-process.fx", "handler-io.fx", "many.fx", "evaluator-after-failure.fx"] {
        as_said_in("attempt", name, ms, None);
    }
}

/// What a preempted process keeps, in registers or frames, is there, moved
/// by the collections the other's work makes, when it goes on. Not the
/// evaluator written in FX-26, whose own recursion is too deep for 100,000
/// calls; it runs the short one.
fn preempted_processes_keep_what_they_hold(ms: &[&str]) {
    let ms: Vec<&str> = ms.iter().copied().filter(|m| *m != "fx-ast-eval").collect();
    as_said("allocating.fx", &ms, None);
}

/// The same, a shorter run, preempted at nearly every poll: every 7th.
fn preempted_at_nearly_every_poll(ms: &[&str]) {
    as_said("allocating-short.fx", ms, Some(7));
    // One loop in cellular code native code called, which calls native
    // code each time round: continuations that cross the machines.
    as_said("allocating-cellular.fx", ms, Some(7));
}
