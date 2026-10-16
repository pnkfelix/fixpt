//! One-shot continuations (`TODO.md` §98, kayak's request), on each machine
//! FX-26 runs on: resumed once, the answer; resumed twice, the same
//! failure everywhere, the run-time failure being what defines the meaning
//! (`programs/run/oneshot-*.fx`).

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

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

/// The last line `fixpt --fx26-machine machine eval` prints for
/// `programs/run/name`.
fn last_line(machine: &str, name: &str) -> String {
    let path = format!("{}/../fixpt-fx26/tests/programs/run/{name}", env!("CARGO_MANIFEST_DIR"));
    let out = Command::new(FIXPT).args(["--fx26-machine", machine, "eval", &path]).output().expect("fixpt runs");
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    text.lines().last().unwrap_or("").to_string()
}

#[test]
fn resumed_once_it_answers_and_twice_it_fails() {
    let runs: Vec<_> = machines()
        .into_iter()
        .map(|m| (m, std::thread::spawn(move || (last_line(m, "oneshot-once.fx"), last_line(m, "oneshot-twice.fx")))))
        .collect();
    for (m, t) in runs {
        let (once, twice) = t.join().expect("ran");
        assert!(once.starts_with("43 : int"), "{m}, once: {once}");
        assert!(twice.contains("! evaluation failed") && twice.contains(fixpt_heap::ONE_SHOT_TWICE), "{m}, twice: {twice}");
    }
}
