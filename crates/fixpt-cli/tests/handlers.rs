//! Handlers that resume (Heist's R4, `TODO.md` §211, 6), on each machine
//! FX-26 runs on: a deep handler of user code polymorphic in its region,
//! in a turn's `letregion`, inside an `attempt` (`programs/run/deep-handler.fx`).

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

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

#[test]
fn a_deep_handler_resumes_in_its_region() {
    let path = format!("{}/../fixpt-fx26/tests/programs/run/deep-handler.fx", env!("CARGO_MANIFEST_DIR"));
    let runs: Vec<_> = machines()
        .into_iter()
        .map(|m| {
            let path = path.clone();
            (m, std::thread::spawn(move || Command::new(FIXPT).args(["--fx26-machine", m, "eval", &path]).output().expect("fixpt runs")))
        })
        .collect();
    for (m, t) in runs {
        let out = t.join().expect("ran");
        let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        assert!(text.lines().last().unwrap_or("").starts_with("20 : int"), "{m}: {text}");
    }
}
