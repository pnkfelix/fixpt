//! Code a program makes and runs (`TODO.md` §97, `docs/research/
//! declared-conventions.md`), on each machine FX-26 runs on: arm64 machine
//! code a program wrote into a bloblet, sealed into the code area and made
//! a native procedure, called from every machine that runs native code; and
//! on the one that runs none (the evaluator written in FX-26), the program's
//! own fallback (`programs/made-code/`).

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// The machines, the stencils only where this build found a nightly
/// compiler; and whether each runs native code.
fn machines() -> Vec<(&'static str, bool)> {
    let stencils = !fixpt_native::stencil::opt_levels().is_empty();
    [
        ("rs-scheme-vm", true),
        ("fx-ast-eval", false),
        ("fx-cells-rsinterp", true),
        ("fx-cells-asminterp", true),
        ("fx-cells-rsjit-cellcc", true),
        ("fx-cells-fxjit-cellcc", true),
        ("fx-cells-stencils-cellcc", true),
        ("fx-regs-rsjit-cellcc", true),
        ("fx-regs-rsjit-nativecc", true),
    ]
    .into_iter()
    .filter(|(m, _)| stencils || !m.contains("stencils"))
    .collect()
}

/// `fixpt --fx26-machine machine eval` of `programs/made-code/name`: the
/// values of its last `n` forms, each as its line begins.
fn values(machine: &str, name: &str, n: usize) -> Vec<String> {
    let path = format!("{}/../fixpt-fx26/tests/programs/made-code/{name}", env!("CARGO_MANIFEST_DIR"));
    let out = Command::new(FIXPT).args(["--fx26-machine", machine, "eval", &path]).output().expect("fixpt runs");
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    let lines: Vec<&str> = text.lines().collect();
    lines[lines.len().saturating_sub(n)..].iter().map(|l| l.split(" : ").next().unwrap_or(l).to_string()).collect()
}

/// A leaf that adds two fixnums, and one that reads its own field, a pair,
/// across the collections a loop's allocation makes.
#[test]
fn leaves_made_and_run() {
    let runs: Vec<_> = machines().into_iter().map(|(m, native)| (m, native, std::thread::spawn(move || values(m, "leaves.fx", 3)))).collect();
    for (m, native, t) in runs {
        let want = [if native { "#t" } else { "#f" }, "42", "41"];
        assert_eq!(t.join().expect("ran"), want, "{m}");
    }
}
