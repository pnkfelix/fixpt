//! Strings at a region, `(stringof r)` (the user's, 2026-10-28;
//! `docs/fx26.md`, "Strings at a region"): `programs/run/stringof.fx` on
//! each machine FX-26 runs on, the evaluator written in FX-26 among them,
//! each giving the same values.

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// The machines: the stencils only where this build found a nightly
/// compiler, the native convention's where it is, and x86_64's own.
fn machines() -> Vec<&'static str> {
    let stencils = !fixpt_native::stencil::opt_levels().is_empty();
    let x86 = cfg!(target_arch = "x86_64");
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
        "fx-regs-fxjit-cellcc",
        "fx-regs-fxjit-nativecc",
    ]
    .into_iter()
    .filter(|m| stencils || !m.contains("stencils"))
    .filter(|m| fixpt_native::NATIVE_CONVENTION_AVAILABLE || !m.ends_with("nativecc"))
    .filter(|m| x86 || !m.starts_with("fx-regs-fxjit"))
    .collect()
}

/// What `fixpt --machine machine eval` of the program says, each line as
/// far as its type.
fn values(machine: &str) -> Vec<String> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../fixpt-fx26/tests/programs/run/stringof.fx");
    let out = Command::new(FIXPT).args(["--machine", machine, "eval", path]).output().expect("fixpt runs");
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    text.lines().map(|l| l.split(" : ").next().unwrap_or(l).to_string()).collect()
}

#[test]
fn strings_at_a_region_on_every_machine() {
    let want = [
        "joined",
        "upcased!",
        "\"abcdéfg\"",
        "#t",
        "\"HELLO, WORLD\"",
        "(#\\b #\\c #\\b)",
        "#t",
        "#u8(195 169 33)",
    ];
    let runs: Vec<_> = machines().into_iter().map(|m| (m, std::thread::spawn(move || values(m)))).collect();
    for (m, t) in runs {
        assert_eq!(t.join().expect("ran"), want, "{m}");
    }
}
