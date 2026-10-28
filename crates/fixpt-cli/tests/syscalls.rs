//! Syscalls (`docs/research/syscalls.md`), on each machine FX-26 runs on:
//! a runtime's own program (`--syscalls`) declares the capabilities it
//! calls by name, at a type in canonical form, and each machine checks the
//! declaration against its runtime's as it loads, and calls it. The
//! programs are `programs/syscalls/`.

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

/// `fixpt --machine machine [--syscalls] eval` of `programs/syscalls/name`:
/// the last `n` lines, each as far as its type.
fn values(machine: &str, name: &str, n: usize, syscalls: bool) -> Vec<String> {
    let path = format!("{}/../fixpt-fx26/tests/programs/syscalls/{name}", env!("CARGO_MANIFEST_DIR"));
    let flag = if syscalls { &["--syscalls"][..] } else { &[] };
    let out = Command::new(FIXPT).args(["--machine", machine]).args(flag).args(["eval", &path]).output().expect("fixpt runs");
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    let lines: Vec<&str> = text.lines().collect();
    lines[lines.len().saturating_sub(n)..].iter().map(|l| l.split(" : ").next().unwrap_or(l).to_string()).collect()
}

/// Each of `programs/syscalls/name` on every machine, alike: what it says.
fn on_every_machine(name: &'static str, n: usize) -> Vec<String> {
    let runs: Vec<_> = machines().into_iter().map(|m| (m, std::thread::spawn(move || values(m, name, n, true)))).collect();
    let mut first: Option<Vec<String>> = None;
    for (m, t) in runs {
        let got = t.join().expect("ran");
        match &first {
            Some(f) => assert_eq!(&got, f, "{m}, {name}"),
            None => first = Some(got),
        }
    }
    first.expect("a machine")
}

/// The three of code this runtime has, each there and called: a page's words;
/// no view of a flat array, which moves when collected; nothing to flush.
#[test]
fn the_runtimes_own_syscalls() {
    assert_eq!(on_every_machine("present.fx", 4), ["#t", "#t", "-1", "#u"]);
}

/// A pure one (Kayak's, a string's length in UTF-8): called from a pure
/// procedure; declared `(io sys)`, a type other than the runtime's, so its
/// declaration fails as it loads.
#[test]
fn a_pure_syscall() {
    assert_eq!(on_every_machine("pure.fx", 3), ["joined-length", "#t", "11"]);
    let says = "! evaluation failed: syscall utf8-length (\"kayak:string-utf8-length/1\"): \
                declared (subr (io sys) (string) int); this runtime's is (subr pure (string) int)";
    assert_eq!(on_every_machine("pure-declared-io.fx", 1), [says]);
}

/// An optional one the runtime has not: the program loads, and says so;
/// a call fails.
#[test]
fn an_optional_syscall_absent() {
    let failed = "! evaluation failed: syscall frob (\"test:frob/1\"): not available on this runtime";
    assert_eq!(on_every_machine("absent.fx", 3), ["#f", "", failed]);
}

/// A required one the runtime has not, and one it has at another type: the
/// declaration fails as it loads, the second saying both types, each in
/// canonical form.
#[test]
fn a_required_syscall_missing_or_of_another_type() {
    let missing = "! evaluation failed: syscall frob (\"test:frob/1\"): this runtime has none";
    assert_eq!(on_every_machine("missing.fx", 2), ["frob", missing]);
    let declared = "(poly ((r1 region) (r2 region)) (subr (maxeff (io sys) (read r1) (write r2)) \
                    ((flatarrayof i64 r1) (flatarrayof i64 r2) int) unit))";
    let ours = "(poly ((r1 region)) (subr (maxeff (io sys) (read r1)) ((flatarrayof i64 r1) int int) unit))";
    let says = format!("! evaluation failed: syscall flush-code (\"code:flush/1\"): declared {declared}; this runtime's is {ours}");
    assert_eq!(on_every_machine("other-type.fx", 2), ["flush-code".to_string(), says]);
}

/// Not a runtime's program: its declaration refused.
#[test]
fn an_ordinary_program_declares_none() {
    let out = values("fx-cells-rsinterp", "ordinary.fx", 1, false);
    assert!(out[0].ends_with("ordinary.fx:3:1: syscalls are declared only by a runtime's own code"), "{out:?}");
}
