//! Code a program makes and runs (`TODO.md` §97, `docs/research/
//! declared-conventions.md`), on each machine FX-26 runs on: machine code a
//! program wrote into a bloblet, sealed into the code area and made a
//! native procedure, called from every machine that runs native code; and
//! on the one that runs none (the evaluator written in FX-26), the program's
//! own fallback. arm64's programs are `programs/made-code/`, x86_64's
//! `programs/made-code-x86_64/`, each the other's twin, to the convention
//! of its machine (`native-arm64.conv`, `native-x86_64.conv`).

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// The programs' directory: this machine's twins.
const DIR: &str = if cfg!(target_arch = "x86_64") { "made-code-x86_64" } else { "made-code" };
/// The `target` clause of this machine's convention.
const TARGET: &str = if cfg!(target_arch = "x86_64") { "\"(target x86_64)\"" } else { "\"(target arm64)\"" };

/// The machines, the stencils only where this build found a nightly
/// compiler, and x86_64's own; and whether each runs the native code a
/// program makes, which is arm64's or x86_64's: elsewhere none does, and
/// each takes the program's fallback.
fn machines() -> Vec<(&'static str, bool)> {
    let stencils = !fixpt_native::stencil::opt_levels().is_empty();
    let x86 = cfg!(target_arch = "x86_64");
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
        ("fx-regs-fxjit-cellcc", true),
        ("fx-regs-fxjit-nativecc", true),
    ]
    .into_iter()
    .filter(|(m, _)| stencils || !m.contains("stencils"))
    .filter(|(m, _)| fixpt_native::NATIVE_CONVENTION_AVAILABLE || !m.ends_with("nativecc"))
    .filter(|(m, _)| x86 || !m.starts_with("fx-regs-fxjit"))
    .map(|(m, native)| (m, native && fixpt_native::NATIVE_CONVENTION_AVAILABLE))
    .collect()
}

/// `fixpt --fx26-machine machine eval` of `programs/DIR/name`: the
/// values of its last `n` forms, each as its line begins.
fn values(machine: &str, name: &str, n: usize) -> Vec<String> {
    values_with(machine, name, n, &[])
}

/// The same, with these variables in the environment.
fn values_with(machine: &str, name: &str, n: usize, vars: &[(&str, &str)]) -> Vec<String> {
    let path = format!("{}/../fixpt-fx26/tests/programs/{DIR}/{name}", env!("CARGO_MANIFEST_DIR"));
    let out = Command::new(FIXPT).args(["--fx26-machine", machine, "eval", &path]).envs(vars.iter().copied()).output().expect("fixpt runs");
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

/// A program that declares the convention it makes code to
/// (`define-convention`, `programs/made-code/declared.fx`): the native
/// convention, named so, its clauses as the program reads them, and a leaf
/// that subtracts, made at it.
#[test]
fn code_made_to_a_declared_convention() {
    let runs: Vec<_> = machines().into_iter().map(|(m, _)| (m, std::thread::spawn(move || values(m, "declared.fx", 2)))).collect();
    for (m, t) in runs {
        assert_eq!(t.join().expect("ran"), [TARGET, "42"], "{m}");
    }
}

/// Typed calls of a made procedure in procedures, in tail position and
/// not (`programs/made-code/typed-calls.fx`): on the arm64 cellular
/// machines a typed tail call of one stopped ("no routine is numbered
/// 40"), and register code's `invoke` crashed.
#[test]
fn typed_calls_of_a_made_procedure() {
    let runs: Vec<_> = machines().into_iter().map(|(m, _)| (m, std::thread::spawn(move || values(m, "typed-calls.fx", 3)))).collect();
    for (m, t) in runs {
        assert_eq!(t.join().expect("ran"), ["42", "42", "42"], "{m}");
    }
}

/// Code a program makes that is not a leaf (`programs/made-code/
/// frames.fx`): a frame with its stack map, the stack's limit, a million
/// pairs by `cons` across collections, fuel and `poll`, and a call of a
/// procedure it is given, native or not; and made at every depth of a
/// recursion. The bytecode VM's procedures cannot be called back, which it
/// says. Then on two machines with time slices of 3, a small nursery and a
/// small stack cache, where the made code's own entry passes the stack's
/// limit (`overflow`).
#[test]
fn code_with_a_frame_made_and_run() {
    let runs: Vec<_> = machines().into_iter().map(|(m, _)| (m, std::thread::spawn(move || values(m, "frames.fx", 2)))).collect();
    for (m, t) in runs {
        let got = t.join().expect("ran");
        if m == "rs-scheme-vm" {
            assert!(got.last().is_some_and(|l| l.contains("cannot call back a procedure of the bytecode VM")), "{m}: {got:?}");
            continue;
        }
        assert_eq!(got, ["500000500000", "165055"], "{m}");
    }
    let stress = [("FIXPT_SLICE", "3"), ("FIXPT_NURSERY", "4096"), ("FIXPT_NATIVE_STACK_CACHE", "1024")];
    for m in ["fx-cells-rsinterp", "fx-regs-rsjit-nativecc"] {
        assert_eq!(values_with(m, "frames.fx", 2, &stress), ["500000500000", "165055"], "{m}, stressed");
    }
}

/// Code made by a generator that reads the convention as data
/// (`programs/made-code/generated.fx`, `fx26:convention.fx`): `frames.fx`'s
/// procedure, every register, offset, tag and routine's entry taken from
/// the declaration read as a `convention`. It is word for word (on x86_64,
/// byte for byte) the code `frames.fx` writes out, and runs as that does.
#[test]
fn code_made_from_the_convention_read_as_data() {
    let runs: Vec<_> = machines().into_iter().map(|(m, _)| (m, std::thread::spawn(move || values(m, "generated.fx", 2)))).collect();
    for (m, t) in runs {
        let got = t.join().expect("ran");
        if m == "rs-scheme-vm" {
            assert!(got.last().is_some_and(|l| l.contains("cannot call back a procedure of the bytecode VM")), "{m}: {got:?}");
            continue;
        }
        assert_eq!(got, ["500000500000", "165055"], "{m}");
    }
    let dir = format!("{}/../fixpt-fx26/tests/programs/{DIR}", env!("CARGO_MANIFEST_DIR"));
    let frames = std::fs::read_to_string(format!("{dir}/frames.fx")).expect("reads");
    // Each line's words (or bytes) before its comment, to the list's end.
    let written: Vec<&str> = frames
        .lines()
        .skip_while(|l| !l.trim_end().ends_with("(list"))
        .skip(1)
        .map(|l| l.split(';').next().unwrap_or("").split_whitespace().map(|w| w.trim_end_matches(')')).filter(|w| w.parse::<u32>().is_ok()).collect::<Vec<_>>())
        .take_while(|ws| !ws.is_empty())
        .flatten()
        .collect();
    assert_eq!(written.len(), if cfg!(target_arch = "x86_64") { 235 } else { 51 });
    let generated = std::fs::read_to_string(format!("{dir}/generated.fx")).expect("reads");
    let path = format!("{}/generated-words.fx", env!("CARGO_TARGET_TMPDIR"));
    let made = if cfg!(target_arch = "x86_64") { "(code-bytes conv)" } else { "(build-code conv)" };
    std::fs::write(&path, format!("{generated}\n{made}\n")).expect("writes");
    let out = Command::new(FIXPT).args(["--fx26-machine", "fx-regs-rsjit-nativecc", "eval", &path]).output().expect("fixpt runs");
    let text = String::from_utf8_lossy(&out.stdout);
    let last = text.lines().last().unwrap_or("");
    let made: Vec<&str> = last.split(" : ").next().unwrap_or("").trim_matches(['(', ')']).split(' ').collect();
    assert_eq!(made, written, "{last}");
}

/// A primitive reached by made code through a field of its code bloblet,
/// not by a number (`programs/made-code/linked.fx`): `*`, the standard
/// operation as a value, then a procedure of the program's own, each
/// called by the code that holds it; a hundred thousand calls, `poll`
/// among them. Then on two machines with time slices of 3 and a small
/// nursery. On the bytecode VM, whose `*` is its primitive object, native
/// code called that out of the machine's reach ("a call of what is not a
/// procedure"); a simple primitive now runs as it is.
#[test]
fn a_primitive_reached_through_a_field() {
    let want = ["49", "333338333350000", "48"];
    let runs: Vec<_> = machines().into_iter().filter(|(m, _)| *m != "rs-scheme-vm").map(|(m, _)| (m, std::thread::spawn(move || values(m, "linked.fx", 3)))).collect();
    for (m, t) in runs {
        let got = t.join().expect("ran");
        assert_eq!(got, want, "{m}");
    }
    // The bytecode VM calls the primitive (a simple one needs no machine),
    // and cannot be called back for the program's own procedure.
    let got = values("rs-scheme-vm", "linked.fx", 4);
    assert_eq!(got[..2], want[..2], "{got:?}");
    assert!(got[3].contains("cannot call back a procedure of the bytecode VM"), "{got:?}");
    let stress = [("FIXPT_SLICE", "3"), ("FIXPT_NURSERY", "4096"), ("FIXPT_NATIVE_STACK_CACHE", "1024")];
    for m in ["fx-cells-rsinterp", "fx-regs-rsjit-nativecc"] {
        assert_eq!(values_with(m, "linked.fx", 3, &stress), want, "{m}, stressed");
    }
}

/// A bloblet made by made code, by the convention's `bloblet` routine
/// (`programs/made-code/allocated.fx`): its fields stored, twenty thousand
/// kept across the collections their making makes, and a size it refuses,
/// the trap.
#[test]
fn a_bloblet_made_by_the_routine() {
    let want = ["\"made 24 24\"", "1000000"];
    let refused = "no bloblet of -1 bytes and 2 fields";
    let runs: Vec<_> = machines().into_iter().map(|(m, _)| (m, std::thread::spawn(move || values(m, "allocated.fx", 4)))).collect();
    for (m, t) in runs {
        let got = t.join().expect("ran");
        assert_eq!(got[..2], want, "{m}");
        assert!(got[3].contains(refused), "{m}: {got:?}");
    }
    let stress = [("FIXPT_SLICE", "3"), ("FIXPT_NURSERY", "4096"), ("FIXPT_NATIVE_STACK_CACHE", "1024")];
    for m in ["fx-cells-rsinterp", "fx-regs-rsjit-nativecc"] {
        let got = values_with(m, "allocated.fx", 4, &stress);
        assert_eq!(got[..2], want, "{m}, stressed");
        assert!(got[3].contains(refused), "{m}, stressed: {got:?}");
    }
}

/// Both machines' declarations, read as data (`fx26:convention.fx`) on
/// this one and printed back clause for clause: arm64's registers and
/// x86_64's, and x86_64's places in the state (`(state reg4)`, `(state
/// fuel)`, …) and its `pushed` return address.
#[test]
fn both_declarations_read_as_data() {
    for target in ["arm64", "x86_64"] {
        let conv = std::fs::read_to_string(format!("{}/../fixpt-runtime/src/native-{target}.conv", env!("CARGO_MANIFEST_DIR"))).expect("reads");
        let lines: Vec<String> = conv.lines().map(|l| format!("{l:?}")).collect();
        let program = format!(
            "(define cv (load-input \"fx26:convention.fx\"))\n(define ts (listof string acyclic) (the (listof string acyclic) (list {})))\n(tagcase ((with cv cv-read-clauses) ts) (ok c (extract c target)) (refused w w))\n",
            lines.join(" ")
        );
        let path = format!("{}/read-{target}.fx", env!("CARGO_TARGET_TMPDIR"));
        std::fs::write(&path, program).expect("writes");
        let out = Command::new(FIXPT).args(["--fx26-machine", "fx-cells-rsinterp", "eval", &path]).output().expect("fixpt runs");
        let text = String::from_utf8_lossy(&out.stdout);
        assert!(text.lines().last().is_some_and(|l| l.starts_with(&format!("{target:?} :"))), "{target}: {text}{}", String::from_utf8_lossy(&out.stderr));
    }
}
