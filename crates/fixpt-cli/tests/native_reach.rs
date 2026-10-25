//! What reaches the native convention (`fx-regs-rsjit-nativecc`), as the
//! code `FIXPT_SYMBOLS` names shows: kayak's compiler ran 25 times slower
//! for want of each (`TODO.md` §121).

#![cfg(target_arch = "x86_64")]

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// `text` run natively: its output, and the names of the code it made.
fn run(name: &str, text: &str) -> (String, String) {
    let dir = std::env::temp_dir().join(format!("fixpt-native-reach-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (program, syms) = (dir.join("p.fx"), dir.join("syms"));
    std::fs::write(&program, text).unwrap();
    let out = Command::new(FIXPT)
        .args(["--fx26-machine", "fx-regs-rsjit-nativecc", "eval", program.to_str().unwrap()])
        .env("FIXPT_SYMBOLS", &syms)
        .output()
        .expect("fixpt runs");
    let names = std::fs::read_to_string(&syms).unwrap_or_default();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    (String::from_utf8_lossy(&out.stdout).into_owned(), names)
}

fn has_native(names: &str, prefix: &str) -> bool {
    names.lines().any(|l| l.splitn(3, ' ').nth(2).is_some_and(|n| n.starts_with(&format!("native {prefix}"))))
}

/// An accessor of a record of more fields than a leaf has registers: its
/// `tagcase` loads only the field it uses, so it has register code, and is
/// native (a module holding one was cellular, all of it).
#[test]
fn a_wide_records_accessor_is_native() {
    let (out, names) = run("wide", include_str!("programs/native-reach/wide-accessor.fx"));
    assert!(out.contains("8 : int"), "{out}");
    assert!(!out.contains("not in the native convention"), "{out}");
    assert!(has_native(&names, "big-8"), "no native `big-8`:\n{names}");
}

/// A closure cellular code makes, where no native code is running (a
/// definition held cellular by `stay-cellular`), is compiled natively as it
/// is made, not adapted: native code calls it with no call-out to a
/// cellular machine.
#[test]
fn a_closure_cellular_code_makes_is_native() {
    let (out, names) = run("made", include_str!("programs/native-reach/made-closure.fx"));
    assert!(out.contains("5000 : int"), "{out}");
    assert!(has_native(&names, "adder@"), "no native `adder`:\n{names}");
}

/// A top-level procedure calling itself in tail position, defined one form
/// at a time: in register code a loop, behind a guard that its global holds
/// it still, not a call through the global each time round.
#[test]
fn a_definition_calling_itself_in_tail_position_loops() {
    use std::io::Write as _;
    let mut child = Command::new(FIXPT)
        .args(["--fx26-machine", "fx-regs-rsjit-nativecc", "repl"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt starts");
    let input = include_str!("programs/native-reach/self-loop.fx");
    child.stdin.take().expect("piped").write_all(input.as_bytes()).expect("writes");
    let out = String::from_utf8_lossy(&child.wait_with_output().expect("finishes").stdout).into_owned();
    assert!(out.contains("#t"), "{out}");
    assert!(out.contains("global-guard find written 1"), "no guard of its own global:\n{out}");
}
