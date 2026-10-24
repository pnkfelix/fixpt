//! What reaches the native convention (`fx-regs-rsjit-nativecc`), as the
//! code `FIXPT_SYMBOLS` names shows: kayak's compiler ran 25 times slower
//! for want of it (`TODO.md` §121).

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
