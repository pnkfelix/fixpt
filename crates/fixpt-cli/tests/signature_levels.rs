//! A signature's `bind` facts (Heist's should-work note, entry 2): two into one
//! part are read as before, the later's levels outside the earlier's, and
//! warned of, with the one fact that says it, to be refused.

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

#[test]
fn two_binds_into_one_part_are_warned_of() {
    let dir = format!("{}/tests/programs/signatures", env!("CARGO_MANIFEST_DIR"));
    let out = Command::new(FIXPT).args(["eval", "two-binds.fx"]).current_dir(dir).output().expect("runs");
    let (said, err) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    assert!(out.status.success() && said.contains("5 : int"), "{said}{err}");
    assert!(err.contains("write one, its levels outermost first, `(bind go (x ...) in body)`; two will be refused"), "{err}");
    assert_eq!(err.matches("warning: a signature").count(), 1, "said once: {err}");
}
