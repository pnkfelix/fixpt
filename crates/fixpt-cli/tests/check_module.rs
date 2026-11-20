//! `fixpt check` of a module file (Heist's should-work note, entry 24): one
//! headed `module-parameters` checked as `load-module` reads it, any with
//! `--module`; a file of definitions alone refused as a program says how.

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

fn check(args: &[&str]) -> (Option<i32>, String) {
    let dir = format!("{}/tests/programs/check-module", env!("CARGO_MANIFEST_DIR"));
    let out = Command::new(FIXPT).arg("check").args(args).current_dir(dir).output().expect("runs");
    (out.status.code(), String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr))
}

#[test]
fn a_file_of_definitions_is_a_program_unless_said() {
    let (code, said) = check(&["defs.fx"]);
    assert!(code == Some(1) && said.contains("(read (globals a))") && said.contains("`fixpt check --module defs.fx`"), "{said}");
    let (code, said) = check(&["--module", "defs.fx"]);
    assert!(code == Some(0) && said.contains("checked as a module file") && said.contains("(val b (subr pure () int))") && said.contains("both checkers agree"), "{said}");
}

#[test]
fn a_file_headed_module_parameters_is_a_module_file() {
    let (code, said) = check(&["headed.fx"]);
    assert!(code == Some(0) && said.contains("(subr pure () (moduleof (val a int) (val b (subr pure () int))))") && said.contains("both checkers agree"), "{said}");
}

#[test]
fn a_module_file_is_a_file() {
    let (code, said) = check(&["--module", "(define a int 1)"]);
    assert!(code == Some(2) && said.contains("a module file is a file"), "{said}");
}
