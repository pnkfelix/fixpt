//! `get-environment-variable` and its effect, `(io env-read)`, on every
//! machine: a variable set, set empty, unset, and a name that cannot be
//! one; a procedure that reads one without saying so refused by both
//! checkers.

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

const MACHINES: &[&str] = &["rs-scheme-vm", "fx-ast-eval", "fx-cells-rsinterp", "fx-regs-rsjit-cellcc"];

fn program(name: &str) -> String {
    format!("{}/tests/programs/environment/{name}", env!("CARGO_MANIFEST_DIR"))
}

#[test]
fn a_variable_is_read_on_every_machine() {
    for m in MACHINES {
        let out = Command::new(FIXPT)
            .args(["--machine", m, "eval", &program("get.fx")])
            .env("FIXPT_TEST_SET", "a b")
            .env("FIXPT_TEST_EMPTY", "")
            .env_remove("FIXPT_TEST_UNSET")
            .output()
            .expect("runs");
        let (out, err) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        let want = r#"("=a b" "=" "unset" "unset" "unset") : "#;
        assert!(out.lines().last().is_some_and(|l| l.starts_with(want)), "{m}: {out}{err}");
    }
}

#[test]
fn reading_one_is_an_effect_a_type_says() {
    let text = "(define f (subr pure () bool) (lambda () (tagcase (get-environment-variable \"HOME\") (value v #t) (unset u #f) (not-text u #f))))";
    let out = Command::new(FIXPT).args(["check", text]).output().expect("runs");
    let said = String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr);
    assert!(said.contains("env-read") && !said.contains("disagree"), "{said}");
}
