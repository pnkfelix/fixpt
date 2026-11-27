//! A sum's label written bare, warned of once a file (`fixpt_fx26::labels`;
//! the user's, 2026-11-26): in a `sumof`'s variants and a `sum`'s
//! construction, the program's file and a module file it loads alike; not
//! quoted data, a macro's expansion (`define-datatype`), or a `tagcase`'s
//! arm; and nothing of a file whose labels are keywords.
use std::path::{Path, PathBuf};
use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// `programs/labels/`, where the programs are.
fn dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs/labels")
}

fn run(args: &[&str]) -> (bool, String) {
    let out = Command::new(FIXPT).args(args).current_dir(dir()).env("FIXPT_NO_FASL", "1").output().expect("runs");
    (out.status.success(), String::from_utf8_lossy(&out.stderr).into_owned())
}

const SAID: &str = "a future version will take a sum's label only as a keyword, as types print it, in `sumof`'s variants and `sum`'s constructions";

/// `bare.fx`, and the module file it loads, `m.fx`.
#[test]
fn a_bare_label_is_warned_of_once_a_file() {
    for args in [&["run", "bare.fx"][..], &["--fx26-machine", "fx-cells-rsinterp", "run", "bare.fx"]] {
        let (ok, err) = run(args);
        assert!(ok, "{args:?}: {err}");
        let program = format!("fixpt: bare.fx:2:35: warning: a sum's label written `bad`, not `#:bad`, and 1 more in this file: {SAID}: write `#:bad`");
        let module = format!("fixpt: in `m.fx`, 2:24: warning: a sum's label written `yes`, not `#:yes`, and 1 more in this file: {SAID}: write `#:yes`");
        assert_eq!((err.matches(&program).count(), err.matches(&module).count()), (1, 1), "{args:?}: {err}");
        assert_eq!(err.matches("a sum's label written").count(), 2, "{args:?}: {err}");
    }
}

#[test]
fn keyword_labels_are_not_warned_of() {
    let (ok, err) = run(&["run", "keywords.fx"]);
    assert!(ok && !err.contains("warning"), "{err}");
}
