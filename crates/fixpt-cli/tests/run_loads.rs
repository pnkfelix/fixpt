//! `fixpt run`'s loads: a path in a program file is from that file's
//! directory, as `fixpt eval`'s and `,load`'s are, whatever directory it
//! is run from (Heist's problem E).

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

#[test]
fn a_load_is_from_the_program_files_directory() {
    let dir = std::env::temp_dir().join(format!("fixpt-run-loads-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    std::fs::write(dir.join("sub/answer.fx"), "(define answer int 42)\n").unwrap();
    std::fs::write(dir.join("sub/main.fx"), "(define m (load-module \"answer.fx\"))\n(define main (lambda () (with m answer)))\n").unwrap();
    // Run from the directory above, so that the current directory has no
    // `answer.fx`.
    let out = Command::new(FIXPT).current_dir(&dir).args(["run", "sub/main.fx"]).output().expect("fixpt runs");
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(out.status.code(), Some(42), "{}", String::from_utf8_lossy(&out.stderr));
}
