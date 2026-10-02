//! `fixpt bench` on a named program: both tables, every column with a
//! time, and the answers agreeing.

use std::process::Command;

#[test]
fn bench_prints_a_run_table_and_a_compile_table() {
    let tak = concat!(env!("CARGO_MANIFEST_DIR"), "/../fixpt-fx26/tests/programs/bench/tak.fx");
    let out = Command::new(env!("CARGO_BIN_EXE_fixpt")).args(["bench", "--runs", "1", tak]).output().expect("runs");
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{text}{}", String::from_utf8_lossy(&out.stderr));
    let rows: Vec<&str> = text.lines().filter(|l| l.starts_with("| tak ")).collect();
    assert_eq!(rows.len(), 2, "a row in each table:\n{text}");
    assert!(!text.contains('✗'), "an answer differs:\n{text}");
    assert!(text.contains("| fx arm64 |"), "the compile table:\n{text}");
}
