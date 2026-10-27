//! `FIXPT_PERF_MAP`: a run writes `/tmp/perf-PID.map` as Linux's `perf`
//! reads it (`fixpt_native::symbols`), each line `START LEN NAME`, START
//! and LEN in hex, a procedure the native convention compiled named by its
//! global's name (and the thunk its definition's value is computed by,
//! `define NAME`), as kayak's `fixpt run` on `fx-regs-rsjit-nativecc`.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use std::process::{Command, Stdio};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

#[test]
fn a_run_writes_a_perf_map() {
    let dir = std::env::temp_dir().join(format!("fixpt-perf-map-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let program = dir.join("count.fx");
    let text = "(define count (subr (maxeff spin (read (globals count))) ((n : int) (k : int)) int) (lambda (n k) (if (= n 0) k (count (- n 1) (+ k 1)))))\n(count 1000 0)\n";
    std::fs::write(&program, text).unwrap();
    let child = Command::new(FIXPT)
        .args(["--fx26-machine", "fx-regs-rsjit-nativecc", "run", program.to_str().unwrap()])
        .env("FIXPT_PERF_MAP", "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("fixpt runs");
    let map = format!("/tmp/perf-{}.map", child.id());
    let out = child.wait_with_output().unwrap();
    let written = std::fs::read_to_string(&map);
    let _ = std::fs::remove_file(&map);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let written = written.unwrap_or_else(|e| panic!("{map}: {e}"));
    for line in written.lines() {
        let mut parts = line.splitn(3, ' ');
        let (start, len, name) = (parts.next(), parts.next(), parts.next());
        let hex = |s: Option<&str>| s.is_some_and(|s| u64::from_str_radix(s, 16).is_ok());
        assert!(hex(start) && hex(len) && name.is_some_and(|n| !n.is_empty()), "not as perf reads it: {line}");
    }
    for name in [" native count", " native define count"] {
        assert!(written.lines().any(|l| l.ends_with(name)), "no `{name}` in {map}:\n{written}");
    }
}
