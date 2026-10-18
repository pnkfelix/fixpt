//! `fx-regs-fxjit-nativecc`: the native convention on x86_64, each
//! procedure's code made by the compiler written in FX-26
//! (`native-direct-x64.fx`). Each test program runs on it as on
//! `fx-regs-rsjit-nativecc`, whose procedures Rust compiles: the same
//! output and errors; and with `FIXPT_FX_NATIVE_ORACLE`, every closure
//! either compiles is compiled by both, the same bytes, fields and
//! call-outs (`fixpt_native::direct::describe`), or both decline it.

#![cfg(target_arch = "x86_64")]

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");
const PROGRAMS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../fixpt-fx26/tests/programs");

/// `path` run on `machine` (with the oracle, for FX-26's): its output,
/// errors and status, and what the oracle said.
fn run(machine: &str, path: &str) -> (String, Vec<String>) {
    let out = Command::new(FIXPT)
        .args(["--fx26-machine", machine, "eval", path])
        .env("FIXPT_FX_NATIVE_ORACLE", "1")
        .output()
        .expect("fixpt runs");
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let (oracle, rest): (Vec<&str>, Vec<&str>) = stderr.lines().partition(|l| l.starts_with("fx-native oracle:") || l.starts_with("  Rust") || l.starts_with("  FX-26"));
    (format!("{}\n{}\n{:?}", String::from_utf8_lossy(&out.stdout), rest.join("\n"), out.status.code()), oracle.into_iter().map(String::from).collect())
}

/// The programs of the directories `subs` (all but those that loop until
/// a step limit, and the benchmarks, if none), on both machines, in
/// parallel: what differs.
fn compare(subs: &[&str]) -> (usize, Vec<String>) {
    let mut dirs: Vec<String> = if subs.is_empty() {
        std::fs::read_dir(PROGRAMS).unwrap().map(|e| e.unwrap().file_name().to_string_lossy().into_owned()).filter(|d| d != "diverge" && d != "bench").collect()
    } else {
        subs.iter().map(|s| s.to_string()).collect()
    };
    dirs.sort();
    let mut paths = Vec::new();
    for d in dirs {
        let Ok(entries) = std::fs::read_dir(format!("{PROGRAMS}/{d}")) else { continue };
        let mut ps: Vec<String> = entries.map(|p| p.unwrap().path().display().to_string()).filter(|p| p.ends_with(".fx")).collect();
        ps.sort();
        paths.extend(ps);
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    let wrong = std::sync::Mutex::new(Vec::new());
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get()).min(32);
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| loop {
                let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(path) = paths.get(k) else { break };
                let (want, _) = run("fx-regs-rsjit-nativecc", path);
                let (got, oracle) = run("fx-regs-fxjit-nativecc", path);
                let mut w = wrong.lock().unwrap();
                if !oracle.is_empty() {
                    w.push(format!("{path}: the oracle says\n{}", oracle.join("\n")));
                }
                if got != want {
                    w.push(format!("{path}: FX-26's\n{got}\nRust's\n{want}"));
                }
            });
        }
    });
    (paths.len(), wrong.into_inner().unwrap())
}

#[test]
fn the_native_programs_as_the_rust_compiler_compiles_them() {
    let (n, wrong) = compare(&["native"]);
    eprintln!("{n} programs; {} differ", wrong.len());
    assert!(wrong.is_empty(), "{}", wrong.iter().take(8).cloned().collect::<Vec<_>>().join("\n\n"));
}

#[test]
#[ignore = "every test program, minutes long: cargo test --profile checked -p fixpt-cli --test fx_native -- --ignored"]
fn every_test_program_as_the_rust_compiler_compiles_it() {
    let (n, wrong) = compare(&[]);
    eprintln!("{n} programs; {} differ", wrong.len());
    assert!(wrong.is_empty(), "{}", wrong.iter().take(8).cloned().collect::<Vec<_>>().join("\n\n"));
}
