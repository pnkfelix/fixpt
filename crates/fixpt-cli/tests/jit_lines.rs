//! Lines for a debugger (`fixpt_native::jitdebug`): with frames made from
//! the start (`FIXPT_JIT_DEBUG=frames`), each procedure the native
//! convention compiles has a line table, which `FIXPT_LINES` writes too, a
//! row a line: `NAME +OFFSET FILE:LINE`. A procedure of the program file is
//! placed in that file, at the lines of its definition; one of a module
//! file it loads (`load-module`), in that file. By either compiler to the
//! native convention; on arm64, the one written in Rust.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

#[test]
fn compiled_procedures_have_their_files_lines() {
    lines_on("fx-regs-rsjit-nativecc");
}

/// The same where the compiler written in FX-26 makes each procedure's code.
#[cfg(target_arch = "x86_64")]
#[test]
fn compiled_by_fx26_procedures_have_their_files_lines() {
    lines_on("fx-regs-fxjit-nativecc");
}

fn lines_on(machine: &str) {
    let dir = std::env::temp_dir().join(format!("fixpt-jit-lines-{machine}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    // `programs/jit-lines/`: the program, and the module file it loads.
    std::fs::write(dir.join("helper.fx"), include_str!("programs/jit-lines/helper.fx")).unwrap();
    std::fs::write(dir.join("main.fx"), include_str!("programs/jit-lines/main.fx")).unwrap();
    let lines = dir.join("lines.txt");
    let out = Command::new(FIXPT)
        .args(["--fx26-machine", machine, "run", dir.join("main.fx").to_str().unwrap()])
        .env("FIXPT_JIT_DEBUG", "frames")
        .env("FIXPT_LINES", &lines)
        .output()
        .expect("fixpt runs");
    let written = std::fs::read_to_string(&lines).unwrap_or_default();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    // Each row of `name`'s, as (file's name, line).
    let rows = |name: &str| -> Vec<(String, u32)> {
        written
            .lines()
            .filter(|l| l.split(' ').next() == Some(name))
            .filter_map(|l| {
                let (file, line) = l.rsplit_once(' ')?.1.rsplit_once(':')?;
                Some((std::path::Path::new(file).file_name()?.to_string_lossy().into_owned(), line.parse().ok()?))
            })
            .collect()
    };
    let count = rows("count");
    assert!(count.len() >= 2, "few rows for `count`:\n{written}");
    assert!(count.iter().all(|(f, l)| f == "main.fx" && (4..=7).contains(l)), "`count` placed {count:?}");
    let twice: Vec<(String, u32)> = written.lines().filter(|l| l.contains("helper.fx")).filter_map(|l| {
        let (_, line) = l.rsplit_once(':')?;
        Some(("helper.fx".to_string(), line.parse().ok()?))
    }).collect();
    // `twice`'s body at its line; the procedure making the module, of the
    // whole file, anywhere in it.
    assert!(twice.contains(&("helper.fx".to_string(), 4)) && twice.iter().all(|(_, l)| (1..=4).contains(l)), "the module's procedures placed {twice:?}:\n{written}");
}

/// With gdb here, and leave to attach (`ptrace_scope` 0): attached to a
/// program running native code, `scripts/debuggers/fixpt_gdb.py`'s
/// commands show the frames' values, and the backtrace its lines.
#[cfg(target_arch = "x86_64")]
#[test]
fn gdb_shows_the_frames_values() {
    use std::io::BufRead;
    let attach = std::fs::read_to_string("/proc/sys/kernel/yama/ptrace_scope").map_or(true, |s| s.trim() == "0");
    if !attach || Command::new("gdb").arg("--version").output().is_err() {
        eprintln!("no gdb, or no leave to attach: not tried");
        return;
    }
    let dir = std::env::temp_dir().join(format!("fixpt-jit-values-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let program = dir.join("values.fx");
    std::fs::write(&program, include_str!("programs/jit-lines/values.fx")).unwrap();
    let mut child = Command::new(FIXPT)
        .args(["--fx26-machine", "fx-regs-rsjit-nativecc", "--step-limit", "none", "run", program.to_str().unwrap()])
        .env("FIXPT_JIT_DEBUG", "frames")
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt runs");
    let mut first = String::new();
    std::io::BufReader::new(child.stdout.take().unwrap()).read_line(&mut first).unwrap();
    let script = concat!(env!("CARGO_MANIFEST_DIR"), "/../../scripts/debuggers/fixpt_gdb.py");
    let out = Command::new("gdb")
        .args(["-p", &child.id().to_string(), "-batch", "-nx", "-x", script])
        .args(["-ex", "thread 2", "-ex", "bt 4", "-ex", "frame 1", "-ex", "fx-frame", "-ex", "frame 0", "-ex", "fx-frame"])
        .output()
        .expect("gdb runs");
    let _ = child.kill();
    let _ = child.wait();
    let _ = std::fs::remove_dir_all(&dir);
    let text = String::from_utf8_lossy(&out.stdout);
    assert_eq!(first, "ready\n");
    assert!(text.contains("in spin () at ") && text.contains("values.fx:4"), "no line for `spin`:\n{text}");
    assert!(text.contains("in keep () at ") && text.contains("values.fx:9"), "no line for `keep`:\n{text}");
    // `keep` 1's frame keeps 2, the head of its list; `spin`, a leaf, none.
    assert!(text.contains("slot 2: 2") && text.contains("its code: #<bloblet"), "no values for `keep`:\n{text}");
    assert!(text.contains("no frame of its own here"), "`spin` taken for a frame:\n{text}");
}

/// With lldb here, on the Mac, and leave to attach: attached to a program
/// running native code, its backtrace names each compiled frame, the leaf
/// `spin` and the three `keep`s under it, and `scripts/debuggers/
/// fixpt_lldb.py`'s commands show their values. Lines need the program to
/// go on once after attaching (`docs/research/debugging.md`), which lldb's
/// batch mode cannot do and stop again.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn lldb_shows_the_frames_values() {
    use std::io::BufRead;
    if Command::new("lldb").arg("--version").output().is_err() {
        eprintln!("no lldb: not tried");
        return;
    }
    let dir = std::env::temp_dir().join(format!("fixpt-jit-values-lldb-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let program = dir.join("values.fx");
    std::fs::write(&program, include_str!("programs/jit-lines/values.fx")).unwrap();
    let mut child = Command::new(FIXPT)
        .args(["--fx26-machine", "fx-regs-rsjit-nativecc", "--step-limit", "none", "run", program.to_str().unwrap()])
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt runs");
    let mut first = String::new();
    std::io::BufReader::new(child.stdout.take().unwrap()).read_line(&mut first).unwrap();
    let script = concat!(env!("CARGO_MANIFEST_DIR"), "/../../scripts/debuggers/fixpt_lldb.py");
    let out = Command::new("lldb")
        .args(["--batch", "--no-lldbinit", "-o", &format!("command script import {script}")])
        .args(["-o", &format!("process attach --pid {}", child.id())])
        .args(["-o", "thread select 2", "-o", "bt 5", "-o", "frame select 1", "-o", "fx-frame", "-o", "frame select 0", "-o", "fx-frame"])
        .args(["-o", "process detach"])
        .output()
        .expect("lldb runs");
    let _ = child.kill();
    let _ = child.wait();
    let _ = std::fs::remove_dir_all(&dir);
    let text = String::from_utf8_lossy(&out.stdout);
    if text.contains("attach failed") || String::from_utf8_lossy(&out.stderr).contains("attach failed") {
        eprintln!("no leave to attach: not tried");
        return;
    }
    assert_eq!(first, "ready\n");
    assert!(text.contains("`spin + ") && text.matches("`keep + ").count() >= 3, "frames unnamed:\n{text}");
    // `keep` 1's frame keeps 2, the head of its list; `spin`, a leaf, none.
    assert!(text.contains("slot 2: 2") && text.contains("its code: #<bloblet"), "no values for `keep`:\n{text}");
    assert!(text.contains("no frame of its own here"), "`spin` taken for a frame:\n{text}");
}
