//! Names for the machine code we make, for profilers: with
//! `FIXPT_SYMBOLS=FILE` set, every piece of machine code placed (the
//! cellular machine's routines, each word compiled into it, the native
//! convention's procedures and stubs) appends a line to FILE, and code
//! moved by a collection appends its new place:
//!
//! ```text
//! START LEN NAME
//! ```
//!
//! START the first address, in hex; LEN its length in bytes; NAME the rest
//! of the line. `%p` in FILE is the process's id, for runs that start
//! processes of their own (`cargo test`, the CLI's tests). macOS's
//! `sample` shows our code as `???` and an address; `fixpt-symbolize FILE
//! SAMPLE` (in `fixpt-tools`) names it. Code is collected and its room
//! used again, so an address may have had several names over a run: the
//! symbolizer gives every one.
//!
//! With `FIXPT_PERF_MAP` set (to anything), the same lines go to
//! `/tmp/perf-PID.map` as Linux's `perf` reads them, LEN in hex too, so
//! `perf report` names our code. Both may be set at once. Perf knows no
//! time of a name, so where room was used again it gives one of the names.
//!
//! Every note also goes to `gdb` and `lldb`, through the GDB JIT interface
//! (`crate::jitdebug`), unless `FIXPT_JIT_DEBUG` is `0`.

use std::io::Write;
use std::sync::{Mutex, OnceLock};

/// The files written to: `FIXPT_SYMBOLS`'s, and the perf map, each with
/// whether its lengths are in hex.
fn files() -> &'static [(Mutex<std::fs::File>, bool)] {
    static FILES: OnceLock<Vec<(Mutex<std::fs::File>, bool)>> = OnceLock::new();
    FILES.get_or_init(|| {
        let pid = std::process::id().to_string();
        let symbols = std::env::var("FIXPT_SYMBOLS").ok().map(|p| (p.replace("%p", &pid), false, "FIXPT_SYMBOLS"));
        let perf = std::env::var_os("FIXPT_PERF_MAP").map(|_| (format!("/tmp/perf-{pid}.map"), true, "FIXPT_PERF_MAP"));
        symbols
            .into_iter()
            .chain(perf)
            .filter_map(|(path, hex, var)| match std::fs::OpenOptions::new().create(true).append(true).open(&path) {
                Ok(f) => Some((Mutex::new(f), hex)),
                Err(e) => {
                    eprintln!("{var}: cannot open {path}: {e}");
                    None
                }
            })
            .collect()
    })
}

/// Whether names are being written: to make a name only when they are.
pub fn enabled() -> bool {
    crate::jitdebug::enabled() || !files().is_empty()
}

/// `len` bytes of machine code at `start` are `name`'s, from now on.
pub fn note(start: usize, len: usize, name: &str) {
    note_lines(start, len, name, None);
}

/// The same, and where its code came from (`jitdebug::Piece::lines`).
pub fn note_lines(start: usize, len: usize, name: &str, lines: Option<(u32, Vec<(u32, i64)>)>) {
    let name = name.replace('\n', " ");
    if crate::jitdebug::enabled() {
        // Code a call enters, the return address on the stack's top: its
        // frames can be known (`crate::cfi`).
        let called = name.starts_with("native ") && !name.ends_with("stack cache underflow") && !name.ends_with("a mark's return");
        crate::jitdebug::register(&crate::jitdebug::Piece { start, len, name: &name, called, lines });
    }
    for (f, hex) in files() {
        if let Ok(mut f) = f.lock() {
            let _ = if *hex { writeln!(f, "{start:x} {len:x} {name}") } else { writeln!(f, "{start:x} {len} {name}") };
        }
    }
}
