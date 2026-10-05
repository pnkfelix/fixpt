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
//! SAMPLE` (in `fixpt-tidy`) names it. Code is collected and its room
//! used again, so an address may have had several names over a run: the
//! symbolizer gives every one.

use std::io::Write;
use std::sync::{Mutex, OnceLock};

fn file() -> Option<&'static Mutex<std::fs::File>> {
    static FILE: OnceLock<Option<Mutex<std::fs::File>>> = OnceLock::new();
    FILE.get_or_init(|| {
        let path = std::env::var("FIXPT_SYMBOLS").ok()?.replace("%p", &std::process::id().to_string());
        match std::fs::OpenOptions::new().create(true).append(true).open(&path) {
            Ok(f) => Some(Mutex::new(f)),
            Err(e) => {
                eprintln!("FIXPT_SYMBOLS: cannot open {path}: {e}");
                None
            }
        }
    })
    .as_ref()
}

/// Whether names are being written: to make a name only when they are.
pub fn enabled() -> bool {
    file().is_some()
}

/// `len` bytes of machine code at `start` are `name`'s, from now on.
pub fn note(start: usize, len: usize, name: &str) {
    if let Some(f) = file()
        && let Ok(mut f) = f.lock()
    {
        let _ = writeln!(f, "{start:x} {len} {}", name.replace('\n', " "));
    }
}
