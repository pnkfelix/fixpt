//! What the checker reads from disk: a module file's text, or its `.fasl`,
//! each read (or tried) through here and counted, per thread. What a check
//! found may be kept and used again (`facts_cache`) only if it read nothing
//! here, depending on nothing but its text and the build: the module files
//! built in (`fx26:…`) are the build's.
//!
//! And, while a log is kept ([`log_begin`]), each file read or tried, with
//! what was read (`TODO.md` §189): what a heap dump is keyed by, so that a
//! change to any file its load read, not only those it was given, makes it
//! stale. For the whole process, not a thread: a load may read on another.

use std::cell::Cell;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

thread_local! {
    static READS: Cell<u64> = const { Cell::new(0) };
}

/// Each file read or tried since [`log_begin`], in order: its path, made
/// absolute, and the digest of what was read ([`digest`]), none if there
/// was nothing to read. None while no log is kept.
static LOG: Mutex<Option<Vec<(PathBuf, Option<u64>)>>> = Mutex::new(None);

/// Keep a log of every file read from here on, in place of any before.
pub fn log_begin() {
    *LOG.lock().unwrap_or_else(|e| e.into_inner()) = Some(Vec::new());
}

/// The log kept so far ([`log_begin`]); empty if none is kept.
pub fn logged() -> Vec<(PathBuf, Option<u64>)> {
    LOG.lock().unwrap_or_else(|e| e.into_inner()).clone().unwrap_or_default()
}

/// The digest a file's contents are logged by: [`logged`]'s, and what a
/// dump compares a file's contents now with.
pub fn digest(bytes: &[u8]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    ("fixpt-read", bytes).hash(&mut h);
    h.finish()
}

/// `at`, read as `bytes` (none if it could not be), logged if a log is kept.
fn log(at: &Path, bytes: Option<&[u8]>) {
    let mut log = LOG.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(log) = log.as_mut() {
        let at = std::path::absolute(at).unwrap_or_else(|_| at.to_path_buf());
        log.push((std::fs::canonicalize(&at).unwrap_or(at), bytes.map(digest)));
    }
}

/// A read from disk, or a try at one: counted.
fn note() {
    READS.with(|r| r.set(r.get() + 1));
}

/// The text of the file at `at`, read, the read counted (failed or not:
/// that there is none is what the check found too) and logged.
pub(crate) fn read_file(at: &Path) -> std::io::Result<String> {
    note();
    let r = std::fs::read_to_string(at);
    log(at, r.as_ref().ok().map(|t| t.as_bytes()));
    r
}

/// The file at `at`, mapped: counted and logged as [`read_file`] is.
pub(crate) fn map(at: &Path) -> std::io::Result<fixpt_heap::Mapped> {
    note();
    let r = fixpt_heap::Mapped::open(at);
    log(at, r.as_ref().ok().and_then(|b| b.get(..)));
    r
}

/// The reads so far on this thread: a check that read nothing leaves it as
/// it was.
pub(crate) fn count() -> u64 {
    READS.with(|r| r.get())
}
