//! What the checker reads from disk: a module file's text, or its `.fasl`,
//! each read (or tried) through here and counted, per thread. What a check
//! found may be kept and used again (`facts_cache`) only if it read nothing
//! here, depending on nothing but its text and the build: the module files
//! built in (`fx26:…`) are the build's.

use std::cell::Cell;

thread_local! {
    static READS: Cell<u64> = const { Cell::new(0) };
}

/// A read from disk, or a try at one: counted.
pub(crate) fn note() {
    READS.with(|r| r.set(r.get() + 1));
}

/// The text of the file at `at`, read, the read counted (failed or not:
/// that there is none is what the check found too).
pub(crate) fn read_file(at: &std::path::Path) -> std::io::Result<String> {
    note();
    std::fs::read_to_string(at)
}

/// The reads so far on this thread: a check that read nothing leaves it as
/// it was.
pub(crate) fn count() -> u64 {
    READS.with(|r| r.get())
}
