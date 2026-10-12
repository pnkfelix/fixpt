//! The world outside an FX-26 program, as its I/O primitives see it
//! (`TODO.md` §84): the standard streams, the command-line arguments, and
//! the status the program asked to exit with.
//!
//! A `World` is either the process's own (`fixpt run`, `fixpt eval`), whose
//! writes go straight to the standard output and error, or captured, whose
//! writes are kept for a test to read. The program cannot tell which: both
//! answer every primitive alike.

use std::io::Write as _;

/// The program's world: real, or captured for a test.
#[derive(Default)]
pub struct World {
    /// Whether writes are kept here rather than written to the process's
    /// streams.
    pub captured: bool,
    /// What a captured world's program wrote to its standard output.
    pub stdout: Vec<u8>,
    /// And to its standard error.
    pub stderr: Vec<u8>,
    /// The program's command-line arguments, its own (not `fixpt`'s).
    pub args: Vec<String>,
    /// The status `exit` asked for, once it has: the run then stops, and
    /// whoever ran the program ends with it.
    pub exit: Option<i32>,
}

/// One of the standard streams a program writes.
#[derive(Clone, Copy)]
pub enum Stream {
    Stdout,
    Stderr,
}

impl World {
    /// A world whose writes are kept, for a test.
    pub fn captured() -> World {
        World { captured: true, ..World::default() }
    }

    /// `bytes` written whole to `stream`, and flushed, so that what the
    /// program writes to its two streams interleaves as it wrote them.
    pub fn write(&mut self, stream: Stream, bytes: &[u8]) -> std::io::Result<()> {
        match (self.captured, stream) {
            (true, Stream::Stdout) => {
                self.stdout.extend_from_slice(bytes);
                Ok(())
            }
            (true, Stream::Stderr) => {
                self.stderr.extend_from_slice(bytes);
                Ok(())
            }
            (false, Stream::Stdout) => {
                let mut out = std::io::stdout().lock();
                out.write_all(bytes)?;
                out.flush()
            }
            (false, Stream::Stderr) => {
                let mut err = std::io::stderr().lock();
                err.write_all(bytes)?;
                err.flush()
            }
        }
    }
}

/// An I/O error's kind, as FX-26's `io-error` names it (`check::IO_ERROR`):
/// the label of its `kind`, a sum of units.
pub fn error_kind(e: &std::io::Error) -> &'static str {
    use std::io::ErrorKind as K;
    match e.kind() {
        K::NotFound => "not-found",
        K::PermissionDenied => "permission-denied",
        K::AlreadyExists => "already-exists",
        K::NotADirectory => "not-a-directory",
        K::IsADirectory => "is-a-directory",
        K::BrokenPipe => "broken-pipe",
        K::InvalidData => "invalid-data",
        _ => "other",
    }
}
