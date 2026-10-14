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
    /// A captured world's standard input, and how much of it is read; for
    /// the process's own, what has been read from it and not yet taken,
    /// so that reads by lines and by bytes take from one stream.
    pub stdin: Vec<u8>,
    pub stdin_at: usize,
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

/// What `read_line` found.
pub enum Line {
    Text(String),
    Eof,
}

impl World {
    /// The standard input's bytes not yet taken, read from it if there are
    /// none (waiting for one): none only at its end.
    fn buffered(&mut self) -> std::io::Result<&[u8]> {
        if self.stdin_at == self.stdin.len() && !self.captured {
            let mut buf = [0u8; 4096];
            let n = crate::tty::read(&mut buf)?;
            self.stdin.clear();
            self.stdin_at = 0;
            self.stdin.extend_from_slice(&buf[..n]);
        }
        Ok(&self.stdin[self.stdin_at..])
    }

    /// The next line of the standard input, its ending (`\n` or `\r\n`)
    /// left off; the last may have none. A line that is not UTF-8 is an
    /// error of kind `invalid-data`, and is read all the same.
    pub fn read_line(&mut self) -> std::io::Result<Line> {
        let mut bytes = Vec::new();
        loop {
            let rest = self.buffered()?;
            if rest.is_empty() {
                break;
            }
            let (n, done) = rest.iter().position(|b| *b == b'\n').map_or((rest.len(), false), |i| (i + 1, true));
            bytes.extend_from_slice(&rest[..n]);
            self.stdin_at += n;
            if done {
                break;
            }
        }
        if bytes.is_empty() {
            return Ok(Line::Eof);
        }
        if bytes.last() == Some(&b'\n') {
            bytes.pop();
            if bytes.last() == Some(&b'\r') {
                bytes.pop();
            }
        }
        String::from_utf8(bytes)
            .map(Line::Text)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("a line that is not UTF-8, from byte {}", e.utf8_error().valid_up_to())))
    }

    /// The next byte of the standard input, waiting for one; none at its
    /// end.
    pub fn read_byte(&mut self) -> std::io::Result<Option<u8>> {
        let b = self.buffered()?.first().copied();
        self.stdin_at += b.is_some() as usize;
        Ok(b)
    }

    /// At most `n` bytes of the standard input, at least one, waiting for
    /// one, then as many as have come; none at its end.
    pub fn read_bytes(&mut self, n: usize) -> std::io::Result<Vec<u8>> {
        let rest = self.buffered()?;
        let k = rest.len().min(n);
        let out = rest[..k].to_vec();
        self.stdin_at += k;
        Ok(out)
    }

    /// Whether a read of the standard input would not wait: a byte has
    /// come, or it is at its end. A captured one never waits.
    pub fn stdin_ready(&mut self) -> bool {
        self.captured || self.stdin_at < self.stdin.len() || crate::tty::ready(0)
    }

    /// Wait until a read of the standard input would not, or until the
    /// clock reaches `until` (`clock_ns`), if given; whether it would not.
    pub fn wait_stdin(&mut self, until: Option<i64>) -> bool {
        if self.stdin_ready() {
            return true;
        }
        let ms = until.map_or(-1, |t| ((t - clock_ns()).max(0) as u64).div_ceil(1_000_000).min(i32::MAX as u64) as i32);
        crate::tty::ready(ms)
    }

    /// The terminal the standard input is, put in raw mode (`tty::raw`):
    /// none if it is no terminal.
    pub fn terminal_raw(&mut self) -> Option<std::io::Result<()>> {
        (!self.captured && crate::tty::is_terminal()).then(crate::tty::raw)
    }

    /// The terminal's modes as before raw mode: none if it is no terminal.
    pub fn terminal_restore(&mut self) -> Option<std::io::Result<()>> {
        (!self.captured && crate::tty::is_terminal()).then(|| crate::tty::restore().map(|_| ()))
    }

    /// The terminal's rows and columns: none if it is no terminal.
    pub fn terminal_size(&mut self) -> Option<std::io::Result<(u16, u16)>> {
        (!self.captured && crate::tty::is_terminal()).then(crate::tty::size)
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

/// The names in directory `path`, sorted by their bytes; one that is not
/// UTF-8 is an error of kind `invalid-data`, since FX-26's strings are.
pub fn list_dir(path: &str) -> std::io::Result<Vec<String>> {
    let mut names = Vec::new();
    for entry in std::fs::read_dir(path)? {
        let name = entry?.file_name();
        match name.into_string() {
            Ok(n) => names.push(n),
            Err(n) => {
                return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, format!("a name that is not UTF-8: {n:?}")));
            }
        }
    }
    names.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    Ok(names)
}

/// File `path` replaced by `bytes` whole, atomically: written to a file
/// beside it, flushed to the disk, and renamed over it, so that a reader
/// sees the old contents or the new, never part of either.
pub fn replace_file(path: &str, bytes: &[u8]) -> std::io::Result<()> {
    let target = std::path::Path::new(path);
    let name = target.file_name().ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidInput, format!("no file name in {path:?}")))?;
    let mut temp_name = std::ffi::OsString::from(".");
    temp_name.push(name);
    temp_name.push(format!(".fixpt-{}.tmp", std::process::id()));
    let temp = target.with_file_name(temp_name);
    let written = (|| {
        let mut f = std::fs::File::create(&temp)?;
        f.write_all(bytes)?;
        f.sync_all()
    })();
    match written.and_then(|()| std::fs::rename(&temp, target)) {
        Ok(()) => Ok(()),
        Err(e) => {
            let _ = std::fs::remove_file(&temp);
            Err(e)
        }
    }
}

/// Nanoseconds since the first time this was asked, by the monotonic
/// clock: what FX-26's `clock` gives, so its zero is near the run's start.
pub fn clock_ns() -> i64 {
    static START: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
    let start = *START.get_or_init(std::time::Instant::now);
    i64::try_from(start.elapsed().as_nanos()).unwrap_or(i64::MAX)
}

/// Sleep until `clock_ns` reaches `t`; at once if it has.
pub fn sleep_until(t: i64) {
    let now = clock_ns();
    if t > now {
        std::thread::sleep(std::time::Duration::from_nanos((t - now) as u64));
    }
}
