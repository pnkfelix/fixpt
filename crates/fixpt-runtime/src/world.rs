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
    /// The programs it started (`process-start`), by number.
    pub processes: Vec<Process>,
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

/// A program started beside this one (Heist's, `FIXPT-CHANGES.md` F4): its
/// standard output and error, one pipe, read by a thread of its own into
/// `output`, so that asking never waits; and its input.
pub struct Process {
    child: std::process::Child,
    input: Option<std::process::ChildStdin>,
    output: std::sync::Arc<std::sync::Mutex<Output>>,
    status: Option<std::process::ExitStatus>,
}

/// What a process's reader has read and not yet been taken, and whether
/// the pipe has ended.
#[derive(Default)]
struct Output {
    bytes: Vec<u8>,
    ended: bool,
}

/// How a process is.
pub enum ProcessStatus {
    Running,
    Exited(i32),
    Signalled(i32),
    Unknown,
}

impl World {
    /// Program `argv[0]` started with arguments `argv[1..]`, in directory
    /// `dir` (the working directory if empty), in a session of its own
    /// (`tty::new_session`): no terminal of its own, so that it never takes
    /// this program's, and a group a signal reaches what it starts through.
    /// Its number.
    pub fn process_start(&mut self, argv: &[String], dir: &str) -> std::io::Result<i64> {
        let Some((program, args)) = argv.split_first() else {
            return Err(std::io::Error::new(std::io::ErrorKind::InvalidInput, "no program named"));
        };
        let (reader, writer) = std::io::pipe()?;
        let mut command = std::process::Command::new(program);
        command.args(args).stdin(std::process::Stdio::piped()).stdout(writer.try_clone()?).stderr(writer);
        crate::tty::new_session(&mut command);
        if !dir.is_empty() {
            command.current_dir(dir);
        }
        let mut child = command.spawn()?;
        // The writer's copies went with `command`: the pipe ends when the
        // program's (and its children's) do.
        drop(command);
        let input = child.stdin.take();
        let output = std::sync::Arc::new(std::sync::Mutex::new(Output::default()));
        let out = output.clone();
        std::thread::spawn(move || {
            use std::io::Read as _;
            let mut reader = reader;
            let mut buf = [0u8; 8192];
            loop {
                match reader.read(&mut buf) {
                    Ok(0) | Err(_) => break,
                    Ok(n) => out.lock().unwrap().bytes.extend_from_slice(&buf[..n]),
                }
            }
            out.lock().unwrap().ended = true;
        });
        self.processes.push(Process { child, input, output, status: None });
        Ok(self.processes.len() as i64 - 1)
    }

    fn process(&mut self, p: i64) -> Option<&mut Process> {
        usize::try_from(p).ok().and_then(|p| self.processes.get_mut(p))
    }

    /// What process `p` has written since last asked, as text: a character
    /// cut by the read waits for the rest, and bytes not UTF-8 are U+FFFD.
    pub fn process_output(&mut self, p: i64) -> String {
        let Some(proc) = self.process(p) else { return String::new() };
        let mut out = proc.output.lock().unwrap();
        let bytes = std::mem::take(&mut out.bytes);
        let keep = if out.ended { 0 } else { incomplete_tail(&bytes) };
        let (text, rest) = bytes.split_at(bytes.len() - keep);
        out.bytes = rest.to_vec();
        String::from_utf8_lossy(text).into_owned()
    }

    /// Whether process `p` runs: it has ended once it has exited and its
    /// output has all been read, so that a last `process_output` after
    /// gives the rest.
    pub fn process_status(&mut self, p: i64) -> ProcessStatus {
        use std::os::unix::process::ExitStatusExt as _;
        let Some(proc) = self.process(p) else { return ProcessStatus::Unknown };
        if proc.status.is_none() {
            proc.status = proc.child.try_wait().ok().flatten();
        }
        match proc.status {
            Some(s) if proc.output.lock().unwrap().ended => match (s.code(), s.signal()) {
                (Some(c), _) => ProcessStatus::Exited(c),
                (None, Some(sig)) => ProcessStatus::Signalled(sig),
                (None, None) => ProcessStatus::Unknown,
            },
            _ => ProcessStatus::Running,
        }
    }

    /// `bytes` written to process `p`'s input.
    pub fn process_write(&mut self, p: i64, bytes: &[u8]) -> std::io::Result<()> {
        use std::io::Write as _;
        match self.process(p).and_then(|proc| proc.input.as_mut()) {
            Some(input) => input.write_all(bytes).and_then(|()| input.flush()),
            None => Err(std::io::Error::new(std::io::ErrorKind::BrokenPipe, "the process's input is closed")),
        }
    }

    /// Process `p`'s input closed: it reads its end.
    pub fn process_close_input(&mut self, p: i64) {
        if let Some(proc) = self.process(p) {
            proc.input = None;
        }
    }

    /// Signal `sig` sent to process `p`'s group, unless it has ended.
    pub fn process_signal(&mut self, p: i64, sig: i32) {
        if let Some(proc) = self.process(p)
            && proc.status.is_none()
        {
            crate::tty::signal_group(proc.child.id(), sig);
        }
    }
}

/// How many bytes at the end of `bytes` begin a UTF-8 character not yet
/// whole.
fn incomplete_tail(bytes: &[u8]) -> usize {
    for back in 1..=bytes.len().min(3) {
        let b = bytes[bytes.len() - back];
        if b & 0xC0 != 0x80 {
            let need = if b >= 0xF0 { 4 } else if b >= 0xE0 { 3 } else if b >= 0xC0 { 2 } else { 1 };
            return if need > back { back } else { 0 };
        }
    }
    0
}
