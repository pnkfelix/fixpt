//! The standard input as a file descriptor, and the terminal it may be
//! (`TODO.md` §95): reads and waits that the scheduler can make without
//! blocking the others, raw mode and back, and the terminal's size. The
//! one place in this crate that calls the system directly.
#![allow(unsafe_code)]

use std::sync::Mutex;

const STDIN: libc::c_int = 0;

/// Bytes read from the standard input into `buf`: how many, 0 at its end.
pub fn read(buf: &mut [u8]) -> std::io::Result<usize> {
    loop {
        // SAFETY: `buf` is valid for writes of its length.
        let n = unsafe { libc::read(STDIN, buf.as_mut_ptr().cast(), buf.len()) };
        if n >= 0 {
            return Ok(n as usize);
        }
        let e = std::io::Error::last_os_error();
        if e.kind() != std::io::ErrorKind::Interrupted {
            return Err(e);
        }
    }
}

/// Whether a read of the standard input would not block (it has a byte,
/// or is at its end, or failed), waiting for that at most `ms`
/// milliseconds, or for ever if negative.
pub fn ready(ms: i32) -> bool {
    let mut p = libc::pollfd { fd: STDIN, events: libc::POLLIN, revents: 0 };
    loop {
        // SAFETY: one `pollfd`, valid for the call.
        let n = unsafe { libc::poll(&mut p, 1, ms) };
        if n >= 0 {
            return n > 0;
        }
        if std::io::Error::last_os_error().kind() != std::io::ErrorKind::Interrupted {
            return true;
        }
    }
}

/// Whether the standard input is a terminal.
pub fn is_terminal() -> bool {
    // SAFETY: no memory is passed.
    unsafe { libc::isatty(STDIN) == 1 }
}

/// The terminal's modes as they were before the program first asked for
/// raw mode, to put back.
static SAVED: Mutex<Option<libc::termios>> = Mutex::new(None);

fn modes() -> std::io::Result<libc::termios> {
    // SAFETY: a `termios` is plain data, which `tcgetattr` fills.
    let mut t: libc::termios = unsafe { std::mem::zeroed() };
    // SAFETY: `t` is valid for the call.
    if unsafe { libc::tcgetattr(STDIN, &mut t) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(t)
}

fn set_modes(t: &libc::termios) -> std::io::Result<()> {
    // SAFETY: `t` is valid for the call.
    if unsafe { libc::tcsetattr(STDIN, libc::TCSAFLUSH, t) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(())
}

/// The terminal in raw mode: no echo, no line editing, each key as it
/// comes, ^C, ^Z and ^\ keys rather than signals, no flow control, a
/// carriage return not made a newline. Output is as before (a newline
/// still begins the next line). The modes before saved, the first time.
pub fn raw() -> std::io::Result<()> {
    let t = modes()?;
    let mut saved = SAVED.lock().unwrap_or_else(|p| p.into_inner());
    if saved.is_none() {
        *saved = Some(t);
    }
    let mut r = t;
    r.c_iflag &= !(libc::BRKINT | libc::ICRNL | libc::INPCK | libc::ISTRIP | libc::IXON);
    r.c_cflag |= libc::CS8;
    r.c_lflag &= !(libc::ECHO | libc::ICANON | libc::IEXTEN | libc::ISIG);
    r.c_cc[libc::VMIN] = 1;
    r.c_cc[libc::VTIME] = 0;
    set_modes(&r)
}

/// The terminal's modes as they were before raw mode, if it was asked for;
/// whether it was.
pub fn restore() -> std::io::Result<bool> {
    let saved = SAVED.lock().unwrap_or_else(|p| p.into_inner()).take();
    match saved {
        Some(t) => set_modes(&t).map(|()| true),
        None => Ok(false),
    }
}

/// The terminal's size, rows and columns.
pub fn size() -> std::io::Result<(u16, u16)> {
    // SAFETY: a `winsize` is plain data, which the call fills.
    let mut w: libc::winsize = unsafe { std::mem::zeroed() };
    // SAFETY: `w` is valid for the call, which takes a `winsize`.
    if unsafe { libc::ioctl(STDIN, libc::TIOCGWINSZ, &mut w) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok((w.ws_row, w.ws_col))
}
