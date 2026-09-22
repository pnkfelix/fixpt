//! Reading a form from a person, as opposed to from a pipe.
//!
//! Both REPLs read through [`LineReader`], which picks its implementation by
//! asking whether stdin is a terminal:
//!
//! * **[`raw`]** — our own editor: arrow keys, `^A`/`^E`/`^K`/`^U`/`^W`,
//!   history that persists across sessions, and editing that works *across* the
//!   lines of an unfinished form.
//! * **Plain** — `read_line`, for a pipe or a file. Not a degraded mode but the
//!   correct one: writing cursor-movement escapes into a redirected stdout
//!   would corrupt it, and the test suite drives both REPLs through pipes.
//!
//! A REPL reads *forms*, not lines, so the multi-line rule lives here: `Enter`
//! submits when the form is balanced and inserts a newline when it is not. The
//! buffer being edited is the whole form, so you can arrow back up into the
//! first line of a `define` and fix it before submitting, and the form enters
//! history as one entry rather than as three fragments.
//!
//! # Why no line-editing crate
//!
//! `rustyline` would bring fifteen transitive crates, including `nix` and
//! `libc`, into a binary that has no external dependencies at all — and
//! `fixpt build` appends a heap image to a copy of this executable, so every
//! shipped program would carry a line editor it can never use.
//!
//! The one thing that genuinely needs the C library is putting the terminal in
//! raw mode, and the workspace denies `unsafe_code`. So [`raw::RawMode`] shells
//! out to `stty`, saving the old settings and restoring them on `Drop`. That is
//! a real wart, and it is the price of the property above.
//!
//! What we give up by not using a library: reverse search (`^R`), bracketed
//! paste, correct redrawing of lines longer than the terminal is wide, and
//! Windows. Each is additive if it turns out to matter.

use fixpt_read::{FormStatus, SyntaxProfile};
use std::io::{BufRead, Write};

/// Is this text a whole form yet?
///
/// Asked of the *real* reader, never of a paren counter kept here. The REPL
/// used to count parentheses itself, which meant it did not know that the `)`
/// in `#| ) |#` or in `|a(b|` is not a delimiter — it would submit a truncated
/// form and report a syntax error for input that was perfectly good. Anything
/// that has to decide where a datum ends has to be the reader, because that is
/// where the rules live.
fn complete(text: &str, profile: SyntaxProfile) -> bool {
    !matches!(fixpt_read::form_status(text, profile), FormStatus::Incomplete)
}

/// What one read produced.
pub enum Line {
    /// A complete, balanced form.
    Form(String),
    /// `^C`: abandon what was typed and start again.
    Interrupted,
    /// `^D` on an empty line, or end of input.
    Eof,
}

pub struct LineReader {
    inner: Inner,
    profile: SyntaxProfile,
}

enum Inner {
    Plain,
    Raw(Box<raw::Editor>),
}

impl LineReader {
    /// `history` names the file under `$FIXPT_HISTORY_DIR` (default: the home
    /// directory) where this REPL's history is kept. The two languages get
    /// separate files, because recalling a Scheme form at an FX-91 prompt is
    /// never what you meant.
    pub fn new(history: &str, profile: SyntaxProfile) -> LineReader {
        use std::io::IsTerminal as _;
        let inner = if std::io::stdin().is_terminal() && std::io::stdout().is_terminal() {
            Inner::Raw(Box::new(raw::Editor::new(history)))
        } else {
            Inner::Plain
        };
        LineReader { inner, profile }
    }

    /// Offer these names to `Tab`. Called before each prompt, so a procedure
    /// defined a moment ago can be completed immediately.
    pub fn set_completions(&mut self, words: Vec<String>) {
        if let Inner::Raw(e) = &mut self.inner {
            e.words = words;
        }
    }

    /// Read one complete form. `prompt` starts it; `continuation` prefixes the
    /// remaining lines of a form that is not finished yet.
    pub fn read(&mut self, prompt: &str, continuation: &str) -> Line {
        match &mut self.inner {
            Inner::Plain => read_plain(prompt, continuation, self.profile),
            Inner::Raw(e) => e.read(prompt, continuation, self.profile),
        }
    }

    /// Persist history. Errors are ignored: failing to write a history file is
    /// never a reason to disturb the session.
    pub fn save(&mut self) {
        if let Inner::Raw(e) = &mut self.inner {
            e.save();
        }
    }
}

/// Where the cursor is on screen, and how far down the form reaches.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Layout {
    pub cursor_screen_row: usize,
    pub cursor_screen_col: usize,
    pub last_screen_row: usize,
}

/// Lay out a form in **screen rows**.
///
/// A logical line wider than the terminal occupies several rows, so counting
/// newlines — which this used to do — puts the cursor in the wrong place for
/// the rest of the session as soon as one line wraps. Pulled out of `render` so
/// it can be tested directly: it is pure arithmetic, and it is the part most
/// likely to be quietly wrong.
///
/// `line_widths` are in characters, one per logical line. `prompt` prefixes the
/// first, `continuation` the rest.
pub fn layout(
    line_widths: &[usize],
    prompt: usize,
    continuation: usize,
    width: usize,
    cursor_line: usize,
    cursor_col: usize,
) -> Layout {
    let width = width.max(1);
    let prefix = |i: usize| if i == 0 { prompt } else { continuation };
    // How many screen rows a logical line occupies. `n` characters fill
    // columns `0..n-1`, so the last one sits on row `(n-1)/width` — not
    // `n/width`, which overcounts by one whenever the line ends exactly at the
    // right margin.
    let rows_of = |i: usize| {
        let used = prefix(i) + line_widths[i];
        1 + used.saturating_sub(1) / width
    };

    let before: usize = (0..cursor_line).map(rows_of).sum();
    let used = prefix(cursor_line) + cursor_col;
    let total: usize = (0..line_widths.len()).map(rows_of).sum();
    Layout {
        cursor_screen_row: before + used / width,
        cursor_screen_col: used % width,
        last_screen_row: total.saturating_sub(1),
    }
}

/// Accumulate lines until the form is balanced. The prompts are still printed,
/// so a transcript of a piped session reads the way the session looked.
fn read_plain(prompt: &str, continuation: &str, profile: SyntaxProfile) -> Line {
    let stdin = std::io::stdin();
    let mut pending = String::new();
    loop {
        print!("{}", if pending.is_empty() { prompt } else { continuation });
        let _ = std::io::stdout().flush();
        let mut line = String::new();
        match stdin.lock().read_line(&mut line) {
            Ok(0) => {
                return if pending.trim().is_empty() { Line::Eof } else { Line::Form(pending) };
            }
            Ok(_) => {}
            Err(_) => return Line::Eof,
        }
        pending.push_str(&line);
        if pending.trim().is_empty() {
            pending.clear();
        } else if complete(&pending, profile) {
            return Line::Form(pending);
        }
    }
}

mod raw {
    //! The editor proper.

    use super::Line;
    use super::Layout;
    use fixpt_read::SyntaxProfile;
    use std::io::{Read, Write};
    use std::path::PathBuf;
    use std::process::{Command, Stdio};

    /// Terminal settings, restored when this is dropped.
    ///
    /// `stty -g` prints the current settings in a form `stty` itself accepts
    /// back, which is what makes the round trip work without knowing anything
    /// about `termios`. The format differs between platforms; it does not have
    /// to be understood, only returned.
    struct RawMode {
        saved: String,
    }

    impl RawMode {
        fn enable() -> Option<RawMode> {
            // `output()` gives the child a null stdin by default, and `stty`
            // needs the terminal, so inheritance is explicit here.
            let probe = Command::new("stty")
                .arg("-g")
                .stdin(Stdio::inherit())
                .stderr(Stdio::null())
                .output()
                .ok()?;
            if !probe.status.success() {
                return None;
            }
            let saved = String::from_utf8(probe.stdout).ok()?.trim().to_string();
            // `raw` rather than `-icanon -echo`: it also turns off signal
            // generation, so `^C` arrives as a byte we can act on instead of
            // killing the REPL. The cost is that output post-processing is off
            // too, so every newline below is written as `\r\n`.
            let ok = Command::new("stty")
                .args(["raw", "-echo"])
                .stderr(Stdio::null())
                .status()
                .ok()?
                .success();
            if !ok {
                return None;
            }
            Some(RawMode { saved })
        }
    }

    impl Drop for RawMode {
        fn drop(&mut self) {
            let _ = Command::new("stty").arg(&self.saved).stderr(Stdio::null()).status();
        }
    }

    /// One keystroke, after escape sequences have been decoded.
    enum Key {
        Char(char),
        Enter,
        Backspace,
        Delete,
        Left,
        Right,
        Up,
        Down,
        Home,
        End,
        KillToEnd,
        KillToStart,
        KillWord,
        Tab,
        Clear,
        Interrupt,
        EndOfFile,
        Ignored,
    }

    pub struct Editor {
        history: Vec<String>,
        path: Option<PathBuf>,
        pub words: Vec<String>,
        /// Screen rows between the top of the rendered form and the cursor, as
        /// of the last redraw. The next redraw starts by moving back up that
        /// many.
        cursor_row: usize,
        /// Terminal width, for the wrapping arithmetic.
        width: usize,
        /// Whether to emit colour at all.
        pub(crate) colour: bool,
    }

    /// The terminal's width, from `stty size`.
    ///
    /// Same route as raw mode, for the same reason: no `libc`, no `unsafe`.
    /// A terminal that will not say falls back to 80, which is wrong only for
    /// lines that would have wrapped anyway.
    fn terminal_width() -> usize {
        let out = Command::new("stty")
            .arg("size")
            .stdin(Stdio::inherit())
            .stderr(Stdio::null())
            .output()
            .ok();
        out.and_then(|o| {
            let text = String::from_utf8(o.stdout).ok()?;
            text.split_whitespace().nth(1)?.parse::<usize>().ok()
        })
        .filter(|w| *w > 0)
        .unwrap_or(80)
    }

    /// Should anything be coloured?
    ///
    /// `NO_COLOR` is honoured because it is the convention, and `TERM=dumb`
    /// because a terminal that says it cannot should be believed. Neither costs
    /// anything to check and both are the difference between a tool that
    /// behaves in a pipeline and one that does not.
    fn colour_wanted() -> bool {
        if std::env::var_os("NO_COLOR").is_some() {
            return false;
        }
        !matches!(std::env::var("TERM").as_deref(), Ok("dumb") | Err(_))
    }

    fn history_path(name: &str) -> Option<PathBuf> {
        let dir = std::env::var_os("FIXPT_HISTORY_DIR")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(PathBuf::from))?;
        Some(dir.join(name))
    }

    /// History entries may span lines, and the file keeps one per line, so
    /// newlines are escaped going out and unescaped coming back.
    fn escape(s: &str) -> String {
        s.replace('\\', "\\\\").replace('\n', "\\n")
    }

    fn unescape(s: &str) -> String {
        let mut out = String::with_capacity(s.len());
        let mut chars = s.chars();
        while let Some(c) = chars.next() {
            if c != '\\' {
                out.push(c);
                continue;
            }
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('\\') => out.push('\\'),
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            }
        }
        out
    }

    impl Editor {
        pub fn new(name: &str) -> Editor {
            let path = history_path(name);
            let history = path
                .as_ref()
                .and_then(|p| std::fs::read_to_string(p).ok())
                .map(|text| text.lines().filter(|l| !l.is_empty()).map(unescape).collect())
                .unwrap_or_default();
            Editor {
                history,
                path,
                words: Vec::new(),
                cursor_row: 0,
                width: terminal_width(),
                colour: colour_wanted(),
            }
        }

        pub fn save(&mut self) {
            let Some(path) = &self.path else { return };
            // Keep the file from growing without bound; the tail is what
            // anyone ever reaches for.
            let start = self.history.len().saturating_sub(1000);
            let body: String =
                self.history[start..].iter().map(|e| format!("{}\n", escape(e))).collect();
            let _ = std::fs::write(path, body);
        }

        pub fn read(
            &mut self,
            prompt: &str,
            continuation: &str,
            profile: SyntaxProfile,
        ) -> Line {
            let Some(_raw) = RawMode::enable() else {
                // No terminal control available: fall back rather than
                // pretending, so the session still works.
                return super::read_plain(prompt, continuation, profile);
            };
            let result = self.edit(prompt, continuation, profile);
            // The prompt line is finished with; move off it before the
            // terminal goes back to cooked mode.
            let mut out = std::io::stdout();
            let _ = out.write_all(b"\r\n");
            let _ = out.flush();
            if let Line::Form(text) = &result
                && !text.trim().is_empty()
                && self.history.last().map(String::as_str) != Some(text.as_str())
            {
                self.history.push(text.clone());
                self.save();
            }
            result
        }

        fn edit(&mut self, prompt: &str, continuation: &str, profile: SyntaxProfile) -> Line {
            let mut buf: Vec<char> = Vec::new();
            let mut cursor = 0usize;
            // `history.len()` means "editing something new"; anything less is a
            // recalled entry.
            let mut hist = self.history.len();
            // What was being typed before history navigation started, so that
            // coming back down restores it rather than losing it.
            let mut pending: Vec<char> = Vec::new();

            self.cursor_row = 0;
            self.render(prompt, continuation, &buf, cursor, profile, &self.words.clone());
            loop {
                let key = match read_key() {
                    Some(k) => k,
                    None => return Line::Eof,
                };
                match key {
                    Key::Char(c) => {
                        buf.insert(cursor, c);
                        cursor += 1;
                    }
                    Key::Enter => {
                        let text: String = buf.iter().collect();
                        if text.trim().is_empty() {
                            buf.clear();
                            cursor = 0;
                        } else if super::complete(&text, profile) {
                            // Complete, or wrong in a way more typing will not
                            // fix: either way the reader should have its say.
                            return Line::Form(text);
                        } else {
                            // Unfinished: keep editing, one line further down.
                            buf.insert(cursor, '\n');
                            cursor += 1;
                        }
                    }
                    Key::Backspace => {
                        if cursor > 0 {
                            cursor -= 1;
                            buf.remove(cursor);
                        }
                    }
                    Key::Delete => {
                        if cursor < buf.len() {
                            buf.remove(cursor);
                        }
                    }
                    Key::Left => cursor = cursor.saturating_sub(1),
                    Key::Right => cursor = (cursor + 1).min(buf.len()),
                    Key::Home => cursor = line_start(&buf, cursor),
                    Key::End => cursor = line_end(&buf, cursor),
                    Key::KillToEnd => {
                        let end = line_end(&buf, cursor);
                        buf.drain(cursor..end);
                    }
                    Key::KillToStart => {
                        let start = line_start(&buf, cursor);
                        buf.drain(start..cursor);
                        cursor = start;
                    }
                    Key::KillWord => {
                        let mut i = cursor;
                        while i > 0 && buf[i - 1].is_whitespace() {
                            i -= 1;
                        }
                        while i > 0 && !buf[i - 1].is_whitespace() {
                            i -= 1;
                        }
                        buf.drain(i..cursor);
                        cursor = i;
                    }
                    Key::Tab => self.complete(&mut buf, &mut cursor),
                    Key::Clear => {
                        let mut out = std::io::stdout();
                        let _ = out.write_all(b"\x1b[H\x1b[2J");
                        let _ = out.flush();
                        self.cursor_row = 0;
                    }
                    // Within a form that already spans lines, Up and Down move
                    // between those lines; history is what they mean only when
                    // there is nowhere left to go inside the form. That is the
                    // behaviour that lets a recalled `define` be edited.
                    Key::Up => {
                        if row_of(&buf, cursor) > 0 {
                            cursor = move_row(&buf, cursor, -1);
                        } else if hist > 0 {
                            if hist == self.history.len() {
                                pending = buf.clone();
                            }
                            hist -= 1;
                            buf = self.history[hist].chars().collect();
                            cursor = buf.len();
                        }
                    }
                    Key::Down => {
                        let rows = buf.iter().filter(|c| **c == '\n').count();
                        if row_of(&buf, cursor) < rows {
                            cursor = move_row(&buf, cursor, 1);
                        } else if hist < self.history.len() {
                            hist += 1;
                            buf = if hist == self.history.len() {
                                std::mem::take(&mut pending)
                            } else {
                                self.history[hist].chars().collect()
                            };
                            cursor = buf.len();
                        }
                    }
                    Key::Interrupt => return Line::Interrupted,
                    Key::EndOfFile => {
                        if buf.is_empty() {
                            return Line::Eof;
                        }
                        if cursor < buf.len() {
                            buf.remove(cursor);
                        }
                    }
                    Key::Ignored => {}
                }
                self.render(prompt, continuation, &buf, cursor, profile, &self.words.clone());
            }
        }

        /// `Tab`: extend as far as every candidate agrees, then list the rest.
        fn complete(&mut self, buf: &mut Vec<char>, cursor: &mut usize) {
            // A Scheme identifier runs back to the nearest delimiter: `-`, `?`,
            // `!` and `>` are ordinary constituents, so the usual word-boundary
            // rules would cut `vector-ref` in half.
            let start = buf[..*cursor]
                .iter()
                .rposition(|c| c.is_whitespace() || "()[]'`,\";".contains(*c))
                .map_or(0, |i| i + 1);
            let prefix: String = buf[start..*cursor].iter().collect();
            if prefix.is_empty() {
                return;
            }
            let mut hits: Vec<&String> =
                self.words.iter().filter(|w| w.starts_with(&prefix)).collect();
            hits.sort();
            hits.dedup();
            if hits.is_empty() {
                return;
            }
            let shared = common_prefix(&hits);
            if shared.len() > prefix.len() {
                buf.splice(start..*cursor, shared.chars());
                *cursor = start + shared.chars().count();
            } else if hits.len() > 1 {
                let mut out = std::io::stdout();
                let _ = out.write_all(b"\r\n");
                let names: Vec<&str> = hits.iter().map(|s| s.as_str()).collect();
                let _ = out.write_all(names.join("  ").as_bytes());
                let _ = out.write_all(b"\r\n");
                let _ = out.flush();
                self.cursor_row = 0;
            }
        }

        /// Repaint the whole form.
        ///
        /// Everything is written in one `write_all`, so the terminal never
        /// shows a half-drawn line.
        ///
        /// The arithmetic is in **screen rows**, not logical lines. A line
        /// wider than the terminal occupies several rows, and counting
        /// newlines instead — which this used to do — leaves the cursor in the
        /// wrong place for the rest of the session. `stty size` supplies the
        /// width, in keeping with how raw mode is already obtained.
        fn render(
            &mut self,
            prompt: &str,
            continuation: &str,
            buf: &[char],
            cursor: usize,
            profile: SyntaxProfile,
            words: &[String],
        ) {
            let width = self.width.max(8);
            let text: String = buf.iter().collect();
            let lines: Vec<&str> = text.split('\n').collect();
            let painted = self.paint(&text, cursor, profile, words);

            let mut out = String::new();
            if self.cursor_row > 0 {
                out.push_str(&format!("\x1b[{}A", self.cursor_row));
            }
            out.push('\r');
            // Erase downwards: the form may have got shorter.
            out.push_str("\x1b[J");

            // Emit the coloured text, line by line, with its prompt.
            let mut painted_lines = painted.split('\n');
            for i in 0..lines.len() {
                if i > 0 {
                    out.push_str("\r\n");
                }
                out.push_str(if i == 0 { prompt } else { continuation });
                out.push_str(painted_lines.next().unwrap_or(""));
            }

            // Where the cursor belongs, and where printing left it — both in
            // screen rows, both computed from the *logical* buffer so that the
            // colour escapes above cannot affect them.
            let widths: Vec<usize> = lines.iter().map(|l| l.chars().count()).collect();
            let Layout { cursor_screen_row, cursor_screen_col, last_screen_row } = super::layout(
                &widths,
                prompt.chars().count(),
                continuation.chars().count(),
                width,
                row_of(buf, cursor),
                cursor - line_start(buf, cursor),
            );

            if last_screen_row > cursor_screen_row {
                out.push_str(&format!("\x1b[{}A", last_screen_row - cursor_screen_row));
            }
            out.push('\r');
            if cursor_screen_col > 0 {
                out.push_str(&format!("\x1b[{cursor_screen_col}C"));
            }
            self.cursor_row = cursor_screen_row;

            let mut stdout = std::io::stdout();
            let _ = stdout.write_all(out.as_bytes());
            let _ = stdout.flush();
        }
    }

    fn common_prefix(words: &[&String]) -> String {
        let first = words[0];
        let mut len = first.chars().count();
        for w in &words[1..] {
            len = len.min(
                first.chars().zip(w.chars()).take_while(|(a, b)| a == b).count(),
            );
        }
        first.chars().take(len).collect()
    }

    fn row_of(buf: &[char], cursor: usize) -> usize {
        buf[..cursor].iter().filter(|c| **c == '\n').count()
    }

    fn line_start(buf: &[char], cursor: usize) -> usize {
        buf[..cursor].iter().rposition(|c| *c == '\n').map_or(0, |i| i + 1)
    }

    fn line_end(buf: &[char], cursor: usize) -> usize {
        buf[cursor..].iter().position(|c| *c == '\n').map_or(buf.len(), |i| cursor + i)
    }

    /// Move the cursor one row, keeping its column where the new row allows.
    fn move_row(buf: &[char], cursor: usize, delta: isize) -> usize {
        let start = line_start(buf, cursor);
        let col = cursor - start;
        if delta < 0 {
            if start == 0 {
                return cursor;
            }
            let prev_start = line_start(buf, start - 1);
            (prev_start + col).min(start - 1)
        } else {
            let end = line_end(buf, cursor);
            if end == buf.len() {
                return cursor;
            }
            let next_start = end + 1;
            (next_start + col).min(line_end(buf, next_start))
        }
    }

    /// One byte from the terminal, or `None` at end of input.
    fn read_byte() -> Option<u8> {
        let mut b = [0u8; 1];
        match std::io::stdin().lock().read(&mut b) {
            Ok(1) => Some(b[0]),
            _ => None,
        }
    }

    fn read_key() -> Option<Key> {
        let b = read_byte()?;
        Some(match b {
            0x01 => Key::Home,
            0x02 => Key::Left,
            0x03 => Key::Interrupt,
            0x04 => Key::EndOfFile,
            0x05 => Key::End,
            0x06 => Key::Right,
            0x08 | 0x7f => Key::Backspace,
            0x09 => Key::Tab,
            0x0b => Key::KillToEnd,
            0x0c => Key::Clear,
            0x0d | 0x0a => Key::Enter,
            0x0e => Key::Down,
            0x10 => Key::Up,
            0x15 => Key::KillToStart,
            0x17 => Key::KillWord,
            0x1b => read_escape()?,
            b if b < 0x20 => Key::Ignored,
            b => Key::Char(read_utf8(b)?),
        })
    }

    /// `ESC [ …` and `ESC O …`, which is how terminals send the arrow and
    /// navigation keys.
    fn read_escape() -> Option<Key> {
        let b = read_byte()?;
        match b {
            b'[' | b'O' => {}
            // A bare ESC, or a meta-key we do not act on.
            _ => return Some(Key::Ignored),
        }
        let c = read_byte()?;
        Some(match c {
            b'A' => Key::Up,
            b'B' => Key::Down,
            b'C' => Key::Right,
            b'D' => Key::Left,
            b'H' => Key::Home,
            b'F' => Key::End,
            b'0'..=b'9' => {
                // A numeric sequence: `ESC [ <n> ~`, with `<n>` possibly more
                // than one digit. Consume through the terminator either way, so
                // the tail never lands in the buffer as text.
                let mut n = (c - b'0') as u32;
                loop {
                    let d = read_byte()?;
                    match d {
                        b'0'..=b'9' => n = n * 10 + (d - b'0') as u32,
                        b'~' => break,
                        _ => return Some(Key::Ignored),
                    }
                }
                match n {
                    1 | 7 => Key::Home,
                    3 => Key::Delete,
                    4 | 8 => Key::End,
                    _ => Key::Ignored,
                }
            }
            _ => Key::Ignored,
        })
    }

    /// Finish a UTF-8 character whose first byte has already been read.
    fn read_utf8(first: u8) -> Option<char> {
        let extra = match first {
            0x00..=0x7f => 0,
            0xc0..=0xdf => 1,
            0xe0..=0xef => 2,
            0xf0..=0xf7 => 3,
            _ => return None,
        };
        let mut bytes = vec![first];
        for _ in 0..extra {
            bytes.push(read_byte()?);
        }
        std::str::from_utf8(&bytes).ok()?.chars().next()
    }
}

// ------------------------------------------------------------- highlighting

/// Colouring the form as it is typed.
///
/// Three things are shown, in rough order of how much they are worth:
///
/// * **an identifier that is not bound**, dimmed — so a typo is visible at the
///   keystroke that makes it, rather than after `Enter`. The list of bound
///   names is the same one `Tab` completes from;
/// * **the matching delimiter** for the one under the cursor, brightened;
/// * **strings, characters, numbers and comments**, so the shape of a form is
///   readable.
///
/// All of it comes from [`fixpt_read::tokens`] rather than from a scan written
/// here. That is the same discipline `form_status` imposed and for the same
/// reason: a `)` inside `#| … |#` or `|a(b|` is not a delimiter, and a
/// highlighter that decided otherwise would brighten the wrong one.
///
/// Cursor arithmetic is unaffected by any of this, because `render` computes
/// the cursor's position from the *logical* buffer and never from the string it
/// draws — a separation that was already there and is what makes colour nearly
/// free.
mod paint {
    pub const RESET: &str = "\x1b[0m";
    pub const DIM: &str = "\x1b[2m";
    pub const STRING: &str = "\x1b[32m";
    pub const NUMBER: &str = "\x1b[36m";
    pub const COMMENT: &str = "\x1b[90m";
    pub const UNBOUND: &str = "\x1b[31m";
    pub const MATCH: &str = "\x1b[1;33m";
}

impl raw::Editor {
    /// The buffer with colour escapes inserted.
    pub(crate) fn paint(
        &self,
        text: &str,
        cursor: usize,
        profile: fixpt_read::SyntaxProfile,
        words: &[String],
    ) -> String {
        use fixpt_read::TokenKind;
        if !self.colour {
            return text.to_string();
        }
        let toks = fixpt_read::tokens(text, profile);
        // `cursor` is a character index; the tokens speak in bytes.
        let cursor_byte = text
            .char_indices()
            .nth(cursor)
            .map_or(text.len(), |(b, _)| b);
        // A delimiter is matched whether the cursor sits on it or just after
        // it, which is where it lands having typed one.
        let pair = fixpt_read::match_delimiter(&toks, cursor_byte).or_else(|| {
            let before = text[..cursor_byte].char_indices().next_back().map(|(b, _)| b)?;
            fixpt_read::match_delimiter(&toks, before)
        });

        let mut out = String::with_capacity(text.len() * 2);
        for t in &toks {
            let body = &text[t.start..t.end];
            let highlighted = pair.is_some_and(|(o, c)| o.start == t.start || c.start == t.start);
            let colour = if highlighted {
                Some(paint::MATCH)
            } else {
                match t.kind {
                    TokenKind::Str => Some(paint::STRING),
                    TokenKind::Char | TokenKind::Number | TokenKind::Boolean => {
                        Some(paint::NUMBER)
                    }
                    TokenKind::Comment => Some(paint::COMMENT),
                    TokenKind::Quote | TokenKind::Hash => Some(paint::DIM),
                    // The one worth having: a name nothing has bound.
                    TokenKind::Symbol if !words.iter().any(|w| w == body) => {
                        Some(paint::UNBOUND)
                    }
                    _ => None,
                }
            };
            match colour {
                Some(c) => {
                    out.push_str(c);
                    out.push_str(body);
                    out.push_str(paint::RESET);
                }
                None => out.push_str(body),
            }
        }
        out
    }
}


#[cfg(test)]
mod layout_tests {
    use super::{layout, Layout};

    /// Nothing wraps: a screen row is a logical line, which is what the old
    /// arithmetic assumed and the only case it got right.
    #[test]
    fn short_lines_are_one_row_each() {
        let l = layout(&[5, 5, 5], 2, 2, 80, 1, 3);
        assert_eq!(
            l,
            Layout { cursor_screen_row: 1, cursor_screen_col: 5, last_screen_row: 2 }
        );
    }

    /// A line wider than the terminal occupies several rows, and everything
    /// after it moves down.
    #[test]
    fn a_wrapped_line_pushes_what_follows_down() {
        // Width 10, prompt 2. The first line is 18 characters, so with the
        // prompt it fills columns 0..19 — exactly two rows, not three.
        let l = layout(&[18, 3], 2, 2, 10, 1, 0);
        assert_eq!(l.cursor_screen_row, 2, "the second line starts on row 2");
        assert_eq!(l.cursor_screen_col, 2, "just past the continuation prompt");
        assert_eq!(l.last_screen_row, 2);
    }

    /// The cursor inside a wrapped line lands on the right row and column.
    #[test]
    fn the_cursor_follows_the_wrap() {
        // Width 10, prompt 2: columns 0..7 of the text are on row 0, and the
        // 8th character begins row 1.
        let at = |col| layout(&[30], 2, 2, 10, 0, col);
        assert_eq!(at(0).cursor_screen_row, 0);
        assert_eq!(at(7).cursor_screen_col, 9);
        assert_eq!(at(8).cursor_screen_row, 1, "column 8 has wrapped");
        assert_eq!(at(8).cursor_screen_col, 0);
        assert_eq!(at(18).cursor_screen_row, 2);
    }

    /// Degenerate inputs must not panic or produce nonsense, because they
    /// happen: a terminal that will not report its size, and an empty buffer.
    #[test]
    fn degenerate_cases() {
        assert_eq!(layout(&[0], 2, 2, 80, 0, 0).last_screen_row, 0);
        // A width of zero would divide by zero; it is clamped to one, so every
        // character is its own row: 2 of prompt plus 5 of text is 7 rows,
        // numbered 0..6.
        let l = layout(&[5], 2, 2, 0, 0, 3);
        assert_eq!(l.last_screen_row, 6);
        // An empty form has no rows below the first.
        assert_eq!(layout(&[0], 6, 6, 10, 0, 0).cursor_screen_col, 6);
    }
}
