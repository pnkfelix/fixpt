//! Driving the eager reader (`eager-reader.scm`) from Rust.
//!
//! The reader is Scheme, and a checkpoint is one of its states: a suspended
//! parse, holding the composable continuation that is "the rest of the read".
//! [`EagerReader`] keeps one per character fed, in a single heap root, as a
//! Scheme list newest-first. Given the current text, it keeps the checkpoints
//! for the prefix that has not changed and feeds only the rest. Typing or
//! backspacing at the end is one feed or none; an edit in the middle re-feeds
//! from there. The characters themselves are never re-read from the start —
//! the thing `form_status` cannot avoid.

use crate::session::{Handle, Session, SessionError};
use fixpt_heap::Value;

pub const SOURCE: &str = include_str!("eager-reader.scm");

pub struct EagerReader {
    /// The states, newest first. State `i` has consumed `i` characters, so
    /// there is always one more state than characters.
    root: Handle,
    fed: Vec<char>,
    /// What the reader's procedures are called: `eager-start` and the rest,
    /// behind this prefix. Empty for the Scheme reader; `fx:` for the FX-26
    /// one, whose globals are lowered that way.
    prefix: String,
}

/// What the reader makes of the text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EagerStatus {
    Complete,
    Incomplete,
    /// Wrong at character `at` (an index into the text, in characters).
    Invalid { at: usize, message: String },
    /// Still inside lists, and the last thing read in the innermost one is a
    /// `,help` hole: `closers` would close them all.
    Hole { closers: String },
}

impl EagerReader {
    /// A reader with nothing fed. Loads the reader into the session the first
    /// time.
    pub fn new(session: &mut Session) -> Result<EagerReader, SessionError> {
        if !session.is_bound("eager-start") {
            session.eval_str("<eager-reader>", SOURCE)?;
        }
        EagerReader::attach(session, "")
    }

    /// Drive a reader already loaded into `session` whose procedures have the
    /// Scheme reader's names and meanings, behind `prefix`: the FX-26 reader
    /// (`fixpt_fx26::EAGER_READER`) is `fx:eager-start` and so on.
    pub fn attach(session: &mut Session, prefix: &str) -> Result<EagerReader, SessionError> {
        EagerReader::attach_starting(session, prefix, "eager-start")
    }

    /// The same, starting the reader with `start` rather than `eager-start`:
    /// the FX-26 reader reads FX-26's own lexical syntax from
    /// `eager-start-fx26`.
    ///
    /// The reader's handle is made here, outside any scope, so it lasts as
    /// long as the session's roots do; do not attach inside a
    /// `Session::scope`.
    pub fn attach_starting(session: &mut Session, prefix: &str, start: &str) -> Result<EagerReader, SessionError> {
        let st = session.call_global(&format!("{prefix}{start}"), &[])?;
        let root = session.make(|m| {
            let st = m.get(st);
            m.heap().cons(st, Value::NULL)
        });
        Ok(EagerReader { root, fed: Vec::new(), prefix: prefix.to_string() })
    }

    /// The global one of the reader's procedures is in.
    fn name(&self, name: &str) -> String {
        format!("{}{name}", self.prefix)
    }

    /// The newest state, as a handle in the current scope.
    fn newest(&self, session: &mut Session) -> Handle {
        let root = self.root;
        session.make(|m| {
            let list = m.get(root);
            m.heap().car(list)
        })
    }

    /// Bring the checkpoints in line with `text`, feeding what is new.
    pub fn sync(&mut self, session: &mut Session, text: &str) -> Result<(), SessionError> {
        let chars: Vec<char> = text.chars().collect();
        let same = self.fed.iter().zip(&chars).take_while(|(a, b)| a == b).count();
        // Back up: drop the states past the common prefix.
        let back = self.fed.len() - same;
        session.replace(self.root, |m| {
            let mut list = m.get(self.root);
            for _ in 0..back {
                list = m.heap().cdr(list);
            }
            list
        });
        self.fed.truncate(same);
        for &c in &chars[same..] {
            let root = self.root;
            let feed = self.name("eager-feed");
            session.scope(|s| -> Result<(), SessionError> {
                let st = self.newest(s);
                let ch = s.make(|_| Value::char(c));
                let next = s.call_global(&feed, &[st, ch])?;
                s.replace(root, |m| {
                    let (next, list) = (m.get(next), m.get(root));
                    m.heap().cons(next, list)
                });
                Ok(())
            })?;
            self.fed.push(c);
        }
        Ok(())
    }

    /// The reader's view of `text`. With `at_enter`, as though a newline had
    /// just been typed — which is what `Enter` is, and what ends a trailing
    /// symbol or number — without keeping that newline.
    pub fn status(&mut self, session: &mut Session, text: &str, at_enter: bool) -> Result<EagerStatus, SessionError> {
        self.sync(session, text)?;
        session.scope(|s| {
            let st = self.latest(s, at_enter)?;
            let status = s.call_global(&self.name("eager-status"), &[st])?;
            let status = s.view(|v| v.get(status).symbol_name().unwrap_or_default());
            match status.as_str() {
                "complete" => Ok(EagerStatus::Complete),
                "error" => {
                    let at = s.call_global(&self.name("eager-state-position"), &[st])?;
                    let m = s.call_global(&self.name("eager-state-message"), &[st])?;
                    s.view(|v| {
                        Ok(EagerStatus::Invalid {
                            at: v.get(at).fixnum().unwrap_or(0) as usize,
                            message: v.get(m).string().unwrap_or_default(),
                        })
                    })
                }
                _ => {
                    let c = s.call_global(&self.name("eager-hole-closers"), &[st])?;
                    s.view(|v| {
                        let c = v.get(c);
                        Ok(if c.is_false() {
                            EagerStatus::Incomplete
                        } else {
                            EagerStatus::Hole { closers: c.string().unwrap_or_default() }
                        })
                    })
                }
            }
        })
    }

    /// The reader's state after `text` (and a newline, if `at_enter`): for
    /// asking it things this type does not, by calling its procedures. A
    /// handle in the caller's scope.
    pub fn state_after(&mut self, session: &mut Session, text: &str, at_enter: bool) -> Result<Handle, SessionError> {
        self.sync(session, text)?;
        self.latest(session, at_enter)
    }

    fn latest(&self, session: &mut Session, at_enter: bool) -> Result<Handle, SessionError> {
        let st = self.newest(session);
        if !at_enter {
            return Ok(st);
        }
        let nl = session.make(|_| Value::char('\n'));
        session.call_global(&self.name("eager-feed"), &[st, nl])
    }
}
