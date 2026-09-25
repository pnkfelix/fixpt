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

use crate::session::{Session, SessionError};
use fixpt_heap::Value;

pub const SOURCE: &str = include_str!("eager-reader.scm");

pub struct EagerReader {
    /// Heap root: the states, newest first. State `i` has consumed `i`
    /// characters, so there is always one more state than characters.
    root: usize,
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
        if session.global_value("eager-start").is_none() {
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
    pub fn attach_starting(session: &mut Session, prefix: &str, start: &str) -> Result<EagerReader, SessionError> {
        let start = session.global_value(&format!("{prefix}{start}")).expect("the reader is loaded");
        let st = session.call(start, &[])?;
        let list = session.rt.heap.cons(st, Value::NULL);
        let root = session.rt.heap.push_root(list);
        Ok(EagerReader { root, fed: Vec::new(), prefix: prefix.to_string() })
    }

    /// One of the reader's procedures.
    fn proc(&self, session: &Session, name: &str) -> Value {
        session.global_value(&format!("{}{name}", self.prefix)).expect("the reader is loaded")
    }

    /// Bring the checkpoints in line with `text`, feeding what is new.
    pub fn sync(&mut self, session: &mut Session, text: &str) -> Result<(), SessionError> {
        let chars: Vec<char> = text.chars().collect();
        let same = self.fed.iter().zip(&chars).take_while(|(a, b)| a == b).count();
        // Back up: drop the states past the common prefix.
        let mut list = session.rt.heap.root_at(self.root);
        for _ in same..self.fed.len() {
            list = session.rt.heap.cdr(list);
        }
        session.rt.heap.set_root_at(self.root, list);
        self.fed.truncate(same);
        for &c in &chars[same..] {
            // Looked up afresh each time round: a call may collect, and the
            // collector moves objects, so a procedure held across a call is
            // a dangling pointer after it.
            let feed = self.proc(session, "eager-feed");
            let st = session.rt.heap.car(session.rt.heap.root_at(self.root));
            let next = session.call(feed, &[st, Value::char(c)])?;
            // The call may have collected: re-read the root, don't reuse `list`.
            let list = session.rt.heap.root_at(self.root);
            let list = session.rt.heap.cons(next, list);
            session.rt.heap.set_root_at(self.root, list);
            self.fed.push(c);
        }
        Ok(())
    }

    /// The reader's view of `text`. With `at_enter`, as though a newline had
    /// just been typed — which is what `Enter` is, and what ends a trailing
    /// symbol or number — without keeping that newline.
    pub fn status(&mut self, session: &mut Session, text: &str, at_enter: bool) -> Result<EagerStatus, SessionError> {
        self.sync(session, text)?;
        let mut st = session.rt.heap.car(session.rt.heap.root_at(self.root));
        if at_enter {
            let feed = self.proc(session, "eager-feed");
            st = session.call(feed, &[st, Value::char('\n')])?;
        }
        // Everything below takes `st` as an argument to a Scheme call, which
        // roots it; nothing holds it across a call except that way.
        let status = self.proc(session, "eager-status");
        let status = session.call(status, &[st])?;
        let status = session.rt.heap.symbol_name(status);
        match status.as_str() {
            "complete" => Ok(EagerStatus::Complete),
            "error" => {
                // Re-read `st`: the status call may have moved it.
                let st = self.latest(session, text, at_enter)?;
                let msg = self.proc(session, "eager-state-message");
                let pos = self.proc(session, "eager-state-position");
                let at = session.call(pos, &[st])?.as_fixnum() as usize;
                let st = self.latest(session, text, at_enter)?;
                let m = session.call(msg, &[st])?;
                Ok(EagerStatus::Invalid { at, message: session.rt.heap.string_to_rust(m) })
            }
            _ => {
                let st = self.latest(session, text, at_enter)?;
                let closers = self.proc(session, "eager-hole-closers");
                let c = session.call(closers, &[st])?;
                if c.is_false() {
                    Ok(EagerStatus::Incomplete)
                } else {
                    Ok(EagerStatus::Hole { closers: session.rt.heap.string_to_rust(c) })
                }
            }
        }
    }

    /// The newest state for `text`, re-derived after a call that may have
    /// collected. With `at_enter` the newline is fed again: states are values,
    /// so feeding the same one twice gives the same answer.
    fn latest(&mut self, session: &mut Session, text: &str, at_enter: bool) -> Result<Value, SessionError> {
        debug_assert_eq!(self.fed.len(), text.chars().count());
        let st = session.rt.heap.car(session.rt.heap.root_at(self.root));
        if !at_enter {
            return Ok(st);
        }
        let feed = self.proc(session, "eager-feed");
        session.call(feed, &[st, Value::char('\n')])
    }
}
