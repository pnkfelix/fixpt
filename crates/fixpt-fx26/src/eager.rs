//! The eager reader written in FX-26 (`eager-reader.fx`), driven from Rust
//! as the REPL reads what is typed: run compiled with the rest of the front
//! end, its entry points called as the front end's are (`crate::entries`),
//! once its licence is checked (`session::reader_licensed`). No Scheme: as
//! `fixpt_scheme::eager::EagerReader` drives Scheme's own reader on its
//! engine, this drives FX-26's. A state per character fed, newest first, in
//! one root: given the text, the states of the prefix that has not changed
//! are kept, and only the rest is fed.

use crate::front::Front;
use crate::session::Fx26Session;
use fixpt_heap::Value;
use fixpt_scheme::Handle;

/// What the reader makes of the text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Status {
    Complete,
    Incomplete,
    /// Wrong at character `at` (an index into the text, in characters).
    Invalid { at: usize, message: String },
    /// Still inside lists, and the last thing read in the innermost one is a
    /// `,help` hole: `closers` would close them all.
    Hole { closers: String },
}

pub struct Eager {
    /// The states, newest first: state `i` has read `i` characters.
    root: Handle,
    fed: Vec<char>,
}

impl Eager {
    /// A reader with nothing fed, in `s`'s front end, its licence checked.
    /// Its handle is made outside any scope, to last as the session's roots
    /// do: not to be made inside a `scope`.
    pub fn start(s: &mut Fx26Session) -> Result<Eager, String> {
        crate::session::reader_licensed()?;
        s.load_own_pieces().map_err(|e| String::from(e.message))?;
        let st = crate::entries::call(&mut s.scheme, "eager-start-fx26", &[]).map_err(|e| e.to_string())?;
        let root = s.scheme.make(|m| {
            let st = m.get(st);
            m.heap().cons(st, Value::NULL)
        });
        Ok(Eager { root, fed: Vec::new() })
    }

    /// The newest state, as a handle in the current scope.
    fn newest(&self, f: &mut Front) -> Handle {
        let root = self.root;
        f.make(|m| {
            let list = m.get(root);
            m.heap().car(list)
        })
    }

    /// The states brought in line with `text`, what is new fed.
    pub fn sync(&mut self, f: &mut Front, text: &str) -> Result<(), String> {
        let chars: Vec<char> = text.chars().collect();
        let same = self.fed.iter().zip(&chars).take_while(|(a, b)| a == b).count();
        let back = self.fed.len() - same;
        let root = self.root;
        f.replace(root, |m| {
            let mut list = m.get(root);
            for _ in 0..back {
                list = m.heap().cdr(list);
            }
            list
        });
        self.fed.truncate(same);
        for &c in &chars[same..] {
            f.scope(|f| -> Result<(), String> {
                let st = self.newest(f);
                let ch = f.make(|_| Value::char(c));
                let next = crate::entries::call(f, "eager-feed", &[st, ch]).map_err(|e| e.to_string())?;
                f.replace(root, |m| {
                    let (next, list) = (m.get(next), m.get(root));
                    m.heap().cons(next, list)
                });
                Ok(())
            })?;
            self.fed.push(c);
        }
        Ok(())
    }

    /// The reader's view of `text`; with `at_enter`, as though a newline
    /// had just been typed (what `Enter` is, and what ends a trailing symbol
    /// or number), that newline not kept.
    pub fn status(&mut self, f: &mut Front, text: &str, at_enter: bool) -> Result<Status, String> {
        self.sync(f, text)?;
        f.scope(|f| {
            let call = |f: &mut Front, name: &str, args: &[Handle]| crate::entries::call(f, name, args).map_err(|e| e.to_string());
            let mut st = self.newest(f);
            if at_enter {
                let nl = f.make(|_| Value::char('\n'));
                st = call(f, "eager-feed", &[st, nl])?;
            }
            let status = call(f, "eager-status", &[st])?;
            let status = f.view(|v| v.get(status).symbol_name().unwrap_or_default());
            Ok(match status.as_str() {
                "complete" => Status::Complete,
                "error" => {
                    let at = call(f, "eager-state-position", &[st])?;
                    let m = call(f, "eager-state-message", &[st])?;
                    f.view(|v| Status::Invalid { at: v.get(at).fixnum().unwrap_or(0) as usize, message: v.get(m).string().unwrap_or_default() })
                }
                _ => {
                    let c = call(f, "eager-hole-closers", &[st])?;
                    f.view(|v| {
                        let c = v.get(c);
                        if c.is_false() { Status::Incomplete } else { Status::Hole { closers: c.string().unwrap_or_default() } }
                    })
                }
            })
        })
    }
}
