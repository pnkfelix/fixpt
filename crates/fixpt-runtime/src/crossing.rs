//! Continuations that cross machines (`TODO.md` §93): native code calls
//! cellular code it declined to compile, which calls native code, and so
//! on, each machine with frames of its own. A capture up to a prompt that
//! one of the machines out from the capturing one set takes each machine's
//! frames in turn, innermost first, through the calls between them.
//!
//! While a machine is in a call of another machine's code it is a
//! *boundary* here, innermost last; the calls nest strictly, so the
//! innermost boundary is the call of the machine running. Each segment of
//! a crossing continuation is a continuation of its own machine's frames
//! with the segment inside it as its *inner* one: given a value, the
//! segment puts its frames back, then calls its inner one with the value,
//! where the call between the two machines was, and resumes with what that
//! returns.

use std::cell::RefCell;
use std::rc::Rc;

use fixpt_heap::Value;

use crate::Runtime;

/// What a boundary's frames gave a capture: up to the prompt, which they
/// held; or all of them, the prompt further out; or nothing, the prompt
/// not there and no machine calling theirs.
pub enum Crossed {
    Found(Value),
    Beyond(Value),
    Missing,
}

/// A machine in a call of another's code (`across`).
pub trait Crossing {
    /// Its frames, from the call out to a prompt for `tag` or its own
    /// first frame, with `inner` inside.
    fn capture(&self, rt: &mut Runtime, tag: Value, inner: Value) -> Crossed;
    /// All its frames, from the call out, with `inner` inside: if it is
    /// the bottom machine, as a whole continuation of them, which replaces
    /// its frames when given a value.
    fn capture_whole(&self, rt: &mut Runtime, bottom: bool, inner: Value) -> Value;
    /// The marks for `key` in its frames, from the call out, innermost
    /// first; and whether a machine called it, whose frames are further out.
    fn marks(&self, rt: &mut Runtime, key: Value) -> (Vec<Value>, bool);
}

pub type Boundary = Rc<dyn Crossing>;

thread_local! {
    static BOUNDARIES: RefCell<Vec<Boundary>> = const { RefCell::new(Vec::new()) };
}

/// A boundary entered, for the length of the call that `f` makes.
pub fn across<T>(b: Boundary, f: impl FnOnce() -> T) -> T {
    BOUNDARIES.with(|v| v.borrow_mut().push(b));
    let out = f();
    BOUNDARIES.with(|v| v.borrow_mut().pop());
    out
}

/// Whether a machine calls the one running.
pub fn crossed() -> bool {
    BOUNDARIES.with(|v| !v.borrow().is_empty())
}

/// The continuation up to the innermost prompt for `tag` past the machine
/// running, whose own frames, all of them, are `own`; none if no machine
/// out from it has one.
pub fn capture(rt: &mut Runtime, tag: Value, own: Value) -> Option<Value> {
    let n = BOUNDARIES.with(|v| v.borrow().len());
    let mut inner = own;
    for i in (0..n).rev() {
        let b = BOUNDARIES.with(|v| v.borrow()[i].clone());
        match b.capture(rt, tag, inner) {
            Crossed::Found(k) => return Some(k),
            Crossed::Beyond(k) => inner = k,
            Crossed::Missing => return None,
        }
    }
    None
}

/// The whole continuation of the machine running, whose own frames, all
/// of them, are `own`: every machine's frames out to the bottom one's,
/// whose piece is whole. A whole continuation is given its value by the
/// bottom machine, to which a machine called from it throws it.
pub fn capture_whole(rt: &mut Runtime, own: Value) -> Value {
    let n = BOUNDARIES.with(|v| v.borrow().len());
    let mut inner = own;
    for i in (0..n).rev() {
        let b = BOUNDARIES.with(|v| v.borrow()[i].clone());
        inner = b.capture_whole(rt, i == 0, inner);
    }
    inner
}

/// The marks for `key` in the frames of the machines out from the one
/// running, innermost first.
pub fn marks(rt: &mut Runtime, key: Value) -> Vec<Value> {
    let n = BOUNDARIES.with(|v| v.borrow().len());
    let mut out = Vec::new();
    for i in (0..n).rev() {
        let b = BOUNDARIES.with(|v| v.borrow()[i].clone());
        let (marks, more) = b.marks(rt, key);
        out.extend(marks);
        if !more {
            break;
        }
    }
    out
}

/// The marks for `key` a continuation of another convention took,
/// innermost first, or none if it is none (`fixpt-native` installs it with
/// its first machine, before any such continuation is made).
pub type ForeignMarks = fn(&fixpt_heap::Heap, Value, Value) -> Option<Vec<Value>>;

static FOREIGN_MARKS: std::sync::OnceLock<ForeignMarks> = std::sync::OnceLock::new();

pub fn set_foreign_marks(f: ForeignMarks) {
    let _ = FOREIGN_MARKS.set(f);
}

/// `ForeignMarks`, if installed.
pub fn foreign_marks(heap: &fixpt_heap::Heap, k: Value, key: Value) -> Option<Vec<Value>> {
    FOREIGN_MARKS.get().and_then(|f| f(heap, k, key))
}
