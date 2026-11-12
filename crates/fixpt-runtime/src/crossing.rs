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
    /// Whether its frames hold a prompt for `tag`; and whether a machine
    /// called it, whose frames are further out.
    fn has_prompt(&self, rt: &mut Runtime, tag: Value) -> (bool, bool);
}

pub type Boundary = Rc<dyn Crossing>;

thread_local! {
    /// The boundaries of the session running, innermost last, each with
    /// the serial of the heap whose machines it is between.
    static BOUNDARIES: RefCell<Vec<(u64, Boundary)>> = const { RefCell::new(Vec::new()) };
    /// The chains of boundaries `apart` set aside, outermost first: each
    /// the boundaries of a session whose call ran another session's code.
    /// Nothing walks them by default; what is to look past the marker
    /// (a backtrace through both) finds them here.
    static SET_ASIDE: RefCell<Vec<Vec<(u64, Boundary)>>> = const { RefCell::new(Vec::new()) };
}

/// What a machine keeps of the thread's runs besides the boundaries (the
/// direct machine's mark of the call out it runs native calls below):
/// taken and cleared as `apart` begins, and put back as it ends. Installed
/// by the crate that has such a machine (`set_apart_hooks`).
pub type ApartHooks = (fn() -> Box<dyn std::any::Any>, fn(Box<dyn std::any::Any>));

static APART_HOOKS: std::sync::OnceLock<ApartHooks> = std::sync::OnceLock::new();

pub fn set_apart_hooks(h: ApartHooks) {
    let _ = APART_HOOKS.set(h);
}

/// `f`, a run of another session's code inside a call of this one's (a
/// procedural macro's transformer, run as a program is checked: `TODO.md`
/// §261), apart from this session's: its boundaries, and each machine's
/// marks (`ApartHooks`), set aside for `f`'s length, so that what `f` runs
/// captures, finds prompts and marks, and is a bottom machine, in its own
/// session alone. Its heap is not this one's, so nothing of this one's
/// could be part of its continuations anyway. Put back however `f` ends.
pub fn apart<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(Option<Box<dyn std::any::Any>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            if let (Some(m), Some((_, put))) = (self.0.take(), APART_HOOKS.get()) {
                put(m);
            }
            let chain = SET_ASIDE.with(|s| s.borrow_mut().pop()).expect("set aside as `apart` began");
            BOUNDARIES.with(|v| *v.borrow_mut() = chain);
        }
    }
    let chain = BOUNDARIES.with(|v| std::mem::take(&mut *v.borrow_mut()));
    SET_ASIDE.with(|s| s.borrow_mut().push(chain));
    let _restore = Restore(APART_HOOKS.get().map(|(take, _)| take()));
    f()
}

/// That a run of heap `serial`'s code may begin here, `what` asking: the
/// innermost boundary, if any, is its own heap's. A run of another
/// session's code inside a call of this one's is `apart`'s to begin; this
/// fails loudly where one forgot it.
#[track_caller]
pub fn assert_own_chain(serial: u64, what: &str) {
    BOUNDARIES.with(|v| {
        if let Some((h, _)) = v.borrow().last() {
            assert!(*h == serial, "{what} of another heap's session inside this one's call, not `crossing::apart` (`TODO.md` §261)");
        }
    });
}

/// What a call between machines must leave of the thread's Rust stack: a
/// machine run, and a collection, below the call.
const STACK_MARGIN: usize = 256 << 10;

thread_local! {
    /// The lowest address of this thread's stack; 0 where unknown.
    static STACK_LOW: usize = stack_low();
}

/// The lowest address of the running thread's stack, 0 if it is not known.
#[cfg(target_os = "macos")]
#[allow(unsafe_code)]
fn stack_low() -> usize {
    // SAFETY: of the thread running; both only read its attributes.
    unsafe {
        let me = libc::pthread_self();
        libc::pthread_get_stackaddr_np(me) as usize - libc::pthread_get_stacksize_np(me)
    }
}

#[cfg(target_os = "linux")]
#[allow(unsafe_code)]
fn stack_low() -> usize {
    // SAFETY: the attributes of the thread running, read into `attr`, then
    // freed.
    unsafe {
        let mut attr: libc::pthread_attr_t = std::mem::zeroed();
        if libc::pthread_getattr_np(libc::pthread_self(), &mut attr) != 0 {
            return 0;
        }
        let (mut addr, mut size) = (std::ptr::null_mut(), 0);
        let ok = libc::pthread_attr_getstack(&attr, &mut addr, &mut size) == 0;
        libc::pthread_attr_destroy(&mut attr);
        if ok { addr as usize } else { 0 }
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn stack_low() -> usize {
    0
}

/// Whether the Rust stack has room for another call between machines
/// (`TODO.md` §93): each nests a few Rust frames, so calls alternating
/// between them run out of it long before either machine's own stack. A
/// machine refuses the call, a stack overflow, where it has not.
pub fn room() -> bool {
    let here = 0u8;
    let at = std::ptr::addr_of!(here) as usize;
    STACK_LOW.with(|low| *low == 0 || at > low + STACK_MARGIN)
}

/// A boundary entered, between machines of heap `serial`, for the length
/// of the call that `f` makes.
pub fn across<T>(serial: u64, b: Boundary, f: impl FnOnce() -> T) -> T {
    BOUNDARIES.with(|v| v.borrow_mut().push((serial, b)));
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
        let b = BOUNDARIES.with(|v| v.borrow()[i].1.clone());
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
        let b = BOUNDARIES.with(|v| v.borrow()[i].1.clone());
        inner = b.capture_whole(rt, i == 0, inner);
    }
    inner
}

/// Whether a prompt for `tag` is in the frames of the machines out from
/// the one running: a capture up to it would reach it (`capture`).
pub fn reachable(rt: &mut Runtime, tag: Value) -> bool {
    let n = BOUNDARIES.with(|v| v.borrow().len());
    for i in (0..n).rev() {
        let b = BOUNDARIES.with(|v| v.borrow()[i].1.clone());
        match b.has_prompt(rt, tag) {
            (true, _) => return true,
            (false, false) => return false,
            (false, true) => {}
        }
    }
    false
}

/// The marks for `key` in the frames of the machines out from the one
/// running, innermost first.
pub fn marks(rt: &mut Runtime, key: Value) -> Vec<Value> {
    let n = BOUNDARIES.with(|v| v.borrow().len());
    let mut out = Vec::new();
    for i in (0..n).rev() {
        let b = BOUNDARIES.with(|v| v.borrow()[i].1.clone());
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

#[cfg(test)]
mod tests {
    use super::*;

    /// A boundary that holds nothing: for the chain alone.
    struct Empty;

    impl Crossing for Empty {
        fn capture(&self, _: &mut Runtime, _: Value, _: Value) -> Crossed {
            Crossed::Missing
        }
        fn capture_whole(&self, _: &mut Runtime, _: bool, inner: Value) -> Value {
            inner
        }
        fn marks(&self, _: &mut Runtime, _: Value) -> (Vec<Value>, bool) {
            (Vec::new(), false)
        }
        fn has_prompt(&self, _: &mut Runtime, _: Value) -> (bool, bool) {
            (false, false)
        }
    }

    /// Another session's run, `apart`, sees no boundary of this one's, may
    /// begin on its own heap, and leaves this one's chain as it was, however
    /// it ends.
    #[test]
    fn apart_sets_the_chain_aside_and_puts_it_back() {
        across(1, Rc::new(Empty), || {
            assert!(crossed());
            assert_own_chain(1, "this session's code");
            apart(|| {
                assert!(!crossed(), "none of the outer session's boundaries");
                assert_own_chain(2, "the other session's code");
                across(2, Rc::new(Empty), || assert!(crossed()));
            });
            assert!(crossed(), "put back");
            let _ = std::panic::catch_unwind(|| apart(|| panic!("ended by a panic")));
            assert!(crossed(), "put back after a panic too");
            assert_own_chain(1, "this session's code");
        });
        assert!(!crossed());
    }

    /// A run of another heap's code begun inside this session's call, not
    /// `apart`, fails loudly.
    #[test]
    fn another_heaps_run_must_be_apart() {
        across(1, Rc::new(Empty), || {
            let caught = std::panic::catch_unwind(|| assert_own_chain(2, "the other session's code"));
            assert!(caught.is_err(), "refused");
        });
    }
}
