//! What the checker is working on, in debug builds, for when the stack runs
//! low: a *shadow stack* of the expressions `synth`, `check` and `parse_exp`
//! are in, innermost last, each with the address of the frame it was entered
//! from (`enter`). An entry is never popped on the way out, so that no early
//! return need see to it: an entry made at or below a frame later entered is
//! from a call that has returned, and goes then.
//!
//! When the stack the checks use passes a mark (`FIXPT_STACK_HIGH_WATER`
//! bytes, else three quarters of `RUST_MIN_STACK`), the shadow stack is said
//! once on standard error, each entry where its text is
//! (`fixpt_read::describe_source`), and `fixpt_stack_high_water` is called,
//! a function that does nothing, for a debugger to stop at while there is
//! still stack to run its commands on (`tools/gdb/fixpt.py`; by their Rust
//! names, `fixpt_fx26::debug_stack::…`, the crate having no unsafe code to
//! export them by others). Release builds keep none of it.

use fixpt_read::Span;

/// Expression `span`, being checked or read as `what`, entered.
#[inline(always)]
pub(crate) fn enter(what: &'static str, span: Span) {
    #[cfg(debug_assertions)]
    shadow::enter(what, span);
    #[cfg(not(debug_assertions))]
    let _ = (what, span);
}

/// What this thread's shadow stack holds, outermost first, a line each.
pub fn report() -> String {
    #[cfg(debug_assertions)]
    return shadow::report();
    #[cfg(not(debug_assertions))]
    String::from("(no shadow stack: a release build)\n")
}

/// Called once, when the stack the checks use passes the mark: nothing,
/// for a debugger to stop at (`break fixpt_stack_high_water`).
#[inline(never)]
pub fn fixpt_stack_high_water() {
    std::hint::black_box(());
}

/// The shadow stack said on standard error: for a debugger to call.
#[inline(never)]
pub fn fixpt_shadow_report() {
    say(&report());
}

/// `text` on standard error, written to it, not printed: a test's printing
/// is held until the test ends, and a stack overflow ends no test.
fn say(text: &str) {
    use std::io::Write;
    let _ = std::io::stderr().write_all(text.as_bytes());
}

/// Where the span of `file`, `start`..`end` is, as a C string that lasts
/// until the next call on this thread: for a debugger's printer of spans.
#[inline(never)]
pub fn fixpt_span_place(file: u32, start: u32, end: u32) -> *const std::ffi::c_char {
    thread_local! {
        static SAID: std::cell::RefCell<std::ffi::CString> = std::cell::RefCell::new(std::ffi::CString::default());
    }
    let span = Span { file: fixpt_read::FileId(file), start, end, expansion: 0 };
    let said = fixpt_read::describe_source(span).unwrap_or_else(|| format!("file {file}, {start}..{end}"));
    let said = std::ffi::CString::new(said.replace('\0', " ")).unwrap_or_default();
    SAID.with(|s| {
        *s.borrow_mut() = said;
        s.borrow().as_ptr()
    })
}

#[cfg(debug_assertions)]
mod shadow {
    use std::cell::RefCell;

    use fixpt_read::Span;

    #[derive(Default)]
    struct Shadow {
        /// The address the outermost entry was made from: what the checks'
        /// stack is measured from.
        base: usize,
        entries: Vec<(usize, &'static str, Span)>,
        /// The mark, in bytes of stack; 0 for none.
        mark: usize,
        reported: bool,
    }

    thread_local! {
        static SHADOW: RefCell<Shadow> = RefCell::new(Shadow { mark: mark(), ..Shadow::default() });
    }

    fn mark() -> usize {
        let bytes = |v: &str| std::env::var(v).ok().and_then(|s| s.trim().parse::<usize>().ok());
        bytes("FIXPT_STACK_HIGH_WATER").or_else(|| bytes("RUST_MIN_STACK").map(|n| n / 4 * 3)).unwrap_or(0)
    }

    #[inline(never)]
    pub(super) fn enter(what: &'static str, span: Span) {
        let here = 0u8;
        let at = std::hint::black_box(&here) as *const u8 as usize;
        let crossed = SHADOW.with(|s| {
            let mut s = s.borrow_mut();
            while s.entries.last().is_some_and(|(a, _, _)| *a <= at) {
                s.entries.pop();
            }
            if s.entries.is_empty() {
                s.base = at;
            }
            s.entries.push((at, what, span));
            let crossed = s.mark != 0 && !s.reported && s.base.saturating_sub(at) > s.mark;
            s.reported |= crossed;
            crossed
        });
        if crossed {
            let mark = SHADOW.with(|s| s.borrow().mark);
            super::say(&format!("fixpt: the checks have used more than {mark} bytes of stack; what they are in:\n{}", report()));
            // What a debugger calls here, kept in the binary.
            std::hint::black_box((super::fixpt_shadow_report as fn(), super::fixpt_span_place as fn(u32, u32, u32) -> *const std::ffi::c_char));
            super::fixpt_stack_high_water();
        }
    }

    pub(super) fn report() -> String {
        SHADOW.with(|s| {
            let s = s.borrow();
            let mut out = String::new();
            for (i, (at, what, span)) in s.entries.iter().enumerate() {
                let place = fixpt_read::describe_source(*span).unwrap_or_else(|| format!("{span:?}"));
                out.push_str(&format!("  {i:>4} {:>8} B  {what:<6} {place}\n", s.base.saturating_sub(*at)));
            }
            out
        })
    }
}
