//! Control on the native machines' own stacks: prompts, marks, aborts, and
//! continuations captured and reinstated, without lifting the stacks into
//! the Rust machine and back (the round trip).
//!
//! These are the Rust machine's routines (`fixpt_engine::threaded`), step
//! for step, and it stays their oracle. They can work in place because a
//! native return entry has the Rust machine's bits: `(word, 8k, 8fp,
//! closure)` is `(word, fixnum k, fixnum fp, closure)`. So a stack index is
//! the same number to both, and a continuation captured by one can be
//! reinstated by the other.
//!
//! Every push checks the stack's room, where the Rust machine's stacks are
//! vectors, so a deep reinstatement traps rather than writing past them.

use fixpt_engine::threaded::{prompt_height, prompt_regions, prompt_word, reinstated_prompt, MARK_MARK, PROMPT_MARK, Trap};
use fixpt_heap::layout::kind;
use fixpt_heap::layout::threaded::{
    CLOSURE_WORD, CONT_BASE, CONT_CLO, CONT_CUR, CONT_DS, CONT_FIELDS, CONT_FP, CONT_K, CONT_RS, CONT_REGIONS, CONT_WHOLE, WORD_CELL0,
};
use fixpt_heap::{Heap, Value};

use crate::threaded::State;

/// The stacks as the Rust machine sees them: the data stack's values and
/// the return stack's words, each indexed from the bottom.
struct Stacks<'s> {
    st: &'s mut State,
}

impl Stacks<'_> {
    fn ds_len(&self) -> usize {
        (self.st.ds_base - self.st.dsp) as usize / 8
    }
    fn ds_at(&self, i: usize) -> u64 {
        self.st.ds_base - 8 - 8 * i as u64
    }
    fn ds_get(&self, i: usize) -> Value {
        // SAFETY: below `ds_len`, a word of the data stack.
        unsafe { Value(*(self.ds_at(i) as *const u64)) }
    }
    fn ds_push(&mut self, v: Value) -> Result<(), Trap> {
        if self.st.dsp - 8 < self.st.ds_limit {
            return Err(Trap::StackOverflow);
        }
        self.st.dsp -= 8;
        // SAFETY: within the data stack's room, checked above.
        unsafe { *(self.st.dsp as *mut u64) = v.raw() };
        Ok(())
    }
    fn ds_pop(&mut self, routine: &'static str) -> Result<Value, Trap> {
        if self.ds_len() == 0 {
            return Err(Trap::Underflow { routine });
        }
        let v = self.ds_get(self.ds_len() - 1);
        self.st.dsp += 8;
        Ok(v)
    }
    fn ds_truncate(&mut self, n: usize) {
        self.st.dsp = self.st.ds_base - 8 * n as u64;
    }

    /// The return stack's length in words, four to an entry.
    fn rs_len(&self) -> usize {
        (self.st.rs_base - self.st.rsp) as usize / 8
    }
    fn rs_get(&self, i: usize) -> Value {
        // Entry `i / 4` from the bottom, word `i % 4` within it.
        let at = self.st.rs_base - 32 * (i as u64 / 4 + 1) + 8 * (i as u64 % 4);
        // SAFETY: below `rs_len`, a word of the return stack.
        unsafe { Value(*(at as *const u64)) }
    }
    fn rs_push_entry(&mut self, e: [Value; 4]) -> Result<(), Trap> {
        if self.st.rsp - 32 <= self.st.rs_limit {
            return Err(Trap::TooDeep);
        }
        self.st.rsp -= 32;
        for (j, v) in e.iter().enumerate() {
            // SAFETY: within the return stack's room, checked above.
            unsafe { *((self.st.rsp + 8 * j as u64) as *mut u64) = v.raw() };
        }
        Ok(())
    }
    fn rs_truncate(&mut self, words: usize) {
        self.st.rsp = self.st.rs_base - 8 * words as u64;
    }

    /// The registers as a return entry, and back.
    fn push_return(&mut self) -> Result<(), Trap> {
        let e = [Value(self.st.cur), Value(self.st.d), Value(self.st.fp), Value(self.st.clo)];
        self.rs_push_entry(e)
    }
    fn fp(&self) -> usize {
        self.st.fp as usize / 8
    }
    fn set_regs(&mut self, cur: Value, k: usize, fp: usize, clo: Value) {
        (self.st.cur, self.st.d, self.st.fp, self.st.clo) = (cur.raw(), 8 * k as u64, 8 * fp as u64, clo.raw());
    }

    /// Return to the entry on top, leaving any prompt's marker or mark on
    /// the way behind.
    fn pop_return(&mut self) {
        loop {
            let n = self.rs_len();
            let cur = self.rs_get(n - 4);
            if cur == PROMPT_MARK || cur == MARK_MARK {
                self.rs_truncate(n - 4);
                continue;
            }
            let (d, fp, clo) = (self.rs_get(n - 3), self.rs_get(n - 2), self.rs_get(n - 1));
            (self.st.cur, self.st.d, self.st.fp, self.st.clo) = (cur.raw(), d.raw(), fp.raw(), clo.raw());
            self.rs_truncate(n - 4);
            return;
        }
    }

    /// Where the innermost entry marked `sentinel` for `key` starts.
    fn find_marked(&self, sentinel: Value, key: Value) -> Option<usize> {
        let mut i = self.rs_len();
        while i >= 4 {
            i -= 4;
            if self.rs_get(i) == sentinel && self.rs_get(i + 1) == key {
                return Some(i);
            }
        }
        None
    }
}

const CLOSURE: u8 = kind("threaded-closure");
const CONTINUATION: u8 = kind("threaded-continuation");

fn is_a(heap: &Heap, v: Value, k: u8) -> bool {
    v.is_bloblet() && heap.bloblet_kind(v) == k
}

/// Run closure `thunk` with no arguments above a marker entry.
fn enter_above(s: &mut Stacks, heap: &Heap, thunk: Value, marker: [Value; 4], routine: &'static str) -> Result<(), Trap> {
    if !is_a(heap, thunk, CLOSURE) {
        return Err(Trap::Type { routine });
    }
    s.push_return()?;
    s.rs_push_entry(marker)?;
    let fp = s.ds_len();
    s.set_regs(heap.bloblet_slot(thunk, CLOSURE_WORD), WORD_CELL0, fp, thunk);
    Ok(())
}

/// Call the closure or continuation on top with the `n` values below it.
fn call(s: &mut Stacks, heap: &mut Heap, n: usize, tail: bool, routine: &'static str) -> Result<(), Trap> {
    if s.ds_len() < s.fp() + n + 1 {
        return Err(Trap::Underflow { routine });
    }
    let c = s.ds_pop(routine)?;
    if is_a(heap, c, CONTINUATION) {
        if n != 1 {
            return Err(Trap::Prim(format!("a continuation takes one value, and was given {n}")));
        }
        let v = s.ds_pop(routine)?;
        return reinstate(s, heap, c, v, tail);
    }
    if !is_a(heap, c, CLOSURE) {
        return Err(Trap::Type { routine });
    }
    let word = heap.bloblet_slot(c, CLOSURE_WORD);
    let fp = if tail {
        // Slide the new frame down over this one.
        let (from, to) = (s.ds_len() - n, s.fp());
        for i in 0..n {
            let v = s.ds_get(from + i);
            // SAFETY: `to + i` is below the stack's length.
            unsafe { *(s.ds_at(to + i) as *mut u64) = v.raw() };
        }
        s.ds_truncate(to + n);
        to
    } else {
        s.push_return()?;
        s.ds_len() - n
    };
    s.set_regs(word, WORD_CELL0, fp, c);
    Ok(())
}

/// A continuation of the stacks from word `rs_from` and value `ds_from` up.
fn capture(s: &Stacks, heap: &mut Heap, rs_from: usize, ds_from: usize, whole: bool) -> Value {
    if crate::threaded::TIMING.with(|t| *t) {
        let words = (s.ds_len() - ds_from + s.rs_len() - rs_from) as u64;
        crate::threaded::CAPTURED.with(|c| {
            let mut c = c.borrow_mut();
            (c.0, c.1) = (c.0 + words, c.1 + 1);
            if c.1.is_power_of_two() {
                eprintln!("capture {}: {} data, {} return words", c.1, s.ds_len() - ds_from, s.rs_len() - rs_from);
            }
        });
    }
    let ds = heap.vector_with(s.ds_len() - ds_from, |i| s.ds_get(ds_from + i));
    // An entry register code's `blr` pushed is marked (its `8k` negated):
    // resumed from a continuation it returns the stack's way, so it is
    // captured plain.
    let rs = heap.vector_with(s.rs_len() - rs_from, |i| {
        let w = s.rs_get(rs_from + i);
        let lead = s.rs_get(rs_from + i - i % 4);
        let entry = lead != PROMPT_MARK && lead != MARK_MARK;
        if i % 4 == 1 && entry && w.is_fixnum() && w.as_fixnum() < 0 { Value::fixnum(-w.as_fixnum()) } else { w }
    });
    let k = heap.make_bloblet(CONTINUATION, CONT_FIELDS, 0, true);
    let fields = [
        (CONT_DS, ds),
        (CONT_RS, rs),
        (CONT_CUR, Value(s.st.cur)),
        (CONT_K, Value(s.st.d)),
        (CONT_FP, Value(s.st.fp)),
        (CONT_CLO, Value(s.st.clo)),
        (CONT_BASE, Value::fixnum(ds_from as i64)),
        (CONT_WHOLE, Value::boolean(whole)),
        (CONT_REGIONS, Value::fixnum(heap.live_regions() as i64)),
    ];
    for (f, v) in fields {
        heap.set_bloblet_slot(k, f, v);
    }
    k
}

/// Give continuation `k` the value `v`: composed onto these stacks, frame
/// pointers and prompts' heights moved by the difference in depth; or,
/// whole, replacing them.
fn reinstate(s: &mut Stacks, heap: &mut Heap, k: Value, v: Value, tail: bool) -> Result<(), Trap> {
    let ds = heap.bloblet_slot(k, CONT_DS);
    let rs = heap.bloblet_slot(k, CONT_RS);
    let whole = heap.bloblet_slot(k, CONT_WHOLE) == Value::TRUE;
    let old_base = heap.bloblet_slot(k, CONT_BASE).as_fixnum();
    if whole {
        s.ds_truncate(0);
        s.rs_truncate(0);
        // The regions entered since it was taken end, as an abort's do.
        heap.region_exit(heap.bloblet_slot(k, CONT_REGIONS).as_fixnum() as usize);
    } else if tail {
        let fp = s.fp();
        s.ds_truncate(fp);
    } else {
        s.push_return()?;
    }
    let delta = s.ds_len() as i64 - old_base;
    let live = heap.live_regions();
    for v in heap.obj_iter(ds) {
        s.ds_push(v)?;
    }
    let mut words = heap.obj_iter(rs);
    while let (Some(a), Some(b), Some(c), Some(d)) = (words.next(), words.next(), words.next(), words.next()) {
        let mut entry = [a, b, c, d];
        if entry[0] == PROMPT_MARK {
            entry[3] = reinstated_prompt(entry[3], delta, whole, live);
        } else if entry[0] != MARK_MARK {
            entry[2] = Value::fixnum(entry[2].as_fixnum() + delta);
        }
        s.rs_push_entry(entry)?;
    }
    let cur = heap.bloblet_slot(k, CONT_CUR);
    let kk = heap.bloblet_slot(k, CONT_K).as_fixnum() as usize;
    let fp = (heap.bloblet_slot(k, CONT_FP).as_fixnum() + delta) as usize;
    s.set_regs(cur, kk, fp, heap.bloblet_slot(k, CONT_CLO));
    s.ds_push(v)
}

/// Routine `name`, if it is one done here; its operands, if any, start at
/// the saved ip. `None` for the rest.
pub(crate) fn run(st: &mut State, heap: &mut Heap, name: &'static str, safepoint: fn(&mut State, &mut Heap)) -> Option<Result<(), Trap>> {
    let r = match name {
        "prompt" | "withmark" | "withmark-tail" | "abort" | "callcomp" | "callcc" | "firstmark" | "call" | "tailcall"
        | "tcall" | "ttailcall" | "resume" => {
            routine(st, heap, name, safepoint)
        }
        _ => return None,
    };
    Some(r)
}

fn routine(st: &mut State, heap: &mut Heap, name: &'static str, safepoint: fn(&mut State, &mut Heap)) -> Result<(), Trap> {
    match name {
        "call" | "tailcall" | "tcall" | "ttailcall" => {
            let k = (st.d / 8) as usize;
            let n = heap.bloblet_slot(Value(st.cur), k).as_fixnum() as usize;
            st.d += 8;
            call(&mut Stacks { st }, heap, n, name.ends_with("tailcall"), name)
        }
        "resume" => {
            let mut s = Stacks { st };
            let k = s.ds_pop(name)?;
            let v = s.ds_pop(name)?;
            if !is_a(heap, k, CONTINUATION) {
                return Err(Trap::Type { routine: name });
            }
            reinstate(&mut s, heap, k, v, true)
        }
        "prompt" => {
            let mut s = Stacks { st };
            let thunk = s.ds_pop(name)?;
            let handler = s.ds_pop(name)?;
            let tag = s.ds_pop(name)?;
            let height = prompt_word(s.ds_len(), heap.live_regions());
            enter_above(&mut s, heap, thunk, [PROMPT_MARK, tag, handler, height], name)
        }
        "withmark" => {
            let mut s = Stacks { st };
            let thunk = s.ds_pop(name)?;
            let v = s.ds_pop(name)?;
            let key = s.ds_pop(name)?;
            enter_above(&mut s, heap, thunk, [MARK_MARK, key, v, Value::fixnum(0)], name)
        }
        "withmark-tail" => {
            let mut s = Stacks { st };
            let thunk = s.ds_pop(name)?;
            let v = s.ds_pop(name)?;
            let key = s.ds_pop(name)?;
            if !is_a(heap, thunk, CLOSURE) {
                return Err(Trap::Type { routine: name });
            }
            let fp = s.fp();
            s.ds_truncate(fp);
            let n = s.rs_len();
            if n >= 4 && s.rs_get(n - 4) == MARK_MARK && s.rs_get(n - 3) == key {
                // The value's word of the entry on top.
                // SAFETY: word 2 of the top entry, within the return stack.
                unsafe { *((s.st.rsp + 16) as *mut u64) = v.raw() };
            } else {
                s.rs_push_entry([MARK_MARK, key, v, Value::fixnum(0)])?;
            }
            let fp = s.ds_len();
            s.set_regs(heap.bloblet_slot(thunk, CLOSURE_WORD), WORD_CELL0, fp, thunk);
            Ok(())
        }
        "abort" => {
            let mut s = Stacks { st };
            let v = s.ds_pop(name)?;
            let tag = s.ds_pop(name)?;
            let Some(at) = s.find_marked(PROMPT_MARK, tag) else {
                return Err(Trap::Prim("abort: no prompt for this tag".into()));
            };
            let handler = s.rs_get(at + 2);
            let (height, regions) = (prompt_height(s.rs_get(at + 3)), prompt_regions(s.rs_get(at + 3)));
            s.rs_truncate(at);
            s.pop_return();
            s.ds_truncate(height);
            // What the regions entered inside the prompt held is gone with
            // what was cut: no frame left can resume their bodies.
            heap.region_exit(regions);
            s.ds_push(v)?;
            s.ds_push(handler)?;
            call(&mut s, heap, 1, false, name)
        }
        "callcomp" | "callcc" => {
            let at = {
                let mut s = Stacks { st: &mut *st };
                if name == "callcomp" {
                    let tag = s.ds_pop(name)?;
                    let Some(at) = s.find_marked(PROMPT_MARK, tag) else {
                        return Err(Trap::Prim("call-with-composable-continuation: no prompt for this tag".into()));
                    };
                    Some(at)
                } else {
                    None
                }
            };
            // The procedure stays on the stack through the safepoint.
            safepoint(st, heap);
            let mut s = Stacks { st };
            let proc_ = s.ds_pop(name)?;
            let k = match at {
                Some(at) => {
                    let height = prompt_height(s.rs_get(at + 3));
                    capture(&s, heap, at + 4, height, false)
                }
                None => capture(&s, heap, 0, 0, true),
            };
            // Given as a closure, so that everything callable is one.
            let k = heap.continuation_closure(k);
            s.ds_push(k)?;
            s.ds_push(proc_)?;
            call(&mut s, heap, 1, false, name)
        }
        "firstmark" => {
            let mut s = Stacks { st };
            let default = s.ds_pop(name)?;
            let key = s.ds_pop(name)?;
            let v = match s.find_marked(MARK_MARK, key) {
                Some(at) => s.rs_get(at + 2),
                None => default,
            };
            s.ds_push(v)
        }
        _ => unreachable!("only the routines `run` takes"),
    }
}
