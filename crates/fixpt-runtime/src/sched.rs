//! What FX-26's processes and `par` need of the runtime (`docs/fx26.md`,
//! "Processes"): a run queue of tasks, mailboxes, I-cells that tasks wait
//! for, and messages copied. The scheduler itself is FX-26, over prompts
//! (`fx26:processes.fx`, built in), and reaches these through one
//! primitive, `%fx26-sched`, an operation's number and two operands; so
//! every way FX-26 runs has them at once.
//!
//! A task is something the scheduler runs: a thunk, called under its
//! prompt, which ends or waits by capturing the rest of itself and
//! aborting there. Each task has the heap's place stack of its own
//! (`Heap::task_new`), so that tasks interleaving never end each other's
//! places. A task that waits hands over a thunk that resumes it; whatever
//! it waits for (a message, an I-cell's value) puts that thunk on the run
//! queue when it comes.
//!
//! The state is a vector, the value of a global no program names: the run
//! queue (the front, oldest first; the back, newest first), the scheduler's
//! prompt tag, a seed (a fixnum) when the queue is to be taken in an order
//! of its own (`FIXPT_SCHED_SEED`), else `#f`, the words copied, the
//! timers: what waits for the clock (a `pselect`'s deadline), each a pair
//! of the time and the waker, newest first; and the tasks cancelled (a
//! `race`'s losers), which end, not run, the next time they would; the
//! scheduler's `preempt`, which a machine calls at a poll whose time slice
//! is spent (`preempt_due`), or `#f`; the tasks it stopped, parked apart
//! from the run queue (newest first), so that `drain` ends; and how many
//! tasks the first task is running now, one inside another.

use crate::error::Outcome;
use crate::runtime::Runtime;
use fixpt_heap::layout::kind;
use fixpt_heap::{Heap, Value};

const STATE: &str = "%fx26-sched-state";
const FRONT: usize = 0;
const BACK: usize = 1;
const TAG: usize = 2;
const SEED: usize = 3;
const COPIED: usize = 4;
const TIMERS: usize = 5;
const CANCELLED: usize = 6;
const PREEMPT: usize = 7;
const PARKED: usize = 8;
const RUNNING: usize = 9;
const TRAMPOLINE: usize = 10;

/// The polls between two decisions whether to preempt (`preempt_due`): a
/// task's time slice, in each machine's polls (a bytecode machine's
/// instructions; procedure entries and backward branches in compiled code).
pub const SLICE: u64 = 1 << 16;

pub const ICELL: u8 = kind("icell");
pub const MAILBOX: u8 = kind("mailbox");
/// An I-cell's fields: whether it is full, its value, its waiters.
pub const ICELL_FULL: usize = 2;
pub const ICELL_VALUE: usize = 3;
pub const ICELL_WAITERS: usize = 4;
/// A mailbox's fields: messages, oldest first, then newest first; the task
/// waiting.
const MB_FRONT: usize = 2;
const MB_BACK: usize = 3;
const MB_WAITER: usize = 4;

/// The operations, by number, as `fx26:processes.fx` names them.
pub mod op {
    pub const TASK_NEW: i64 = 0;
    pub const TASK_SWITCH: i64 = 1;
    pub const TASK_END: i64 = 2;
    pub const TASK_CURRENT: i64 = 3;
    pub const PUSH: i64 = 4;
    pub const POP: i64 = 5;
    pub const MAILBOX_NEW: i64 = 6;
    pub const MAILBOX_PUT: i64 = 7;
    pub const MAILBOX_TAKE: i64 = 8;
    pub const MAILBOX_WAIT: i64 = 9;
    pub const ICELL_FULL: i64 = 10;
    pub const ICELL_WAIT: i64 = 11;
    pub const TAG: i64 = 12;
    pub const SET_TAG: i64 = 13;
    pub const ICELL_PUT: i64 = 14;
    pub const ICELL_VALUE: i64 = 15;
    pub const REAP_ENTER: i64 = 16;
    pub const MAILBOX_READY: i64 = 17;
    pub const TIMER_ADD: i64 = 18;
    pub const TIMER_DUE: i64 = 19;
    pub const TIMER_REMOVE: i64 = 20;
    pub const TIMERS_WAIT: i64 = 21;
    pub const ICELL_UNWAIT: i64 = 22;
    pub const MAILBOX_UNWAIT: i64 = 23;
    pub const TASK_CANCEL: i64 = 24;
    pub const TASK_CANCELLED: i64 = 25;
    pub const SET_PREEMPT: i64 = 26;
    pub const PARK: i64 = 27;
    pub const POP_ANY: i64 = 28;
    pub const RUNNING: i64 = 29;
    pub const TIMERS_FIRE: i64 = 30;
    pub const PREEMPT_WANTED: i64 = 31;
}

/// The state's vector, made if there is none yet.
fn state(heap: &mut Heap) -> Value {
    let sym = heap.intern_static(STATE);
    let slot = heap.symbol_global_slot(sym);
    let s = heap.global(slot);
    if heap.is_a(s, fixpt_heap::ObjType::Vector) {
        return s;
    }
    let seed = std::env::var("FIXPT_SCHED_SEED").ok().and_then(|s| s.parse::<i64>().ok());
    let s = heap.vector_from(&[Value::NULL, Value::NULL, Value::FALSE, seed.map_or(Value::FALSE, Value::fixnum), Value::fixnum(0), Value::NULL, Value::NULL, Value::FALSE, Value::NULL, Value::fixnum(0), Value::FALSE]);
    heap.set_global(slot, s);
    s
}

/// The state's vector, if there is one: making nothing, for a poll, which
/// must not allocate.
fn state_if_any(heap: &Heap) -> Option<Value> {
    let sym = heap.interned(STATE)?;
    let s = heap.global(heap.symbol_global_slot(sym));
    heap.is_a(s, fixpt_heap::ObjType::Vector).then_some(s)
}

/// Take the run queue in an order of the seed's (a test's, to try many), or,
/// with none, oldest first.
pub fn set_seed(heap: &mut Heap, seed: Option<i64>) {
    let s = state(heap);
    heap.obj_set(s, SEED, seed.map_or(Value::FALSE, |n| Value::fixnum(n & 0x0fff_ffff_ffff)));
}

/// Words copied into messages since the runtime began.
pub fn words_copied(heap: &mut Heap) -> i64 {
    let s = state(heap);
    heap.obj_ref(s, COPIED).as_fixnum()
}

/// After a run that failed: no task is left to resume. The run queue is
/// emptied, every task but the first ended, and the first made current. A
/// mailbox or I-cell that a task waits for keeps the waiter, which will
/// never run: harmless, as nothing else can wake it.
pub fn reset(heap: &mut Heap) {
    let s = state(heap);
    heap.obj_set(s, FRONT, Value::NULL);
    heap.obj_set(s, BACK, Value::NULL);
    heap.obj_set(s, TIMERS, Value::NULL);
    heap.obj_set(s, CANCELLED, Value::NULL);
    heap.obj_set(s, PARKED, Value::NULL);
    heap.obj_set(s, RUNNING, Value::fixnum(0));
    heap.tasks_reset();
}

fn push(heap: &mut Heap, thunk: Value) {
    let s = state(heap);
    let back = heap.obj_ref(s, BACK);
    let back = heap.cons(thunk, back);
    heap.obj_set(s, BACK, back);
}

/// The next task to run, or `#f`: the oldest, or, with a seed, one chosen
/// by it, so that a test can try many orders.
fn pop(heap: &mut Heap) -> Value {
    let s = state(heap);
    let mut front = heap.obj_ref(s, FRONT);
    if front == Value::NULL {
        let mut back = heap.obj_ref(s, BACK);
        while back.is_pair() {
            front = heap.cons(heap.car(back), front);
            back = heap.cdr(back);
        }
        heap.obj_set(s, BACK, Value::NULL);
    }
    if !front.is_pair() {
        heap.obj_set(s, FRONT, Value::NULL);
        return Value::FALSE;
    }
    let seed = heap.obj_ref(s, SEED);
    if seed.is_fixnum() {
        // A linear congruential step, then that many places along.
        let next = seed.as_fixnum().wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407) & 0x0fff_ffff_ffff;
        heap.obj_set(s, SEED, Value::fixnum(next));
        let mut items = Vec::new();
        let mut l = front;
        while l.is_pair() {
            items.push(heap.car(l));
            l = heap.cdr(l);
        }
        let i = (next >> 13) as usize % items.len();
        let t = items.remove(i);
        let rest = heap.list_from(&items);
        heap.obj_set(s, FRONT, rest);
        return t;
    }
    let t = heap.car(front);
    let rest = heap.cdr(front);
    heap.obj_set(s, FRONT, rest);
    t
}

/// What a message shares with its sender rather than copies: what is
/// never written (symbols, numbers kept in the heap), procedures and
/// continuations (code, and what their effects say they do not write), and
/// the capabilities, I-cells and mailboxes, whose identity is the point.
/// Everything else a transmissible type allows is immutable data, copied.
fn shared(heap: &Heap, v: Value) -> bool {
    if v.is_pair() {
        return false;
    }
    const COPIED: [u8; 6] = [kind("string"), kind("bytevector"), kind("bloblet"), kind("sum"), kind("product"), kind("flat-array")];
    !COPIED.contains(&heap.bloblet_head(v).kind)
}

/// `%fx26-sched`'s operation `n` on `a` and `b`. Each operand is checked
/// to be what the operation takes, so that no call of it can break the
/// heap; only the scheduler calls it, which the checkers make so.
pub fn run_op(rt: &mut Runtime, n: i64, a: Value, b: Value) -> Outcome<Value> {
    let unit = rt.heap.intern_static("#u");
    let is = |rt: &Runtime, v: Value, k: u8| v.is_bloblet() && rt.heap.bloblet_kind(v) == k;
    match n {
        op::TASK_SWITCH | op::TASK_END | op::TASK_CANCEL if !a.is_fixnum() || !rt.heap.task_live(a.as_fixnum() as usize) => {
            return rt.fail("%fx26-sched: no such task", &[a]);
        }
        op::MAILBOX_PUT | op::MAILBOX_TAKE | op::MAILBOX_WAIT | op::MAILBOX_READY if !is(rt, a, MAILBOX) => {
            return rt.type_error("a mailbox", a);
        }
        op::MAILBOX_UNWAIT if !is(rt, a, MAILBOX) => return rt.type_error("a mailbox", a),
        op::ICELL_FULL | op::ICELL_WAIT | op::ICELL_VALUE | op::ICELL_UNWAIT if !is(rt, a, ICELL) => {
            return rt.type_error("an i-cell", a);
        }
        op::TIMER_ADD | op::TIMER_DUE => {
            let t = crate::prim::fixed_in(rt, a, crate::prim::Width::I64)? as i64;
            return Ok(if n == op::TIMER_DUE { Value::boolean(crate::world::clock_ns() >= t) } else { timer_add(rt, t, b) });
        }
        op::TIMERS_WAIT => return Ok(timers_wait(rt, true)),
        op::TIMERS_FIRE => return Ok(timers_wait(rt, false)),
        // For the evaluator written in FX-26, which runs a program's
        // scheduler as its own values, and so calls its `preempt` itself:
        // whether to, on the one machine it runs on.
        op::PREEMPT_WANTED => {
            let w = state_if_any(&rt.heap).is_some_and(|s| wanted(rt, s, |_, _| true));
            return Ok(Value::boolean(w));
        }
        _ => {}
    }
    let heap = &mut rt.heap;
    Ok(match n {
        op::TASK_NEW => Value::fixnum(heap.task_new() as i64),
        op::TASK_SWITCH => Value::fixnum(heap.task_switch(a.as_fixnum() as usize) as i64),
        op::TASK_END => {
            if a.as_fixnum() != 0 {
                heap.task_end(a.as_fixnum() as usize);
                // Its number, free for another task, is not cancelled.
                let s = state(heap);
                let cs = heap.obj_ref(s, CANCELLED);
                let cs = without(heap, cs, |_, t| t == a);
                heap.obj_set(s, CANCELLED, cs);
            }
            unit
        }
        // Task `a`, live, cancelled: it ends the next time it would run.
        op::TASK_CANCEL => {
            if a.as_fixnum() != 0 {
                let s = state(heap);
                let cs = heap.obj_ref(s, CANCELLED);
                let cs = heap.cons(a, cs);
                heap.obj_set(s, CANCELLED, cs);
            }
            unit
        }
        op::TASK_CANCELLED => {
            let s = state(heap);
            let mut cs = heap.obj_ref(s, CANCELLED);
            let mut found = false;
            while cs.is_pair() && !found {
                found = heap.car(cs) == a;
                cs = heap.cdr(cs);
            }
            Value::boolean(found)
        }
        op::TASK_CURRENT => Value::fixnum(heap.task_current() as i64),
        op::PUSH => {
            push(heap, a);
            unit
        }
        op::POP => pop(heap),
        // The scheduler's `preempt`, for the machines to call.
        op::SET_PREEMPT => {
            let s = state(heap);
            heap.obj_set(s, PREEMPT, a);
            if heap.obj_ref(s, TRAMPOLINE) == Value::FALSE {
                use fixpt_heap::layout::cellular::routine;
                let cells = [routine("call"), 0, routine("drop"), routine("exit")].map(|n| Value::fixnum(n as i64));
                let name = heap.intern_static("%preempt-trampoline");
                let t = heap.make_cellular_word(name, &cells).expect("a word");
                let s = state(heap);
                heap.obj_set(s, TRAMPOLINE, t);
            }
            unit
        }
        // A task stopped at a poll, apart from the run queue.
        op::PARK => {
            let s = state(heap);
            let ps = heap.obj_ref(s, PARKED);
            let ps = heap.cons(a, ps);
            heap.obj_set(s, PARKED, ps);
            unit
        }
        // The next task to run, or, with none, the oldest parked one.
        op::POP_ANY => {
            let t = pop(heap);
            if t != Value::FALSE {
                t
            } else {
                let s = state(heap);
                let mut ps = heap.obj_ref(s, PARKED);
                let mut rest = Vec::new();
                while ps.is_pair() {
                    rest.push(heap.car(ps));
                    ps = heap.cdr(ps);
                }
                match rest.pop() {
                    None => Value::FALSE,
                    Some(t) => {
                        let ps = heap.list_from(&rest);
                        heap.obj_set(s, PARKED, ps);
                        t
                    }
                }
            }
        }
        // The first task begins (`a` 1) or ends (-1) running a task.
        op::RUNNING => {
            let s = state(heap);
            let n = heap.obj_ref(s, RUNNING).as_fixnum() + if a.is_fixnum() { a.as_fixnum() } else { 0 };
            heap.obj_set(s, RUNNING, Value::fixnum(n.max(0)));
            unit
        }
        op::MAILBOX_NEW => {
            let m = heap.make_bloblet(MAILBOX, 3, 0, true);
            heap.set_bloblet_slot(m, MB_FRONT, Value::NULL);
            heap.set_bloblet_slot(m, MB_BACK, Value::NULL);
            heap.set_bloblet_slot(m, MB_WAITER, Value::FALSE);
            m
        }
        // The message copied, at the back; the receiver, if it waits, run.
        op::MAILBOX_PUT => {
            let (msg, words) = heap.copy_within(b, shared);
            let s = state(heap);
            let copied = heap.obj_ref(s, COPIED).as_fixnum();
            heap.obj_set(s, COPIED, Value::fixnum(copied + words as i64));
            let back = heap.bloblet_slot(a, MB_BACK);
            let back = heap.cons(msg, back);
            heap.set_bloblet_slot(a, MB_BACK, back);
            let w = heap.bloblet_slot(a, MB_WAITER);
            if w != Value::FALSE {
                heap.set_bloblet_slot(a, MB_WAITER, Value::FALSE);
                push(heap, w);
            }
            unit
        }
        op::MAILBOX_READY => {
            let ready = heap.bloblet_slot(a, MB_FRONT).is_pair() || heap.bloblet_slot(a, MB_BACK).is_pair();
            Value::boolean(ready)
        }
        // The oldest message, taken.
        op::MAILBOX_TAKE => {
            let mut front = heap.bloblet_slot(a, MB_FRONT);
            if !front.is_pair() {
                let mut back = heap.bloblet_slot(a, MB_BACK);
                while back.is_pair() {
                    front = heap.cons(heap.car(back), front);
                    back = heap.cdr(back);
                }
                heap.set_bloblet_slot(a, MB_BACK, Value::NULL);
            }
            if !front.is_pair() {
                heap.set_bloblet_slot(a, MB_FRONT, Value::NULL);
                return rt.fail("%fx26-sched: an empty mailbox taken from", &[]);
            }
            let m = heap.car(front);
            let rest = heap.cdr(front);
            heap.set_bloblet_slot(a, MB_FRONT, rest);
            m
        }
        op::MAILBOX_WAIT => {
            heap.set_bloblet_slot(a, MB_WAITER, b);
            unit
        }
        op::ICELL_FULL => heap.bloblet_slot(a, ICELL_FULL),
        op::ICELL_VALUE => heap.bloblet_slot(a, ICELL_VALUE),
        op::ICELL_WAIT => {
            let ws = heap.bloblet_slot(a, ICELL_WAITERS);
            let ws = heap.cons(b, ws);
            heap.set_bloblet_slot(a, ICELL_WAITERS, ws);
            unit
        }
        // Waker `b` no longer waits for `a`: a `pselect`'s, once one of its
        // events has woken it (so that one waiting many times keeps none).
        op::ICELL_UNWAIT => {
            let ws = heap.bloblet_slot(a, ICELL_WAITERS);
            let ws = without(heap, ws, |_, w| w == b);
            heap.set_bloblet_slot(a, ICELL_WAITERS, ws);
            unit
        }
        op::MAILBOX_UNWAIT => {
            if heap.bloblet_slot(a, MB_WAITER) == b {
                heap.set_bloblet_slot(a, MB_WAITER, Value::FALSE);
            }
            unit
        }
        op::TIMER_REMOVE => {
            let s = state(heap);
            let ts = heap.obj_ref(s, TIMERS);
            let ts = without(heap, ts, |heap, t| heap.cdr(t) == a);
            heap.obj_set(s, TIMERS, ts);
            unit
        }
        op::ICELL_PUT => return icell_put(rt, a, b),
        // `(sum some tag)`, the scheduler's prompt tag, or `(sum none #u)`
        // before the scheduler has made one.
        op::TAG => {
            let s = state(heap);
            let t = heap.obj_ref(s, TAG);
            const SUM: u8 = kind("sum");
            if t == Value::FALSE {
                let none = heap.intern_static("none");
                heap.make_frozen(SUM, &[none, unit])
            } else {
                let some = heap.intern_static("some");
                heap.make_frozen(SUM, &[some, t])
            }
        }
        op::SET_TAG => {
            let s = state(heap);
            heap.obj_set(s, TAG, a);
            unit
        }
        // A reap, the current task's newest place: a process's own.
        op::REAP_ENTER => Value::fixnum(heap.reap_enter() as i64),
        _ => return rt.fail("%fx26-sched: no such operation", &[Value::fixnum(n)]),
    })
}

/// List `l` without the items `drop` picks, in the same order; `l` itself
/// if it has none.
fn without(heap: &mut Heap, l: Value, drop: impl Fn(&Heap, Value) -> bool) -> Value {
    let mut kept = Vec::new();
    let mut any = false;
    let mut x = l;
    while x.is_pair() {
        let v = heap.car(x);
        if drop(heap, v) {
            any = true;
        } else {
            kept.push(v);
        }
        x = heap.cdr(x);
    }
    if any { heap.list_from(&kept) } else { l }
}

/// Waker `w` run when the clock reaches `t` (a time `clock_ns` gives).
fn timer_add(rt: &mut Runtime, t: i64, w: Value) -> Value {
    let heap = &mut rt.heap;
    let t = Value::fixnum(t.clamp(fixpt_heap::value::FIXNUM_MIN, fixpt_heap::value::FIXNUM_MAX));
    let entry = heap.cons(t, w);
    let s = state(heap);
    let ts = heap.obj_ref(s, TIMERS);
    let ts = heap.cons(entry, ts);
    heap.obj_set(s, TIMERS, ts);
    heap.intern_static("#u")
}

/// When no task can run and the first waits: `#f` if no timer is set;
/// else, having slept until the earliest (if `sleep`), each timer due taken,
/// its waker run (in the order of their times), and `#t`.
fn timers_wait(rt: &mut Runtime, sleep: bool) -> Value {
    let heap = &mut rt.heap;
    let s = state(heap);
    let ts = heap.obj_ref(s, TIMERS);
    if !ts.is_pair() {
        return Value::FALSE;
    }
    let mut earliest = i64::MAX;
    let mut x = ts;
    while x.is_pair() {
        earliest = earliest.min(heap.car(heap.car(x)).as_fixnum());
        x = heap.cdr(x);
    }
    if sleep {
        crate::world::sleep_until(earliest);
    }
    let now = crate::world::clock_ns();
    let mut due = Vec::new();
    let mut x = ts;
    while x.is_pair() {
        let t = heap.car(x);
        if heap.car(t).as_fixnum() <= now {
            due.push((heap.car(t).as_fixnum(), heap.cdr(t)));
        }
        x = heap.cdr(x);
    }
    let ts = without(heap, ts, |heap, t| heap.car(t).as_fixnum() <= now);
    heap.obj_set(s, TIMERS, ts);
    // The oldest first among those of one time.
    due.reverse();
    due.sort_by_key(|&(t, _)| t);
    for (_, w) in due {
        push(heap, w);
    }
    Value::TRUE
}

/// At a poll whose time slice is spent: the scheduler's `preempt`, for the
/// machine to call there and then go on, if another task could run and
/// preempting is safe here; else none. In a task, the first task waits for
/// it to stop (it runs every other), so it is preempted wherever
/// `reachable` finds the scheduler's prompt on the machine's own stack,
/// which `preempt` captures up to (no capture crosses from one machine to
/// another). The first task is, if another is queued or parked, or a
/// deadline is due, and it is not running one already (`preempt` runs one).
pub fn preempt_due(rt: &mut Runtime, reachable: impl FnOnce(&Runtime, Value) -> bool) -> Option<Value> {
    preempt_due_with(rt, reachable).map(|(f, _)| f)
}

/// `preempt_due`'s procedure, with a cellular word for a cellular machine
/// to enter with it on the data stack: `call 0`, `drop`, `exit`, which
/// calls it and goes back to the cell it stopped at, the stacks as they
/// were.
pub fn preempt_due_with(rt: &mut Runtime, reachable: impl FnOnce(&Runtime, Value) -> bool) -> Option<(Value, Value)> {
    let heap = &rt.heap;
    let s = state_if_any(heap)?;
    let f = heap.obj_ref(s, PREEMPT);
    if f == Value::FALSE || !wanted(rt, s, reachable) {
        return None;
    }
    Some((f, rt.heap.obj_ref(s, TRAMPOLINE)))
}

/// Whether the scheduler would have the current task preempted here
/// (`preempt_due`), whoever calls its `preempt`.
fn wanted(rt: &Runtime, s: Value, reachable: impl FnOnce(&Runtime, Value) -> bool) -> bool {
    let heap = &rt.heap;
    if heap.task_current() == 0 {
        let runnable = [FRONT, BACK, PARKED].iter().any(|&k| heap.obj_ref(s, k).is_pair()) || timer_due(heap, s);
        return runnable && heap.obj_ref(s, RUNNING).as_fixnum() == 0;
    }
    let tag = heap.obj_ref(s, TAG);
    tag != Value::FALSE && reachable(rt, tag)
}

/// Whether a timer is due.
fn timer_due(heap: &Heap, s: Value) -> bool {
    let now = crate::world::clock_ns();
    let mut x = heap.obj_ref(s, TIMERS);
    while x.is_pair() {
        if heap.car(heap.car(x)).as_fixnum() <= now {
            return true;
        }
        x = heap.cdr(x);
    }
    false
}

/// A new I-cell, empty, in the heap: shared by the processes it is sent
/// to, so never in a place that could end before them.
pub fn make_icell(heap: &mut Heap) -> Value {
    let c = heap.make_bloblet(ICELL, 3, 0, true);
    heap.set_bloblet_slot(c, ICELL_FULL, Value::FALSE);
    heap.set_bloblet_slot(c, ICELL_VALUE, Value::FALSE);
    heap.set_bloblet_slot(c, ICELL_WAITERS, Value::NULL);
    c
}

/// I-cell `c` given `v`, its one write; the tasks waiting for it run.
pub fn icell_put(rt: &mut Runtime, c: Value, v: Value) -> Outcome<Value> {
    if !c.is_bloblet() || rt.heap.bloblet_kind(c) != ICELL {
        return rt.type_error("an i-cell", c);
    }
    if rt.heap.bloblet_slot(c, ICELL_FULL) != Value::FALSE {
        return rt.fail("an i-cell written twice", &[v]);
    }
    let heap = &mut rt.heap;
    heap.set_bloblet_slot(c, ICELL_VALUE, v);
    heap.set_bloblet_slot(c, ICELL_FULL, Value::TRUE);
    let mut ws = heap.bloblet_slot(c, ICELL_WAITERS);
    heap.set_bloblet_slot(c, ICELL_WAITERS, Value::NULL);
    // In the order they began to wait.
    let mut order = Vec::new();
    while ws.is_pair() {
        order.push(heap.car(ws));
        ws = heap.cdr(ws);
    }
    for w in order.into_iter().rev() {
        push(heap, w);
    }
    Ok(heap.intern_static("#u"))
}
