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
//! tasks the first task is running now, one inside another; the trampoline
//! word (`preempt_due_with`); each task of a monitored group (a monitored
//! process's tasks, or a `race` branch's), with its group (its first
//! task), as pairs; each group's handler, `(group . handler)`; a
//! failure caught, `(message . handler)`, for the scheduler to give the
//! handler (`task_failed`); each `race` branch's group with the group it
//! is inside, `(group . group)`, which its failure cancels too; and each
//! task that waits, with how it stops waiting, `(task . stop)`, so that,
//! cancelled, it ends at once (`REAP`); and the wakers waiting for the
//! standard input (`STDIN_WAIT`).

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
const GROUPS: usize = 11;
const MONITORS: usize = 12;
const FAILURE: usize = 13;
const PARENTS: usize = 14;
const WAITING: usize = 15;
const STDIN_WAITERS: usize = 16;
/// Heist's F6: the wakers waiting for a process's output, and for its end,
/// each `(p . waker)`.
const OUTPUT_WAITERS: usize = 17;
const EXIT_WAITERS: usize = 18;
/// The wakers waiting for any process's news.
const NEWS_WAITERS: usize = 19;

/// The polls between two decisions whether to preempt (`preempt_due`): a
/// task's time slice, in each machine's polls (a bytecode machine's
/// instructions; procedure entries and backward branches in compiled code).
/// `FIXPT_SLICE` sets another, for testing (`slice`).
pub const SLICE: u64 = 1 << 16;

/// The time slice: `SLICE`, or `FIXPT_SLICE` if set (1 or more), so that a
/// test may preempt at nearly every poll.
pub fn slice() -> u64 {
    static S: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *S.get_or_init(|| std::env::var("FIXPT_SLICE").ok().and_then(|s| s.parse().ok()).filter(|&n| n > 0).unwrap_or(SLICE))
}

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
    pub const PREEMPT_DONE: i64 = 32;
    pub const QUIET: i64 = 33;
    pub const ICELL_OFFER: i64 = 34;
    pub const MONITOR: i64 = 35;
    pub const INHERIT: i64 = 36;
    pub const TAKE_FAILURE: i64 = 37;
    pub const TASK_FAILED: i64 = 38;
    pub const BRANCH_GROUP: i64 = 39;
    pub const WAITING: i64 = 40;
    pub const WOKEN: i64 = 41;
    pub const REAP: i64 = 42;
    pub const STDIN_READY: i64 = 43;
    pub const STDIN_WAIT: i64 = 44;
    pub const STDIN_UNWAIT: i64 = 45;
    pub const OUTPUT_READY: i64 = 46;
    pub const OUTPUT_WAIT: i64 = 47;
    pub const OUTPUT_UNWAIT: i64 = 48;
    pub const EXIT_READY: i64 = 49;
    pub const EXIT_WAIT: i64 = 50;
    pub const EXIT_UNWAIT: i64 = 51;
    pub const NEWS_READY: i64 = 52;
    pub const NEWS_WAIT: i64 = 53;
    pub const NEWS_UNWAIT: i64 = 54;
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
    let s = heap.vector_from(&[Value::NULL, Value::NULL, Value::FALSE, seed.map_or(Value::FALSE, Value::fixnum), Value::fixnum(0), Value::NULL, Value::NULL, Value::FALSE, Value::NULL, Value::fixnum(0), Value::FALSE, Value::NULL, Value::NULL, Value::FALSE, Value::NULL, Value::NULL, Value::NULL, Value::NULL, Value::NULL, Value::NULL]);
    heap.set_global(slot, s);
    s
}

/// The scheduler's prompt tag, once it has one: what a machine at a poll
/// looks for beyond its own frames (`crossing::reachable`), before it asks
/// `preempt_due`.
pub fn prompt_tag(heap: &Heap) -> Option<Value> {
    state_if_any(heap).map(|s| heap.obj_ref(s, TAG)).filter(|t| *t != Value::FALSE)
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
    heap.obj_set(s, GROUPS, Value::NULL);
    heap.obj_set(s, MONITORS, Value::NULL);
    heap.obj_set(s, FAILURE, Value::FALSE);
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
        op::TASK_SWITCH | op::TASK_END | op::TASK_CANCEL | op::MONITOR | op::INHERIT | op::BRANCH_GROUP | op::WAITING if !a.is_fixnum() || !rt.heap.task_live(a.as_fixnum() as usize) => {
            return rt.fail(&format!("%fx26-sched: no such task (op {n})"), &[a]);
        }
        op::MAILBOX_PUT | op::MAILBOX_TAKE | op::MAILBOX_WAIT | op::MAILBOX_READY if !is(rt, a, MAILBOX) => {
            return rt.type_error("a mailbox", a);
        }
        op::MAILBOX_UNWAIT if !is(rt, a, MAILBOX) => return rt.type_error("a mailbox", a),
        op::ICELL_FULL | op::ICELL_WAIT | op::ICELL_VALUE | op::ICELL_UNWAIT | op::ICELL_OFFER if !is(rt, a, ICELL) => {
            return rt.type_error("an i-cell", a);
        }
        op::TIMER_ADD | op::TIMER_DUE => {
            let t = crate::prim::fixed_in(rt, a, crate::prim::Width::I64)? as i64;
            return Ok(if n == op::TIMER_DUE { Value::boolean(crate::world::clock_ns() >= t) } else { timer_add(rt, t, b) });
        }
        op::TIMERS_WAIT => return Ok(timers_wait(rt, true)),
        op::TIMERS_FIRE => return Ok(timers_wait(rt, false)),
        // For the evaluator written in FX-26, whose failures are its own (an
        // abort to its tag): the current task failed with message `a`; the
        // scheduler's tag to abort to, if it is of a monitored process
        // (`task_failed`), else `#f`. The evaluator runs on one machine, the
        // scheduler's prompt on it.
        op::TASK_FAILED => {
            if !rt.heap.is_a(a, fixpt_heap::ObjType::String) {
                return rt.type_error("a string", a);
            }
            let m = rt.heap.string_to_rust(a);
            // The evaluator's polls cannot see whether the scheduler's
            // prompt is still on the stack (`PREEMPT_WANTED` assumes it
            // is), so the failed task is made quiet from here: after the
            // abort, until `TAKE_FAILURE` ends it, the scheduler's own code
            // runs as that task, outside the prompt, and a poll there would
            // `suspend` it with no prompt to capture to.
            let tag = task_failed(rt, &m, |_, _| true);
            if tag.is_some() {
                rt.heap.quiet_enter();
            }
            return Ok(tag.unwrap_or(Value::FALSE));
        }
        // For the evaluator written in FX-26, which runs a program's
        // scheduler as its own values, and so calls its `preempt` itself:
        // whether to, on the one machine it runs on.
        op::PREEMPT_WANTED => {
            let w = match state_if_any(&rt.heap) {
                Some(s) => wanted(rt, s, |_, _| true),
                None => false,
            };
            if w {
                rt.heap.quiet_enter();
            }
            return Ok(Value::boolean(w));
        }
        // Out of what `QUIET` began (`preempt_done`).
        op::PREEMPT_DONE => {
            preempt_done(rt);
            return Ok(rt.heap.intern_static("#u"));
        }
        // The current task not to be preempted until `PREEMPT_DONE`: from
        // when it hands its waker over until it has left (`suspend`), lest
        // a preemption between leave two ways to resume it.
        op::QUIET => {
            rt.heap.quiet_enter();
            return Ok(rt.heap.intern_static("#u"));
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
                forget_task(heap, a);
            }
            unit
        }
        // Task `a`, new, the first of a monitored group (a process, a
        // `race` branch): a group of its own, whose failure handler `b`,
        // `(subr any (string) unit)`, the scheduler calls with a failure's
        // message.
        op::MONITOR | op::BRANCH_GROUP => {
            let s = state(heap);
            // A `race` branch's group is inside the current task's, if it
            // has one: should that group fail, the branch is cancelled too.
            if n == op::BRANCH_GROUP
                && let Some(p) = group_of(heap, Value::fixnum(heap.task_current() as i64))
            {
                let e = heap.cons(a, p);
                let ps = heap.obj_ref(s, PARENTS);
                let ps = heap.cons(e, ps);
                heap.obj_set(s, PARENTS, ps);
            }
            let g = heap.cons(a, a);
            let gs = heap.obj_ref(s, GROUPS);
            let gs = heap.cons(g, gs);
            heap.obj_set(s, GROUPS, gs);
            let m = heap.cons(a, b);
            let ms = heap.obj_ref(s, MONITORS);
            let ms = heap.cons(m, ms);
            heap.obj_set(s, MONITORS, ms);
            unit
        }
        // Task `a`, new, a branch (`par`, `race`) of the current task: of
        // its group, if it has one, so that its failure is the process's.
        op::INHERIT => {
            if let Some(g) = group_of(heap, Value::fixnum(heap.task_current() as i64)) {
                let s = state(heap);
                let e = heap.cons(a, g);
                let gs = heap.obj_ref(s, GROUPS);
                let gs = heap.cons(e, gs);
                heap.obj_set(s, GROUPS, gs);
            }
            unit
        }
        // The failure `task_failed` caught, if any: the current task, which
        // failed, ended, and `(message . handler)` for the scheduler to call;
        // else `#f`.
        op::TAKE_FAILURE => {
            let s = state(heap);
            let f = heap.obj_ref(s, FAILURE);
            if f != Value::FALSE {
                heap.obj_set(s, FAILURE, Value::FALSE);
                let t = heap.task_current();
                if t != 0 {
                    heap.task_end(t);
                    forget_task(heap, Value::fixnum(t as i64));
                }
            }
            f
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
                let done = crate::PRIMITIVES.iter().position(|d| d.name == "%fx26-preempt-done").expect("a primitive") as u64;
                let cells = [routine("call"), 0, routine("drop"), routine("prim"), done, 0, routine("drop"), routine("exit")].map(|n| Value::fixnum(n as i64));
                let name = heap.intern_static("%preempt-trampoline");
                let t = heap.make_cellular_word(name, &cells).expect("a word");
                let s = state(heap);
                heap.obj_set(s, TRAMPOLINE, t);
            }
            unit
        }
        // Whether a read of the standard input would not wait (`TODO.md`
        // §95); waker `a` run once it would not, and taken back.
        op::STDIN_READY => Value::boolean(rt.world.stdin_ready()),
        op::STDIN_WAIT => {
            let s = state(heap);
            let ws = heap.obj_ref(s, STDIN_WAITERS);
            let ws = heap.cons(a, ws);
            heap.obj_set(s, STDIN_WAITERS, ws);
            unit
        }
        op::STDIN_UNWAIT => {
            let s = state(heap);
            let ws = heap.obj_ref(s, STDIN_WAITERS);
            let ws = without(heap, ws, |_, w| w == a);
            heap.obj_set(s, STDIN_WAITERS, ws);
            unit
        }
        // Heist's F6: whether process `a` has output to take; whether it
        // has ended, its output all taken; waker `b` run once it has (or
        // is), and taken back (`a` the waker).
        op::OUTPUT_READY => Value::boolean(rt.world.process_output_ready(a.as_fixnum())),
        op::EXIT_READY => Value::boolean(rt.world.process_ended(a.as_fixnum())),
        // Whether any process has news; waker `a` run once one has.
        op::NEWS_READY => Value::boolean(rt.world.process_news() >= 0),
        op::NEWS_WAIT => {
            let s = state(heap);
            let ws = heap.obj_ref(s, NEWS_WAITERS);
            let ws = heap.cons(a, ws);
            heap.obj_set(s, NEWS_WAITERS, ws);
            unit
        }
        op::NEWS_UNWAIT => {
            let s = state(heap);
            let ws = heap.obj_ref(s, NEWS_WAITERS);
            let ws = without(heap, ws, |_, w| w == a);
            heap.obj_set(s, NEWS_WAITERS, ws);
            unit
        }
        op::OUTPUT_WAIT | op::EXIT_WAIT => {
            let slot = if n == op::OUTPUT_WAIT { OUTPUT_WAITERS } else { EXIT_WAITERS };
            let s = state(heap);
            let e = heap.cons(a, b);
            let ws = heap.obj_ref(s, slot);
            let ws = heap.cons(e, ws);
            heap.obj_set(s, slot, ws);
            unit
        }
        op::OUTPUT_UNWAIT | op::EXIT_UNWAIT => {
            let slot = if n == op::OUTPUT_UNWAIT { OUTPUT_WAITERS } else { EXIT_WAITERS };
            let s = state(heap);
            let ws = heap.obj_ref(s, slot);
            let ws = without(heap, ws, |heap, e| heap.cdr(e) == a);
            heap.obj_set(s, slot, ws);
            unit
        }
        // Task `a` waits, and `b` stops it waiting: its waker taken back.
        op::WAITING => {
            let s = state(heap);
            let e = heap.cons(a, b);
            let ws = heap.obj_ref(s, WAITING);
            let ws = heap.cons(e, ws);
            heap.obj_set(s, WAITING, ws);
            unit
        }
        // Task `a` waits no more: it was woken.
        op::WOKEN => {
            let s = state(heap);
            let ws = heap.obj_ref(s, WAITING);
            let ws = without(heap, ws, |h, e| h.car(e) == a);
            heap.obj_set(s, WAITING, ws);
            unit
        }
        // Each cancelled task that waits, `(task . stop)`, for the scheduler
        // to stop and end, now: none is left waiting.
        op::REAP => {
            let s = state(heap);
            let (cs, mut ws) = (heap.obj_ref(s, CANCELLED), heap.obj_ref(s, WAITING));
            let cancelled = |h: &Heap, t: Value| {
                let mut c = cs;
                while c.is_pair() {
                    if h.car(c) == t {
                        return true;
                    }
                    c = h.cdr(c);
                }
                false
            };
            let mut reaped = Vec::new();
            while ws.is_pair() {
                let e = heap.car(ws);
                if cancelled(heap, heap.car(e)) {
                    reaped.push(e);
                }
                ws = heap.cdr(ws);
            }
            let ws = heap.obj_ref(s, WAITING);
            let ws = without(heap, ws, |h, e| cancelled(h, h.car(e)));
            heap.obj_set(s, WAITING, ws);
            heap.list_from(&reaped)
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
        // Waker `b` for `a`'s next message; run at once if one is there.
        // A task checks, then waits, and may be preempted in between
        // (`preempt_due`): what arrived meanwhile must still wake it.
        op::MAILBOX_WAIT => {
            if heap.bloblet_slot(a, MB_FRONT).is_pair() || heap.bloblet_slot(a, MB_BACK).is_pair() {
                push(heap, b);
            } else {
                heap.set_bloblet_slot(a, MB_WAITER, b);
            }
            unit
        }
        op::ICELL_FULL => heap.bloblet_slot(a, ICELL_FULL),
        op::ICELL_VALUE => heap.bloblet_slot(a, ICELL_VALUE),
        // Waker `b` for `a`'s value; run at once if it has one (as
        // `MAILBOX_WAIT`).
        op::ICELL_WAIT if heap.bloblet_slot(a, ICELL_FULL) != Value::FALSE => {
            push(heap, b);
            unit
        }
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
        // I-cell `a` given `b` if it has no value yet, in one step: the
        // first of `race`'s branches to finish, though another, preempted
        // between a test and a fill, finishes too.
        op::ICELL_OFFER if heap.bloblet_slot(a, ICELL_FULL) != Value::FALSE => unit,
        op::ICELL_OFFER => return icell_put(rt, a, b),
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

/// Waker `w` run when the clock reaches `t` (a time `clock_ns` gives); at
/// once if it has (as `MAILBOX_WAIT`).
fn timer_add(rt: &mut Runtime, t: i64, w: Value) -> Value {
    let heap = &mut rt.heap;
    if crate::world::clock_ns() >= t {
        push(heap, w);
        return heap.intern_static("#u");
    }
    let t = Value::fixnum(t.clamp(fixpt_heap::value::FIXNUM_MIN, fixpt_heap::value::FIXNUM_MAX));
    let entry = heap.cons(t, w);
    let s = state(heap);
    let ts = heap.obj_ref(s, TIMERS);
    let ts = heap.cons(entry, ts);
    heap.obj_set(s, TIMERS, ts);
    heap.intern_static("#u")
}

/// When no task can run and the first waits: `#f` if no timer is set and
/// no waker waits for the standard input or a process (Heist's F6); else,
/// having slept until the earliest timer, or until the input is ready or a
/// process has news, whichever is first (if `sleep`), the wakers of what is
/// ready run, and each timer due taken, its waker run (in the order of
/// their times), and `#t`.
fn timers_wait(rt: &mut Runtime, sleep: bool) -> Value {
    let s = state(&mut rt.heap);
    let ts = rt.heap.obj_ref(s, TIMERS);
    let input = rt.heap.obj_ref(s, STDIN_WAITERS).is_pair();
    let news = rt.heap.obj_ref(s, NEWS_WAITERS).is_pair();
    let processes = rt.heap.obj_ref(s, OUTPUT_WAITERS).is_pair() || rt.heap.obj_ref(s, EXIT_WAITERS).is_pair() || news;
    if !ts.is_pair() && !input && !processes {
        return Value::FALSE;
    }
    let heap = &rt.heap;
    let mut earliest = None;
    let mut x = ts;
    while x.is_pair() {
        let t = heap.car(heap.car(x)).as_fixnum();
        earliest = Some(earliest.map_or(t, |e: i64| e.min(t)));
        x = heap.cdr(x);
    }
    if sleep {
        match (input, processes, earliest) {
            (_, true, until) => rt.world.wait_processes(until, input),
            (true, false, until) => {
                rt.world.wait_stdin(until);
            }
            (false, false, Some(t)) => crate::world::sleep_until(t),
            (false, false, None) => {}
        }
    }
    if input && rt.world.stdin_ready() {
        let heap = &mut rt.heap;
        let mut ws = heap.obj_ref(s, STDIN_WAITERS);
        heap.obj_set(s, STDIN_WAITERS, Value::NULL);
        let mut order = Vec::new();
        while ws.is_pair() {
            order.push(heap.car(ws));
            ws = heap.cdr(ws);
        }
        for w in order.into_iter().rev() {
            push(&mut rt.heap, w);
        }
    }
    if news && rt.world.process_news() >= 0 {
        let mut ws = rt.heap.obj_ref(s, NEWS_WAITERS);
        rt.heap.obj_set(s, NEWS_WAITERS, Value::NULL);
        let mut order = Vec::new();
        while ws.is_pair() {
            order.push(rt.heap.car(ws));
            ws = rt.heap.cdr(ws);
        }
        for w in order.into_iter().rev() {
            push(&mut rt.heap, w);
        }
    }
    if processes {
        for (slot, ready) in [(OUTPUT_WAITERS, true), (EXIT_WAITERS, false)] {
            let mut ws = rt.heap.obj_ref(s, slot);
            let mut waiting = Vec::new();
            let mut woken = Vec::new();
            while ws.is_pair() {
                let e = rt.heap.car(ws);
                let p = rt.heap.car(e).as_fixnum();
                let now = if ready { rt.world.process_output_ready(p) } else { rt.world.process_ended(p) };
                if now { woken.push(rt.heap.cdr(e)) } else { waiting.push(e) }
                ws = rt.heap.cdr(ws);
            }
            if !woken.is_empty() {
                let rest = rt.heap.list_from(&waiting);
                rt.heap.obj_set(s, slot, rest);
                for w in woken.into_iter().rev() {
                    push(&mut rt.heap, w);
                }
            }
        }
    }
    let heap = &mut rt.heap;
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
///
/// `own` says whether `preempt` is a procedure this machine calls (another
/// machine's program may have left its scheduler's: they share a runtime).
/// When this says to call it, the task is marked as being preempted until
/// `preempt` is done (`PREEMPT_DONE`), and not preempted again meanwhile
/// (the scheduler's own code, preempted, would capture a capture under
/// way), nor at the next slice's end, so that it has a slice of its own
/// whatever `preempt` cost: else, with a slice shorter than that, no task
/// would ever go on.
pub fn preempt_due(rt: &mut Runtime, own: impl FnOnce(&Heap, Value) -> bool, reachable: impl FnOnce(&Runtime, Value) -> bool) -> Option<Value> {
    preempt_due_with(rt, own, reachable).map(|(f, _)| f)
}

/// `preempt_due`'s procedure, with a cellular word for a cellular machine
/// to enter with it on the data stack: `call 0`, `drop`, then
/// `%fx26-preempt-done` (`preempt_done`), `drop`, `exit`, which calls it
/// and goes back to the cell it stopped at, the stacks as they were.
pub fn preempt_due_with(
    rt: &mut Runtime,
    own: impl FnOnce(&Heap, Value) -> bool,
    reachable: impl FnOnce(&Runtime, Value) -> bool,
) -> Option<(Value, Value)> {
    let heap = &rt.heap;
    let s = state_if_any(heap)?;
    let f = heap.obj_ref(s, PREEMPT);
    if f == Value::FALSE || !own(heap, f) || !wanted(rt, s, reachable) {
        return None;
    }
    let f = rt.heap.obj_ref(s, PREEMPT);
    rt.heap.quiet_enter();
    Some((f, rt.heap.obj_ref(s, TRAMPOLINE)))
}

/// Whether the scheduler would have the current task preempted here
/// (`preempt_due`), whoever calls its `preempt`.
fn wanted(rt: &mut Runtime, s: Value, reachable: impl FnOnce(&Runtime, Value) -> bool) -> bool {
    if rt.heap.task_quiet() || rt.heap.take_grace() {
        return false;
    }
    let heap = &rt.heap;
    if heap.task_current() == 0 {
        let runnable = [FRONT, BACK, PARKED].iter().any(|&k| heap.obj_ref(s, k).is_pair()) || timer_due(heap, s);
        return runnable && heap.obj_ref(s, RUNNING).as_fixnum() == 0;
    }
    let tag = heap.obj_ref(s, TAG);
    tag != Value::FALSE && reachable(rt, tag)
}

/// What a machine does once a call of `preempt` it made at a poll has
/// returned (the task resumed, if it was parked): the task may be preempted
/// again, after a slice of its own; as `PREEMPT_DONE` ends a wait's quiet.
pub fn preempt_done(rt: &mut Runtime) {
    rt.heap.quiet_leave();
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

/// What the scheduler kept of task `t`, ended: its number, free for another
/// task, is neither cancelled nor of a group nor waiting; and, if it began
/// a monitored process, the monitor goes with it, and what group it was
/// inside, or had inside it.
fn forget_task(heap: &mut Heap, t: Value) {
    let s = state(heap);
    let cs = heap.obj_ref(s, CANCELLED);
    let cs = without(heap, cs, |_, c| c == t);
    heap.obj_set(s, CANCELLED, cs);
    let gs = heap.obj_ref(s, GROUPS);
    let gs = without(heap, gs, |h, e| h.car(e) == t);
    heap.obj_set(s, GROUPS, gs);
    let ms = heap.obj_ref(s, MONITORS);
    let ms = without(heap, ms, |h, m| h.car(m) == t);
    heap.obj_set(s, MONITORS, ms);
    let ps = heap.obj_ref(s, PARENTS);
    let ps = without(heap, ps, |h, e| h.car(e) == t || h.cdr(e) == t);
    heap.obj_set(s, PARENTS, ps);
    let ws = heap.obj_ref(s, WAITING);
    let ws = without(heap, ws, |h, e| h.car(e) == t);
    heap.obj_set(s, WAITING, ws);
}

/// The group task `t` is of, if any.
fn group_of(heap: &Heap, t: Value) -> Option<Value> {
    let s = state_if_any(heap)?;
    let mut gs = heap.obj_ref(s, GROUPS);
    while gs.is_pair() {
        let e = heap.car(gs);
        if heap.car(e) == t {
            return Some(heap.cdr(e));
        }
        gs = heap.cdr(gs);
    }
    None
}

/// The current task failed (a panic, `error`, or a trap), with `message`:
/// if it is of a monitored group (a monitored process's, a `race`
/// branch's), and the scheduler's prompt is where `reachable` finds it, the
/// failure is the group's, not the form's (`docs/fx26.md`, "Monitors"). The
/// rest of the group cancelled, the failure kept for the scheduler to give
/// the group's handler (`TAKE_FAILURE`), and the prompt's tag given back,
/// for the machine to abort to, with `#u`, as a task that waits does; else
/// none, and the failure is the form's.
pub fn task_failed(rt: &mut Runtime, message: &str, reachable: impl FnOnce(&Runtime, Value) -> bool) -> Option<Value> {
    let heap = &rt.heap;
    let cur = heap.task_current();
    if cur == 0 {
        return None;
    }
    let s = state_if_any(heap)?;
    let g = group_of(heap, Value::fixnum(cur as i64))?;
    let mut ms = heap.obj_ref(s, MONITORS);
    let mut mon = None;
    while ms.is_pair() {
        let m = heap.car(ms);
        if heap.car(m) == g {
            mon = Some(heap.cdr(m));
        }
        ms = heap.cdr(ms);
    }
    let mon = mon?;
    let tag = heap.obj_ref(s, TAG);
    if tag == Value::FALSE || !reachable(rt, tag) || heap.obj_ref(s, FAILURE) != Value::FALSE {
        return None;
    }
    let heap = &mut rt.heap;
    // The rest of the group cancelled, and every group inside it (`race`
    // branches', `BRANCH_GROUP`): each ends the next time it would run.
    let mut groups = vec![g];
    loop {
        let before = groups.len();
        let mut ps = heap.obj_ref(s, PARENTS);
        while ps.is_pair() {
            let e = heap.car(ps);
            if groups.contains(&heap.cdr(e)) && !groups.contains(&heap.car(e)) {
                groups.push(heap.car(e));
            }
            ps = heap.cdr(ps);
        }
        if groups.len() == before {
            break;
        }
    }
    let mut others = Vec::new();
    let mut gs = heap.obj_ref(s, GROUPS);
    while gs.is_pair() {
        let e = heap.car(gs);
        if groups.contains(&heap.cdr(e)) && heap.car(e).as_fixnum() as usize != cur {
            others.push(heap.car(e));
        }
        gs = heap.cdr(gs);
    }
    for t in others {
        let cs = heap.obj_ref(s, CANCELLED);
        let cs = heap.cons(t, cs);
        heap.obj_set(s, CANCELLED, cs);
    }
    let m = heap.make_string(message);
    let f = heap.cons(m, mon);
    heap.obj_set(s, FAILURE, f);
    // Whatever it was in (a wait, a preemption) left behind.
    while heap.task_quiet() {
        heap.quiet_leave();
    }
    Some(tag)
}

/// What a failure says, as `task_failed` gives it to a monitor: an error
/// object's message, or the condition written.
pub fn condition_message(rt: &Runtime, obj: Value) -> String {
    if rt.is_error_object(obj) {
        let m = rt.heap.obj_ref(obj, 1);
        if rt.heap.is_a(m, fixpt_heap::ObjType::String) {
            return rt.heap.string_to_rust(m);
        }
    }
    crate::print::write_value(&rt.heap, obj)
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
