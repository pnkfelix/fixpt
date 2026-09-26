//! The threaded machine's routines for code compiled from FX-26: frames and
//! locals, closures, calls and tail calls, globals, and the runtime's
//! primitives. Words are built by hand here; the compiler (PLAN.md §11, 9d)
//! makes them from FX-26.

use fixpt_engine::threaded::{Machine, SELF, Trap, WordBuilder};
use fixpt_heap::Value;
use fixpt_runtime::Runtime;

fn fx(n: i64) -> Value {
    Value::fixnum(n)
}

/// A one-field global cell.
fn cell(rt: &mut Runtime, v: Value) -> Value {
    let c = rt.heap.make_bloblet(fixpt_heap::layout::kind("bloblet"), 1, 0, true);
    rt.heap.set_bloblet_slot(c, 2, v);
    c
}

fn run(rt: &mut Runtime, word: Value) -> Result<Vec<Value>, Trap> {
    let mut m = Machine::with_fuel(10_000_000);
    m.run_in_runtime(rt, word)?;
    Ok(m.ds)
}

/// `fact`, a closure in a global, calling itself through the global, its
/// argument slot 0 of its frame: `(lambda (n) (if (< n 1) 1 (* n (fact (- n 1)))))`.
#[test]
fn a_recursive_closure_through_a_global() {
    let mut rt = Runtime::new();
    let g = cell(&mut rt, Value::FALSE);
    let mut b = WordBuilder::new();
    let els = b.label();
    b.slot(0).lit(fx(1)).prim("<").zbranch(els).lit(fx(1)).ret();
    b.place(els);
    b.slot(0).slot(0).lit(fx(1)).prim("-").global(g).call_closure(1).runtime("*", 2).ret();
    let body = b.build(&mut rt.heap, "fact");
    // Top level: make the closure, store it, call it with 10.
    let mut t = WordBuilder::new();
    t.closure(body, 0).global_set(g).lit(fx(10)).global(g).call_closure(1).prim("exit");
    let top = t.build(&mut rt.heap, "top");
    assert_eq!(run(&mut rt, top).unwrap(), [fx(3628800)]);
}

/// A flat closure: `((lambda (n) (lambda (m) (+ n m))) 5)` copies `n` in,
/// and applied to 37 reads it as free value 0.
#[test]
fn a_closure_carries_its_free_values() {
    let mut rt = Runtime::new();
    let mut inner = WordBuilder::new();
    inner.free(0).slot(0).prim("+").ret();
    let inner = inner.build(&mut rt.heap, "adder");
    let mut outer = WordBuilder::new();
    outer.slot(0).closure(inner, 1).ret();
    let outer = outer.build(&mut rt.heap, "make-adder");
    let mut t = WordBuilder::new();
    t.lit(fx(37)).lit(fx(5)).closure(outer, 0).call_closure(1).call_closure(1).prim("exit");
    let top = t.build(&mut rt.heap, "top");
    assert_eq!(run(&mut rt, top).unwrap(), [fx(42)]);
}

/// A loop as a tail call: 200,000 iterations, three times the return
/// stack's limit on calls, with no stack growing.
#[test]
fn tail_calls_do_not_grow_the_stacks() {
    let mut rt = Runtime::new();
    let g = cell(&mut rt, Value::FALSE);
    // (lambda (i acc) (if (= i 0) acc (loop (- i 1) (+ acc 1))))
    let mut b = WordBuilder::new();
    let els = b.label();
    b.slot(0).lit(fx(0)).prim("eq").zbranch(els).slot(1).ret();
    b.place(els);
    b.slot(0).lit(fx(1)).prim("-").slot(1).lit(fx(1)).prim("+").global(g).tailcall(2);
    let body = b.build(&mut rt.heap, "loop");
    let mut t = WordBuilder::new();
    t.closure(body, 0).global_set(g).lit(fx(200_000)).lit(fx(0)).global(g).call_closure(2).prim("exit");
    let top = t.build(&mut rt.heap, "top");
    assert_eq!(run(&mut rt, top).unwrap(), [fx(200_000)]);
}

/// A call allocates nothing.
#[test]
fn calls_allocate_nothing() {
    let mut rt = Runtime::new();
    let mut id = WordBuilder::new();
    id.slot(0).ret();
    let id = id.build(&mut rt.heap, "id");
    let g = cell(&mut rt, Value::FALSE);
    let mut t = WordBuilder::new();
    let top_l = t.label();
    let done = t.label();
    t.closure(id, 0).global_set(g).lit(fx(100_000));
    t.place(top_l).prim("dup").lit(fx(0)).prim("eq").zbranch(done);
    t.prim("exit");
    t.place(done).global(g).call_closure(1).lit(fx(1)).prim("-").branch(top_l);
    let top = t.build(&mut rt.heap, "top");
    let used = rt.heap.used();
    assert_eq!(run(&mut rt, top).unwrap(), [fx(0)]);
    // The one closure the top word makes: header, word, trailer. The
    // 100,000 calls add nothing. (Unless a bug-finding collection policy
    // is on, whose fillers change the count: see `Heap::gc_every`.)
    if rt.heap.gc_every == 0 {
        assert_eq!(rt.heap.used(), used + 3, "the calls allocated");
    }
}

/// Runtime primitives, and their failures as traps.
#[test]
fn primitives_are_called_and_their_errors_trapped() {
    let mut rt = Runtime::new();
    let s = rt.heap.make_string("ab");
    let t = rt.heap.make_string("cd");
    let mut b = WordBuilder::new();
    b.lit(s).lit(t).runtime("string-append", 2).prim("exit");
    let w = b.build(&mut rt.heap, "t");
    let out = run(&mut rt, w).unwrap();
    assert_eq!(fixpt_runtime::write_value(&rt.heap, out[0]), "\"abcd\"");

    let mut b = WordBuilder::new();
    b.lit(fx(1)).lit(fx(0)).runtime("quotient", 2).prim("exit");
    let w = b.build(&mut rt.heap, "div0");
    assert!(matches!(run(&mut rt, w), Err(Trap::Prim(_))));
}

/// A slot past the stack, or a free value the closure lacks, traps; so
/// does calling what is not a closure.
#[test]
fn frames_and_calls_are_checked() {
    let mut rt = Runtime::new();
    let mut body = WordBuilder::new();
    body.slot(3).ret();
    let body = body.build(&mut rt.heap, "reads-past");
    let mut t = WordBuilder::new();
    t.lit(fx(1)).closure(body, 0).call_closure(1).prim("exit");
    let top = t.build(&mut rt.heap, "top");
    assert_eq!(run(&mut rt, top), Err(Trap::Field { routine: "slot" }));

    let mut body = WordBuilder::new();
    body.free(0).ret();
    let body = body.build(&mut rt.heap, "no-free");
    let mut t = WordBuilder::new();
    t.closure(body, 0).call_closure(0).prim("exit");
    let top = t.build(&mut rt.heap, "top");
    assert_eq!(run(&mut rt, top), Err(Trap::Field { routine: "free" }));

    let mut t = WordBuilder::new();
    t.lit(fx(1)).lit(fx(2)).call_closure(1).prim("exit");
    let top = t.build(&mut rt.heap, "not-a-closure");
    assert_eq!(run(&mut rt, top), Err(Trap::Type { routine: "call" }));
}

/// Words are checked as they are made.
#[test]
fn a_word_that_would_run_off_its_end_is_refused() {
    let mut rt = Runtime::new();
    let mut b = WordBuilder::new();
    b.lit(fx(1));
    let err = b.try_build(&mut rt.heap, "falls-off").expect_err("refused");
    assert!(err.contains("must end"), "{err}");
    let mut b = WordBuilder::new();
    b.prim("slot");
    let err = b.try_build(&mut rt.heap, "no-operand").expect_err("refused");
    assert!(err.contains("needs 1 operand"), "{err}");
    let _ = SELF;
}
