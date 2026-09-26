//! The routines for code compiled from FX-26 (frames, closures, calls,
//! globals, the runtime's primitives) on every machine: the Rust one, the
//! hand-encoded one, and the stencils at each level, the same results and
//! traps.
#![allow(unsafe_code)]

use fixpt_engine::threaded::{Machine, Trap, WordBuilder};
use fixpt_heap::Value;
use fixpt_native::stencil::{StencilMachine, opt_levels};
use fixpt_native::threaded::NativeMachine;
use fixpt_runtime::Runtime;

const FUEL: u64 = 10_000_000;

fn fx(n: i64) -> Value {
    Value::fixnum(n)
}

fn cell(rt: &mut Runtime, v: Value) -> Value {
    let c = rt.heap.make_bloblet(fixpt_heap::layout::kind("bloblet"), 1, 0, true);
    rt.heap.set_bloblet_slot(c, 2, v);
    c
}

/// Every machine on `word`, fresh from `setup` each time (globals are state);
/// all must agree. The results, written.
fn all(setup: impl Fn(&mut Runtime) -> Value) -> Result<Vec<String>, Trap> {
    let show = |rt: &Runtime, r: Result<Vec<Value>, Trap>| r.map(|vs| vs.iter().map(|v| fixpt_runtime::write_value(&rt.heap, *v)).collect::<Vec<_>>());
    let mut rt = Runtime::new();
    let w = setup(&mut rt);
    let mut m = Machine::with_fuel(FUEL);
    let r = m.run_in_runtime(&mut rt, w).map(|()| m.ds.clone());
    let rust = show(&rt, r);
    let mut rt = Runtime::new();
    let w = setup(&mut rt);
    let r = NativeMachine::new().run_in_runtime(&mut rt, w, &[], FUEL);
    assert_eq!(show(&rt, r), rust, "the hand-encoded machine disagrees");
    for opt in opt_levels() {
        let mut rt = Runtime::new();
        let w = setup(&mut rt);
        let r = StencilMachine::new(opt).expect("built").run_in_runtime(&mut rt, w, &[], FUEL);
        assert_eq!(show(&rt, r), rust, "the stencils at -O{opt} disagree");
    }
    rust
}

#[test]
fn a_recursive_closure_through_a_global() {
    let out = all(|rt| {
        let g = cell(rt, Value::FALSE);
        let mut b = WordBuilder::new();
        let els = b.label();
        b.slot(0).lit(fx(1)).prim("<").zbranch(els).lit(fx(1)).ret();
        b.place(els);
        b.slot(0).slot(0).lit(fx(1)).prim("-").global(g).call_closure(1).runtime("*", 2).ret();
        let body = b.build(&mut rt.heap, "fact");
        let mut t = WordBuilder::new();
        t.closure(body, 0).global_set(g).lit(fx(10)).global(g).call_closure(1).prim("exit");
        t.build(&mut rt.heap, "top")
    });
    assert_eq!(out.unwrap(), ["3628800"]);
}

#[test]
fn flat_closures_and_tail_calls() {
    let out = all(|rt| {
        let mut inner = WordBuilder::new();
        inner.free(0).slot(0).prim("+").ret();
        let inner = inner.build(&mut rt.heap, "adder");
        let mut outer = WordBuilder::new();
        outer.slot(0).closure(inner, 1).ret();
        let outer = outer.build(&mut rt.heap, "make-adder");
        let g = cell(rt, Value::FALSE);
        let mut lp = WordBuilder::new();
        let els = lp.label();
        lp.slot(0).lit(fx(0)).prim("eq").zbranch(els).slot(1).ret();
        lp.place(els);
        lp.slot(0).lit(fx(1)).prim("-").slot(1).lit(fx(1)).prim("+").global(g).tailcall(2);
        let lp = lp.build(&mut rt.heap, "loop");
        let mut t = WordBuilder::new();
        t.lit(fx(37)).lit(fx(5)).closure(outer, 0).call_closure(1).call_closure(1);
        t.closure(lp, 0).global_set(g).lit(fx(200_000)).lit(fx(0)).global(g).call_closure(2).prim("exit");
        t.build(&mut rt.heap, "top")
    });
    assert_eq!(out.unwrap(), ["42", "200000"]);
}

#[test]
fn checks_trap_alike() {
    let slot = all(|rt| {
        let mut body = WordBuilder::new();
        body.slot(3).ret();
        let body = body.build(&mut rt.heap, "reads-past");
        let mut t = WordBuilder::new();
        t.lit(fx(1)).closure(body, 0).call_closure(1).prim("exit");
        t.build(&mut rt.heap, "top")
    });
    assert_eq!(slot, Err(Trap::Field { routine: "slot" }));
    let free = all(|rt| {
        let mut body = WordBuilder::new();
        body.free(0).ret();
        let body = body.build(&mut rt.heap, "no-free");
        let mut t = WordBuilder::new();
        t.closure(body, 0).call_closure(0).prim("exit");
        t.build(&mut rt.heap, "top")
    });
    assert_eq!(free, Err(Trap::Field { routine: "free" }));
    let call = all(|rt| {
        let mut t = WordBuilder::new();
        t.lit(fx(1)).lit(fx(2)).call_closure(1).prim("exit");
        t.build(&mut rt.heap, "not-a-closure")
    });
    assert_eq!(call, Err(Trap::Type { routine: "call" }));
    let prim = all(|rt| {
        let mut t = WordBuilder::new();
        t.lit(fx(1)).lit(fx(0)).runtime("quotient", 2).prim("exit");
        t.build(&mut rt.heap, "div0")
    });
    assert!(matches!(prim, Err(Trap::Prim(_))), "{prim:?}");
}

#[test]
fn prompts_and_marks_returned_through() {
    // Bodies that return normally: the prompt's and the mark's entries are
    // passed by on the way out, on every machine.
    let out = all(|rt| {
        let mut body = WordBuilder::new();
        body.lit(fx(41)).ret();
        let body = body.build(&mut rt.heap, "body");
        let mut handler = WordBuilder::new();
        handler.slot(0).ret();
        let handler = handler.build(&mut rt.heap, "handler");
        let mut t = WordBuilder::new();
        t.lit(fx(7)).closure(handler, 0).closure(body, 0).prim("prompt").lit(fx(1)).prim("+");
        t.lit(fx(3)).lit(fx(2)).closure(body, 0).prim("withmark");
        t.lit(fx(3)).lit(fx(0)).prim("firstmark").prim("exit");
        t.build(&mut rt.heap, "top")
    });
    assert_eq!(out.unwrap(), ["42", "41", "0"]);
}

#[test]
fn primitives_collect_with_everything_moving() {
    // A collection at every safepoint, which moves every object: a runtime
    // primitive's safepoint must find the frames, the return entries, the
    // word running and the closure, wherever each machine keeps them.
    let out = all(|rt| {
        rt.heap.gc_every = 1;
        let g = cell(rt, Value::FALSE);
        let mut lp = WordBuilder::new();
        let els = lp.label();
        lp.slot(0).lit(fx(0)).prim("eq").zbranch(els).slot(1).free(0).runtime("list", 2).ret();
        lp.place(els);
        lp.slot(0).lit(fx(1)).prim("-").slot(0).slot(1).runtime("list", 2).global(g).tailcall(2);
        let lp = lp.build(&mut rt.heap, "loop");
        let mut t = WordBuilder::new();
        t.lit(fx(1)).lit(fx(2)).runtime("vector", 2).closure(lp, 1).global_set(g);
        t.lit(fx(3)).lit(Value::NULL).global(g).call_closure(2).lit(fx(9)).runtime("list", 2).prim("exit");
        t.build(&mut rt.heap, "top")
    });
    assert_eq!(out.unwrap(), ["(((1 (2 (3 ()))) #(1 2)) 9)"]);
}

#[test]
fn a_loop_marking_in_tail_position_runs_in_constant_space() {
    // loop(n): with-mark key n (λ. if n = 0 then first-mark key else loop(n-1)),
    // the with-mark in tail position: 100,000 iterations, far past the
    // return stack's limit if each stacked a mark, and the mark seen at the
    // end is the last one.
    let out = all(|rt| {
        let key = cell(rt, Value::FALSE);
        let g = cell(rt, Value::FALSE);
        let mut body = WordBuilder::new();
        let els = body.label();
        body.free(0).lit(fx(0)).prim("eq").zbranch(els).global(key).lit(fx(-1)).prim("firstmark").ret();
        body.place(els);
        body.free(0).lit(fx(1)).prim("-").global(g).tailcall(1);
        let body = body.build(&mut rt.heap, "body");
        let mut lp = WordBuilder::new();
        lp.global(key).slot(0).slot(0).closure(body, 1).prim("withmark-tail");
        let lp = lp.build(&mut rt.heap, "loop");
        let mut t = WordBuilder::new();
        t.closure(lp, 0).global_set(g).lit(fx(100_000)).global(g).call_closure(1).prim("exit");
        t.build(&mut rt.heap, "top")
    });
    assert_eq!(out.unwrap(), ["0"]);
}

#[test]
fn continuations_captured_and_composed_with_everything_moving() {
    // (prompt tag (+ 1 (callcomp (λ (k) (k (k 1))) tag)) handler): the
    // continuation is "add one", composed twice, so 1 + (1 + (1 + 1)).
    // Collecting at every safepoint, which moves every object, while the
    // stacks are captured into a continuation and composed back.
    let out = all(|rt| {
        rt.heap.gc_every = 1;
        let tag = cell(rt, Value::FALSE);
        let mut procw = WordBuilder::new();
        procw.lit(fx(1)).slot(0).call_closure(1).slot(0).call_closure(1).ret();
        let procw = procw.build(&mut rt.heap, "twice-k");
        let mut thunk = WordBuilder::new();
        thunk.lit(fx(1)).closure(procw, 0).global(tag).prim("callcomp").prim("+").ret();
        let thunk = thunk.build(&mut rt.heap, "body");
        let mut handler = WordBuilder::new();
        handler.slot(0).ret();
        let handler = handler.build(&mut rt.heap, "handler");
        let mut t = WordBuilder::new();
        t.global(tag).closure(handler, 0).closure(thunk, 0).prim("prompt").prim("exit");
        t.build(&mut rt.heap, "top")
    });
    assert_eq!(out.unwrap(), ["4"]);
}
