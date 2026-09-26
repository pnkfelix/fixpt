//! The native inner interpreters, checked against the Rust one on the same
//! words: the same results, and the same traps. "Native" is the hand-encoded
//! machine and the stencil machine at every optimisation level it was built
//! at.

use fixpt_engine::threaded::{Machine, Trap, WordBuilder, examples, prim, primitive_word};
use fixpt_heap::layout::threaded::WORD_NAME;
use fixpt_heap::{Heap, Value};
use fixpt_native::stencil::{StencilMachine, opt_levels};
use fixpt_native::threaded::NativeMachine;

const FUEL: u64 = 10_000_000;

fn rust(heap: &mut Heap, word: Value, args: &[Value]) -> Result<Vec<Value>, Trap> {
    let mut m = Machine::with_fuel(FUEL);
    m.ds.extend_from_slice(args);
    m.run(heap, word)?;
    Ok(m.ds)
}

/// Every machine on the same word and arguments; they must agree.
fn both(heap: &mut Heap, word: Value, args: &[Value]) -> Result<Vec<Value>, Trap> {
    let root = heap.push_root(word);
    let r = rust(heap, word, args);
    let word = heap.root_at(root);
    let n = NativeMachine::new().run(heap, word, args, FUEL);
    assert_eq!(n, r, "the hand-encoded machine and the Rust machine disagree");
    for opt in opt_levels() {
        let word = heap.root_at(root);
        let s = StencilMachine::new(opt).expect("built").run(heap, word, args, FUEL);
        assert_eq!(s, r, "the stencil machine at -O{opt} and the Rust machine disagree");
    }
    heap.pop_roots_to(root);
    r
}

#[test]
fn stencils_were_built_at_every_level() {
    // The build script warns and carries on without a nightly compiler; on
    // this project's machines there is one, so their absence is a failure.
    assert_eq!(opt_levels(), ["0", "1", "2", "3", "s"]);
}

fn fx(n: i64) -> Value {
    Value::fixnum(n)
}

#[test]
fn fib() {
    let mut heap = Heap::new();
    let fib = examples::fib(&mut heap);
    for i in 0..20 {
        both(&mut heap, fib, &[fx(i)]).unwrap();
    }
    assert_eq!(both(&mut heap, fib, &[fx(20)]).unwrap(), [fx(6765)]);
}

#[test]
fn a_loop() {
    let mut heap = Heap::new();
    let w = examples::sum_to(&mut heap);
    assert_eq!(both(&mut heap, w, &[fx(0), fx(1000)]).unwrap(), [fx(500500)]);
}

#[test]
fn cons_calls_out_and_survives_collection() {
    let mut heap = Heap::with_semispace(1024);
    let w = examples::sum_by_list(&mut heap);
    let root = heap.push_root(w);
    let mut m = NativeMachine::new();
    let before = heap.gc_count;
    for _ in 0..3 {
        let w = heap.root_at(root);
        assert_eq!(m.run(&mut heap, w, &[fx(3000)], FUEL).unwrap(), [fx(4501500)]);
    }
    let during = heap.gc_count - before;
    eprintln!("collections while the native machine ran: {during}");
    assert!(during > 0, "the test is meant to collect under native code");
    for opt in opt_levels() {
        let mut m = StencilMachine::new(opt).expect("built");
        let before = heap.gc_count;
        let w = heap.root_at(root);
        assert_eq!(m.run(&mut heap, w, &[fx(3000)], FUEL).unwrap(), [fx(4501500)]);
        assert!(heap.gc_count > before);
    }
    let w = heap.root_at(root);
    both(&mut heap, w, &[fx(500)]).unwrap();
}

#[test]
fn a_list_built_natively_is_a_list() {
    let mut heap = Heap::with_semispace(512);
    let w = examples::iota(&mut heap);
    let out = NativeMachine::new().run(&mut heap, w, &[fx(100)], FUEL).unwrap();
    let items = heap.list_to_vec(out[0]).unwrap();
    assert_eq!(items, (1..=100).map(fx).collect::<Vec<_>>());
}

#[test]
fn execute_and_fields() {
    let mut heap = Heap::new();
    let plus = primitive_word(&mut heap, "+");
    let fib = examples::fib(&mut heap);
    let mut b = WordBuilder::new();
    b.lit(fx(3)).lit(fx(4)).lit(plus).prim("execute");
    b.lit(fx(10)).lit(prim("-")).prim("execute");
    b.lit(fx(10)).lit(fib).prim("execute");
    b.lit_self().lit(fx(WORD_NAME as i64)).prim("field@").prim("exit");
    let w = b.build(&mut heap, "t");
    let out = both(&mut heap, w, &[]).unwrap();
    assert_eq!(out, [fx(-3), fx(55), heap.intern("t")]);

    // `field@` on a bloblet with no trailer takes the Rust path.
    let bare = heap.make_bloblet(32, 3, 8, false);
    heap.set_bloblet_slot(bare, 2, fx(77));
    let mut b = WordBuilder::new();
    b.lit(bare).lit(fx(2)).prim("field@").prim("exit");
    let w = b.build(&mut heap, "bare");
    assert_eq!(both(&mut heap, w, &[]).unwrap(), [fx(77)]);

    // `field!` on a bloblet that allows it.
    let mut b = WordBuilder::new();
    b.lit(fx(5)).lit(bare).lit(fx(3)).prim("field!").lit(bare).lit(fx(3)).prim("field@").prim("exit");
    let w = b.build(&mut heap, "store");
    assert_eq!(both(&mut heap, w, &[]).unwrap(), [fx(5)]);
}

fn word(heap: &mut Heap, f: impl FnOnce(&mut WordBuilder)) -> Value {
    let mut b = WordBuilder::new();
    f(&mut b);
    b.build(heap, "t")
}

#[test]
fn traps_agree() {
    let mut heap = Heap::new();
    let cases: Vec<(Value, Trap)> = vec![
        (word(&mut heap, |b| { b.lit(Value::TRUE).lit(fx(1)).prim("+").prim("exit"); }), Trap::Type { routine: "+" }),
        (word(&mut heap, |b| { b.lit(fx(1)).lit(Value::NULL).prim("<").prim("exit"); }), Trap::Type { routine: "<" }),
        (
            word(&mut heap, |b| { b.lit(fx(fixpt_heap::value::FIXNUM_MAX)).lit(fx(1)).prim("+").prim("exit"); }),
            Trap::Overflow { routine: "+" },
        ),
        (
            word(&mut heap, |b| { b.lit(fx(fixpt_heap::value::FIXNUM_MIN)).lit(fx(1)).prim("-").prim("exit"); }),
            Trap::Overflow { routine: "-" },
        ),
        (word(&mut heap, |b| { b.lit(fx(1)).prim("car").prim("exit"); }), Trap::Type { routine: "car" }),
        (word(&mut heap, |b| { b.lit_self().lit(fx(1)).prim("field@").prim("exit"); }), Trap::Field { routine: "field@" }),
        (word(&mut heap, |b| { b.lit_self().lit(fx(99)).prim("field@").prim("exit"); }), Trap::Field { routine: "field@" }),
        (word(&mut heap, |b| { b.lit_self().lit(fx(-3)).prim("field@").prim("exit"); }), Trap::Field { routine: "field@" }),
        (word(&mut heap, |b| { b.lit(fx(1)).lit(fx(2)).prim("field@").prim("exit"); }), Trap::Type { routine: "field@" }),
        (
            word(&mut heap, |b| { b.lit(fx(0)).lit_self().lit(fx(5)).prim("field!").prim("exit"); }),
            Trap::Field { routine: "field!" },
        ),
        (word(&mut heap, |b| { b.lit(Value::TRUE).prim("execute").prim("exit"); }), Trap::NotAWord),
        (word(&mut heap, |b| { b.lit(fx(0)).prim("execute").prim("exit"); }), Trap::NoRoutine(0)),
        (word(&mut heap, |b| { b.lit(fx(-4)).prim("execute").prim("exit"); }), Trap::NoRoutine(-4)),
        (word(&mut heap, |b| { b.lit(fx(1000)).prim("execute").prim("exit"); }), Trap::NoRoutine(1000)),
        (word(&mut heap, |b| { let l = b.label(); b.place(l).branch(l); }), Trap::OutOfFuel),
        (word(&mut heap, |b| { let l = b.label(); b.place(l).lit(fx(1)).branch(l); }), Trap::StackOverflow),
        (word(&mut heap, |b| { b.recurse().prim("exit"); }), Trap::TooDeep),
    ];
    // A pair, to give execute something that is a reference but no word.
    let pair = heap.cons(fx(1), fx(2));
    let w = word(&mut heap, |b| { b.lit(pair).prim("execute").prim("exit"); });
    for (w, trap) in cases.into_iter().chain([(w, Trap::NotAWord)]) {
        assert_eq!(both(&mut heap, w, &[]), Err(trap));
    }
}

#[test]
fn halt_stops_in_the_middle() {
    let mut heap = Heap::new();
    let inner = word(&mut heap, |b| { b.lit(fx(1)).prim("halt").lit(fx(2)).prim("exit"); });
    let mut b = WordBuilder::new();
    b.call(&heap, inner).lit(fx(3)).prim("exit");
    let w = b.build(&mut heap, "outer");
    assert_eq!(both(&mut heap, w, &[]).unwrap(), [fx(1)]);
}

#[test]
fn code_sizes() {
    let hand = NativeMachine::new().code_bytes();
    eprintln!("hand-encoded machine: {hand} bytes");
    for opt in opt_levels() {
        eprintln!("stencils -O{opt}: {} bytes", StencilMachine::new(opt).expect("built").code_bytes);
    }
    assert!(hand > 0);
}
