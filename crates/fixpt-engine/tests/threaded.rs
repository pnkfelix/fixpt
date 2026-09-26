//! The Rust inner interpreter on threaded words.

use fixpt_engine::threaded::{Machine, Trap, WordBuilder, examples, prim, primitive_word};
use fixpt_heap::layout::threaded::WORD_NAME;
use fixpt_heap::{Heap, Value};

fn run(heap: &mut Heap, word: Value, args: &[i64]) -> Result<Vec<Value>, Trap> {
    // Fuel enough for any test here, so a runaway program fails, not hangs.
    let mut m = Machine::with_fuel(10_000_000);
    m.ds.extend(args.iter().map(|a| Value::fixnum(*a)));
    m.run(heap, word)?;
    Ok(m.ds)
}

fn fixnums(vs: &[Value]) -> Vec<i64> {
    vs.iter().map(|v| v.as_fixnum()).collect()
}

#[test]
fn fib_recurses() {
    let mut heap = Heap::new();
    let fib = examples::fib(&mut heap);
    let got: Vec<i64> = (0..15).map(|i| fixnums(&run(&mut heap, fib, &[i]).unwrap())[0]).collect();
    assert_eq!(got, [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377]);
}

#[test]
fn a_loop_branches_back() {
    let mut heap = Heap::new();
    let w = examples::sum_to(&mut heap);
    assert_eq!(fixnums(&run(&mut heap, w, &[0, 100]).unwrap()), [5050]);
}

#[test]
fn words_call_words_and_cons_survives_collection() {
    let mut heap = Heap::with_semispace(1024);
    let w = examples::sum_by_list(&mut heap);
    let root = heap.push_root(w);
    for _ in 0..3 {
        let w = heap.root_at(root);
        assert_eq!(fixnums(&run(&mut heap, w, &[2000]).unwrap()), [2001000]);
    }
}

#[test]
fn execute_runs_words_and_primitives() {
    let mut heap = Heap::new();
    let plus = primitive_word(&mut heap, "+");
    let mut b = WordBuilder::new();
    b.lit(Value::fixnum(3)).lit(Value::fixnum(4)).lit(plus).prim("execute");
    b.lit(Value::fixnum(10)).lit(prim("-")).prim("execute").prim("exit");
    let w = b.build(&mut heap, "t");
    assert_eq!(fixnums(&run(&mut heap, w, &[]).unwrap()), [-3]);
}

#[test]
fn a_word_reads_its_own_fields() {
    let mut heap = Heap::new();
    let mut b = WordBuilder::new();
    b.recurse().prim("exit");
    let w = b.build(&mut heap, "me");
    let mut b = WordBuilder::new();
    b.lit(w).lit(Value::fixnum(WORD_NAME as i64)).prim("field@").prim("exit");
    let reader = b.build(&mut heap, "reader");
    let out = run(&mut heap, reader, &[]).unwrap();
    assert_eq!(out, [heap.intern("me")]);
}

#[test]
fn traps() {
    let mut heap = Heap::new();
    let mut b = WordBuilder::new();
    b.lit(Value::TRUE).lit(Value::fixnum(1)).prim("+").prim("exit");
    let w = b.build(&mut heap, "bad-add");
    assert_eq!(run(&mut heap, w, &[]), Err(Trap::Type { routine: "+" }));

    let mut b = WordBuilder::new();
    b.prim("drop").prim("exit");
    let w = b.build(&mut heap, "underflow");
    assert_eq!(run(&mut heap, w, &[]), Err(Trap::Underflow { routine: "drop" }));

    let mut b = WordBuilder::new();
    b.lit(Value::fixnum(fixpt_heap::value::FIXNUM_MAX)).lit(Value::fixnum(1)).prim("+").prim("exit");
    let w = b.build(&mut heap, "overflow");
    assert_eq!(run(&mut heap, w, &[]), Err(Trap::Overflow { routine: "+" }));

    // Words are frozen: no program can rewrite one.
    let mut b = WordBuilder::new();
    b.lit(Value::fixnum(0)).lit_self().lit(Value::fixnum(5)).prim("field!").prim("exit");
    let w = b.build(&mut heap, "self-modifying");
    assert_eq!(run(&mut heap, w, &[]), Err(Trap::Field { routine: "field!" }));

    let mut b = WordBuilder::new();
    b.lit(Value::TRUE).prim("execute").prim("exit");
    let w = b.build(&mut heap, "execute-true");
    assert_eq!(run(&mut heap, w, &[]), Err(Trap::NotAWord));

    let mut b = WordBuilder::new();
    b.recurse().prim("exit");
    let w = b.build(&mut heap, "forever");
    assert_eq!(run(&mut heap, w, &[]), Err(Trap::OutOfFuel));
}
