//! Disassemble compiled procedures, to see what the compiler actually emits.
use fixpt_engine::compile::disassemble;
use fixpt_engine::Backend;
use fixpt_heap::ObjType;
use fixpt_scheme::Session;

fn show(s: &mut Session, name: &str) {
    let sym = s.rt.heap.intern_existing(name).expect("defined");
    let slot = s.rt.heap.symbol_global_slot(sym);
    let v = s.rt.heap.global(slot);
    assert!(s.rt.heap.is_a(v, ObjType::Closure), "{name} is not a closure");
    let code = s.rt.heap.obj_ref(v, 0);
    println!("{}", disassemble(&s.rt.heap, code));
}

/// Count opcodes across every compiled procedure reachable from the globals.
fn histogram(s: &Session) -> (Vec<(String, usize)>, usize, usize) {
    use fixpt_core::lower::CODE_CONSTS;
    use fixpt_engine::compile::op;
    let heap = &s.rt.heap;

    // Every code object reachable from a global closure, plus the nested ones
    // in their constant vectors.
    let mut todo: Vec<fixpt_heap::Value> = Vec::new();
    for sym in heap.symbols_slice().to_vec() {
        let v = heap.global(heap.symbol_global_slot(sym));
        if heap.is_a(v, ObjType::Closure) {
            todo.push(heap.obj_ref(v, 0));
        }
    }
    let mut seen: Vec<fixpt_heap::Value> = Vec::new();
    let mut counts: std::collections::HashMap<u32, usize> = Default::default();
    let mut words = 0usize;
    while let Some(code) = todo.pop() {
        if !heap.is_a(code, ObjType::Code) || seen.contains(&code) {
            continue;
        }
        seen.push(code);
        if !fixpt_core::lower::is_compiled(heap, code) {
            continue;
        }
        // The instructions are the code bloblet's suffix.
        let n = heap.bloblet_head(code).bytes / 4;
        words += n;
        let mut pc = 0usize;
        while pc < n {
            let opcode = heap.bloblet_u32(code, pc);
            *counts.entry(opcode).or_default() += 1;
            pc += op::len(opcode);
        }
        let consts = heap.bloblet_slot(code, CODE_CONSTS);
        if heap.is_a(consts, ObjType::Vector) {
            for i in 0..heap.obj_len(consts) {
                todo.push(heap.obj_ref(consts, i));
            }
        }
    }
    let mut v: Vec<(String, usize)> =
        counts.into_iter().map(|(k, n)| (op::name(k).to_string(), n)).collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    (v, words, seen.len())
}

fn main() {
    let mut s = Session::with_backend(Backend::Bytecode);
    s.eval_str(
        "<x>",
        "(define (square x) (* x x))
         (define (loop n acc) (if (= n 0) acc (loop (- n 1) (+ acc n))))
         (define (adder n) (lambda (x) (+ x n)))
         (define (counter) (let ((n 0)) (lambda () (set! n (+ n 1)) n)))",
    )
    .expect("compiles");
    for f in ["square", "loop", "adder", "counter"] {
        show(&mut s, f);
    }

    // Does a checked purity claim reach the compiler?
    let mut t = Session::with_backend(Backend::Bytecode);
    t.eval_str(
        "<p>",
        "(define (g) (begin (begin '(%fx-note (pure) (basis checked)) (display \"x\")) 1))",
    )
    .expect("compiles");
    println!("--- purity claim ---");
    show(&mut t, "g");

    let (hist, words, procs) = histogram(&s);
    let total: usize = hist.iter().map(|(_, n)| n).sum();
    println!("--- across {procs} compiled procedures, {words} instruction words ---");
    for (name, n) in hist.iter().take(12) {
        println!("  {name:<12} {n:>5}  {:>5.1}%", 100.0 * *n as f64 / total as f64);
    }
    let overhead: usize = hist
        .iter()
        .filter(|(n, _)| n == "global" || n == "call" || n == "tail-call")
        .map(|(_, n)| n)
        .sum();
    println!("  global+call+tail-call = {:.1}% of all instructions", 100.0 * overhead as f64 / total as f64);
}
