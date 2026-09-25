//! Running FX-26: lowered to annotated Scheme (`docs/fx26.md`, plan step 5)
//! and run on both engines, which must agree.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

/// The value of `program`'s last expression, the same on both engines.
fn run(program: &str) -> String {
    let mut answers = Vec::new();
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = Fx26Session::with_backend(backend).expect("starts");
        let v = s.run_program(program).unwrap_or_else(|e| panic!("does not check: {e}\n{program}"));
        answers.push(v.unwrap_or_else(|e| format!("!! {e}")));
    }
    assert_eq!(answers[0], answers[1], "the engines disagree on:\n{program}");
    answers.pop().expect("two")
}

/// What the last form of `program` lowers to.
fn code(program: &str) -> String {
    let mut s = Fx26Session::with_backend(Backend::Ast).expect("starts");
    let forms = s.checker.read_in(fixpt_read::FileId(0), program).expect("reads");
    let mut last = String::new();
    for f in &forms {
        last = s.run(f).expect("checks").code;
    }
    last
}

#[test]
fn the_papers_examples_run() {
    // C1, `twice` of an increment, from 5.
    assert_eq!(run(include_str!("programs/bidirectional/twice.fx")), "7");
    // C3: the continuation is called with 0, then 1 is added.
    assert_eq!(run(include_str!("programs/bidirectional/cwcc.fx")), "1");
}

#[test]
fn prompts_and_composable_continuations_run() {
    // The abort's 5 goes to the handler, which returns it.
    assert_eq!(run(include_str!("programs/bidirectional/own-abort.fx")), "5");
    // `k` adds 1; `(k (k 1))` is 3, and the body adds 1 to that.
    assert_eq!(run(include_str!("programs/bidirectional/capture-and-resume.fx")), "4");
    // The mark set around the capture is in the captured continuation.
    assert_eq!(run(include_str!("programs/run/marks-of.fx")), "(7)");
}

#[test]
fn marks_run() {
    let p = "(let ((key (the (mark-key int @m) (make-continuation-mark-key))))
               (with-mark key 1 (lambda () (first-mark key 0))))";
    assert_eq!(run(p), "1");
}

/// A second `define` shadows: code written before it keeps the first.
#[test]
fn a_redefinition_shadows_rather_than_assigns() {
    assert_eq!(run(include_str!("programs/run/shadowing.fx")), "6");
}

#[test]
fn recursion_and_state_run() {
    assert_eq!(run(include_str!("programs/run/recursion.fx")), "(55 . 1000)");
    assert_eq!(run(include_str!("programs/run/state.fx")), "42");
    assert_eq!(run("(define c (ref int @c) (new 0)) (set c 3)"), "#u");
}

/// Checking does not rule out every failure: the empty list is a pair type's
/// value too.
#[test]
fn a_run_time_error_is_reported_as_one() {
    let v = run("(car (the (listof int @l) nil))");
    assert!(v.starts_with("!! "), "{v}");
}

/// What the checker proved rides along: the standard `+` is integrable and
/// its application pure; a private cell's allocation does not escape.
#[test]
fn the_checkers_facts_are_in_the_lowered_code() {
    let c = code("(+ 1 2)");
    assert!(c.contains("(integrable +)") && c.contains("(pure)"), "{c}");
    assert!(c.contains("(basis checked)"), "{c}");
    let c = code("(let ((r (new 1))) (get r))");
    assert!(c.contains("(no-escape)"), "{c}");
    // A local that shadows a standard name is not the standard binding.
    let c = code("((lambda ((car (subr pure (int) int))) (car 1)) (lambda ((x int)) x))");
    assert!(!c.contains("(integrable car)"), "{c}");
    assert!(c.contains("(fx:car 1)"), "{c}");
}

/// And the compiled engine acts on it: the integrable call becomes one
/// primitive instruction, with no global load.
#[test]
fn the_compiler_uses_the_facts() {
    use fixpt_engine::compile::disassemble;
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let forms = s
        .checker
        .read_in(fixpt_read::FileId(0), "(define f (subr pure (int int) int) (lambda (a b) (+ a b)))")
        .expect("reads");
    s.run(&forms[0]).expect("runs");
    let heap = &s.scheme.rt.heap;
    let sym = heap.intern_existing("fx:f").expect("defined");
    let closure = heap.global(heap.symbol_global_slot(sym));
    let code = heap.obj_ref(closure, 0);
    assert!(heap.is_a(code, fixpt_heap::ObjType::Code));
    let listing = disassemble(heap, code);
    assert!(listing.contains("prim"), "{listing}");
    assert!(!listing.contains("global"), "{listing}");
}
