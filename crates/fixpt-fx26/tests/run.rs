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

/// A second `define`, at a type every use can take, assigns: code written
/// before it sees the second, as in Scheme and at the REPL
/// (`Checker::top_defining`).
#[test]
fn a_redefinition_assigns() {
    assert_eq!(run(include_str!("programs/run/redefinition.fx")), "8");
}

/// Variadic procedures: `vlambda`, calls of any number of arguments, and
/// `apply` (`programs/run/variadic.fx`).
#[test]
fn variadic_procedures_run() {
    assert_eq!(run(include_str!("programs/run/variadic.fx")), "1011");
}

/// `list`: calls of 0 to 10 arguments, and `list` as a value, a `vsubr`
/// that `apply` spreads a list over (`programs/run/list.fx`).
#[test]
fn list_runs() {
    assert_eq!(run(include_str!("programs/run/list.fx")), "5539");
    assert_eq!(run(include_str!("programs/run/list-regions.fx")), "54");
}

/// `apply` gives a variadic procedure a fresh list (F11): one that is at
/// `acyclic` as its type says, not the caller's, which may be written after.
/// A cyclic list is an error, not a loop.
#[test]
fn apply_gives_a_fresh_list() {
    assert_eq!(run(include_str!("programs/run/apply-fresh.fx")), "22");
    let v = run(include_str!("programs/native/apply-cyclic.fx"));
    assert!(v.starts_with("!! ") && v.contains("expected a list"), "{v}");
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

/// What the checker proved rides along: the standard `+` is integrable (as
/// `%fx26-add`, which fails past a fixnum) and its application pure; a private cell's allocation does not escape.
#[test]
fn the_checkers_facts_are_in_the_lowered_code() {
    let c = code("(+ 1 2)");
    assert!(c.contains("(integrable %fx26-add)") && c.contains("(pure)"), "{c}");
    assert!(c.contains("(basis checked)"), "{c}");
    let c = code("(let ((r (new 1))) (get r))");
    assert!(c.contains("(no-escape)"), "{c}");
    // A closure returned holds what it captured, whatever its type says.
    let c = code("(let ((x (cons 1 2))) (lambda () (begin x 1)))");
    assert!(!c.contains("(no-escape)"), "{c}");
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
    let heap = &s.scheme.runtime_unrooted_ref().heap;
    let sym = heap.intern_existing("fx:f").expect("defined");
    let closure = heap.global(heap.symbol_global_slot(sym));
    let code = heap.closure_code(closure);
    assert!(heap.is_a(code, fixpt_heap::ObjType::Code));
    let listing = disassemble(heap, code);
    assert!(listing.contains("prim"), "{listing}");
    assert!(!listing.contains("global"), "{listing}");
}

/// Compiled by the compiler written in FX-26, a form's code is the words it
/// made, those not shown for an earlier form: a definition's lambda once,
/// and the program word, which each form remakes, each time.
#[test]
fn cellular_forms_show_their_new_words() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    s.strategy = fixpt_fx26::session::Strategy::Cellular;
    s.show_words = true;
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/run/sq.fx")).unwrap();
    let forms = s.checker.read_in(fixpt_read::FileId(0), &text).expect("reads");
    let codes: Vec<String> = forms.iter().map(|f| s.run(f).expect("runs").code).collect();
    let words = |c: &str| c.lines().filter(|l| l.starts_with("word ")).map(|l| l.split(' ').nth(1).unwrap().to_string()).collect::<Vec<_>>();
    assert_eq!(words(&codes[0]), ["program", "lambda@45"], "{}", codes[0]);
    assert_eq!(words(&codes[1]), ["program"], "{}", codes[1]);
}

/// Compiled and run on a cellular machine, a form that loops stops at the
/// session's step limit, as it does lowered, on each machine: by recursion,
/// or by calling a continuation again.
#[test]
fn cellular_forms_stop_at_the_step_limit() {
    type Run = fn(&mut fixpt_runtime::Runtime, fixpt_heap::Value, &[fixpt_heap::Value]) -> Result<fixpt_heap::Value, String>;
    let machines: [Run; 3] = [
        fixpt_engine::cellular::run_word,
        fixpt_native::cellular::run_word,
        fixpt_native::cellular::run_word_registers,
    ];
    for (name, i, m) in ["spin", "resume"].into_iter().flat_map(|n| machines.into_iter().enumerate().map(move |(i, m)| (n, i, m))) {
        let text = std::fs::read_to_string(format!("{}/tests/programs/diverge/{name}.fx", env!("CARGO_MANIFEST_DIR"))).unwrap();
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        s.strategy = fixpt_fx26::session::Strategy::Cellular;
        s.register_code = i == 2;
        s.scheme.runtime_unrooted().run_word = Some(m);
        s.set_step_limit(Some(100_000));
        let forms = s.checker.read_in(fixpt_read::FileId(0), &text).expect("reads");
        let outs: Vec<_> = forms.iter().map(|f| s.run(f).expect("runs").value).collect();
        assert_eq!(outs.last(), Some(&Err("evaluation step limit exceeded".to_string())), "{name} on machine {i}");
    }
}

/// A primitive that walks a list ends on a cyclic one, with an error: its
/// type says no `spin` (`tests/programs/diverge/cyclic-reverse.fx`).
#[test]
fn a_primitive_given_a_cyclic_list_fails_rather_than_loops() {
    let text = include_str!("programs/diverge/cyclic-reverse.fx");
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let forms = s.checker.read_in(fixpt_read::FileId(0), text).expect("reads");
    let outs: Vec<_> = forms.iter().map(|f| s.run(f).expect("runs").value).collect();
    let last = outs.last().expect("a value").clone().expect_err("fails");
    assert!(last.contains("proper list"), "{last}");
}
