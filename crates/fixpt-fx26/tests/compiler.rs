//! The compiler written in FX-26 (`src/compile.fx`): programs read, parsed
//! and compiled to threaded words in FX-26, run on the threaded machine,
//! against the evaluator written in FX-26 and the lowering to Scheme
//! (`PLAN.md` §11, step 9d).

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

/// All three ways; they must agree. Returns the value.
fn three(program: &str) -> String {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let compiled = s.compile_with_own_compiler(program).unwrap_or_else(|e| panic!("the FX-26 front end: {e}\n{program}"));
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let evaluated = s.eval_with_own_evaluator(program).unwrap_or_else(|e| panic!("the FX-26 front end: {e}\n{program}"));
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let lowered = s.run_program(program).unwrap_or_else(|e| panic!("does not check: {e}\n{program}"));
    let lowered = lowered.unwrap_or_else(|e| format!("!! {e}"));
    assert_eq!(evaluated, lowered, "the evaluator and the lowering disagree on:\n{program}");
    assert_eq!(compiled, lowered, "the compiled words and the lowering disagree on:\n{program}");
    compiled
}

#[test]
fn small_programs() {
    assert_eq!(three("(+ 1 2)"), "3");
    assert_eq!(three("(let* ((a 1) (b (+ a 1))) (if (and (< a b) (or #f #t)) 'yes 'no))"), "yes");
    assert_eq!(three("(define f (subr pure (int) int) (lambda (n) (if (= n 0) 1 (* n (f (- n 1)))))) (f 10)"), "3628800");
    assert_eq!(three("(the (listof int @l) (cons 1 (cons 2 nil)))"), "(1 2)");
    assert_eq!(three("(let ((r (the (ref int @r) (new 1)))) (begin (set r (+ (get r) 41)) (get r)))"), "42");
    assert_eq!(three("(letrec ((even (subr pure (int) bool) (lambda (n) (if (= n 0) #t (odd (- n 1))))) (odd (subr pure (int) bool) (lambda (n) (if (= n 0) #f (even (- n 1)))))) (even 10))"), "#t");
    assert_eq!(three("(string-append \"ab\" (symbol->string 'cd))"), "\"abcd\"");
    assert_eq!(three("(sum a 1)"), "#<sum a>");
    assert_eq!(three("((lambda ((x int)) ((lambda ((y int)) (+ x y)) 2)) 40)"), "42");
    assert_eq!(three("(tagcase (the (sumof (a int) (b (productof (1 int) (2 int)))) (sum b (product (1 3) (2 4)))) (a n n) (b (x y) (+ x y)))"), "7");
}

#[test]
fn test_programs() {
    for p in [
        include_str!("programs/bidirectional/twice.fx"),
        include_str!("programs/bloblet/point.fx"),
        include_str!("programs/bloblet/bytes.fx"),
        include_str!("programs/bloblet/array-sum.fx"),
        include_str!("programs/bloblet/else-narrows.fx"),
        include_str!("programs/run/recursion.fx"),
        include_str!("programs/run/shadowing.fx"),
        include_str!("programs/run/state.fx"),
    ] {
        three(p);
    }
}

/// What the compiler cannot do yet, it says, rather than miscompiling.
#[test]
fn what_is_not_compiled_yet_says_so() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let out = s.compile_with_own_compiler("(extract (product (a 1)) a)").expect("parses");
    assert!(out.starts_with("!! compile: not yet compiled: extract"), "{out}");
    let out = s.compile_with_own_compiler("(car (the (listof int @l) nil))").expect("parses");
    assert!(out.starts_with("!! "), "a run-time error is reported: {out}");
}

/// Every test program that checks, control ones included, compiled and run
/// on the threaded machine against the lowering; disagreements reported
/// together. Programs with `extract` wait for the checker written in FX-26.
#[test]
fn every_program_compiled() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut report = Vec::new();
    let mut ran = 0;
    for sub in ["bidirectional", "control", "run", "pldi89", "bloblet"] {
        let mut names: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
        names.sort();
        for path in names {
            let program = std::fs::read_to_string(&path).unwrap();
            if program.contains("(extract") || program.contains("define-datatype") {
                continue;
            }
            let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
            let lowered = match s.run_program(&program) {
                Ok(v) => v.unwrap_or_else(|e| format!("!! {e}")),
                Err(_) => continue, // written to be rejected
            };
            let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
            let compiled = s.compile_with_own_compiler(&program).map_err(|e| e.to_string());
            ran += 1;
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            if compiled.as_deref() != Ok(lowered.as_str()) {
                report.push(format!("{sub}/{name}: compiled {compiled:?}, lowered {lowered:?}"));
            }
        }
    }
    assert!(report.is_empty(), "{} of {ran} disagree:\n{}", report.len(), report.join("\n"));
    // The corpus has 14 that check and need no `extract`; fewer means the
    // test stopped finding them.
    assert!(ran >= 14, "only {ran} programs ran");
}
