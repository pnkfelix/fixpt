//! The evaluator written in FX-26 (`src/evaluator.fx`), reading and parsing
//! with the reader and the parser written in FX-26, against the same
//! programs lowered to Scheme (`PLAN.md` §11, step 9b).

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

/// Both ways; they must agree. Returns the value.
fn both(program: &str) -> String {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let ours = s.eval_with_own_evaluator(program).unwrap_or_else(|e| panic!("the FX-26 front end: {e}\n{program}"));
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let scheme = s.run_program(program).unwrap_or_else(|e| panic!("does not check: {e}\n{program}"));
    let scheme = scheme.unwrap_or_else(|e| format!("!! {e}"));
    assert_eq!(ours, scheme, "the evaluator and the lowering disagree on:\n{program}");
    ours
}

#[test]
fn small_programs() {
    assert_eq!(both("(+ 1 2)"), "3");
    assert_eq!(both("(let* ((a 1) (b (+ a 1))) (if (and (< a b) (or #f #t)) 'yes 'no))"), "yes");
    assert_eq!(both("(define f (subr spin (int) int) (lambda (n) (if (= n 0) 1 (* n (f (- n 1)))))) (f 10)"), "3628800");
    assert_eq!(both("(the (listof int @l) (cons 1 (cons 2 nil)))"), "(1 2)");
    assert_eq!(both("(let ((r (the (ref int @r) (new 1)))) (begin (set r (+ (get r) 41)) (get r)))"), "42");
    assert_eq!(both("(extract (product (a 1) (b \"two\")) b)"), "\"two\"");
    assert_eq!(both("(letrec ((even (subr spin (int) bool) (lambda (n) (if (= n 0) #t (odd (- n 1))))) (odd (subr spin (int) bool) (lambda (n) (if (= n 0) #f (even (- n 1)))))) (even 10))"), "#t");
    assert_eq!(both("(string-append \"ab\" (symbol->string 'cd))"), "\"abcd\"");
    assert_eq!(both("(sum a 1)"), "#<sum a>");
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
    ] {
        both(p);
    }
}

#[test]
fn errors_stop_the_program() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let out = s.eval_with_own_evaluator("(car (the (listof int @l) nil))").expect("parses");
    assert!(out.starts_with("!! a pair is expected"), "{out}");
}

/// Every test program that checks, both ways, reported together.
#[test]
fn control_and_marks() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut report = Vec::new();
    for sub in ["bidirectional", "control", "run", "pldi89"] {
        let mut names: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
        names.sort();
        for path in names {
            let program = std::fs::read_to_string(&path).unwrap();
            let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
            let scheme = match s.run_program(&program) {
                Ok(v) => v.unwrap_or_else(|e| format!("!! {e}")),
                Err(_) => continue, // written to be rejected
            };
            let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
            let ours = s.eval_with_own_evaluator(&program).map_err(|e| e.to_string());
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            if ours.as_deref() != Ok(scheme.as_str()) {
                report.push(format!("{sub}/{name}: evaluator {ours:?}, Scheme {scheme:?}"));
            }
        }
    }
    assert!(report.is_empty(), "disagreements:\n{}", report.join("\n"));
}
