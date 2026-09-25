//! The two engines must agree.
//!
//! This is the load-bearing test for the compiler. The AST engine is the one
//! that was conformance-checked against the reference implementations, so the
//! question for the bytecode engine is not "is it right" in the abstract but
//! "does it do what the checked engine does" — on values, on printed output,
//! and on error messages, which is where a compiler bug is most likely to hide
//! behind an answer that merely *looks* plausible.
//!
//! Each case runs in its own pair of sessions, so a case that corrupts state
//! cannot make a later one pass or fail spuriously.

use fixpt_scheme::Session;

/// A budget, so that a program which fails to terminate fails the test instead
/// of hanging it. Generous enough for the deep-recursion cases below; small
/// enough that a runaway is a diagnosis rather than a wedged CI job.
const STEP_LIMIT: u64 = 20_000_000;

/// Scale a workload down when every safepoint collects.
///
/// Under `gc-stress` a collection happens at every single safepoint, so a loop
/// of *n* iterations performs *n* full collections — and a case like
/// `(build 50000)`, whose live heap grows as it goes, copies billions of words
/// before it finishes. None of that volume adds evidence: what `gc-stress`
/// tests is whether each safepoint hands the collector a complete root set, and
/// that shows up in the first dozen collections or not at all. The *shapes*
/// stay identical; only the counts shrink.
const fn work(n: usize) -> usize {
    if cfg!(feature = "gc-stress") { if n > 2_000 { 2_000 } else { n } } else { n }
}

/// Likewise for the exponential case, where the cost is in the branching.
const fn depth(n: usize) -> usize {
    if cfg!(feature = "gc-stress") { 12 } else { n }
}

fn ast() -> Session {
    let mut s = Session::new();
    s.engine.set_step_limit(Some(STEP_LIMIT));
    s
}

fn compiled() -> Session {
    let mut s = Session::compiled();
    s.engine.set_step_limit(Some(STEP_LIMIT));
    s
}

/// What one program produced: what it printed, and what it evaluated to or how
/// it failed. Errors are compared as text on purpose — an engine that reports
/// a different message for the same mistake has diverged.
fn outcome(session: &mut Session, src: &str) -> String {
    let (printed, result) = session.eval_capturing("<diff>", src);
    let value = match result {
        Ok(v) => fixpt_runtime::write_value(&session.rt.heap, v),
        Err(e) => format!("!{e}"),
    };
    format!("{printed}|{value}")
}

#[track_caller]
fn agree(src: &str) {
    let mut a_session = ast();
    let mut vm = compiled();
    let a = outcome(&mut a_session, src);
    let b = outcome(&mut vm, src);
    assert_eq!(a, b, "engines disagree on: {src}");
    assert!(!a.contains("|!"), "both engines failed on {src}: {a}");
}

/// For cases where failing is the point.
#[track_caller]
fn agree_failing(src: &str) {
    let mut a_session = ast();
    let mut vm = compiled();
    let a = outcome(&mut a_session, src);
    let b = outcome(&mut vm, src);
    assert_eq!(a, b, "engines disagree on: {src}");
    assert!(a.contains("|!"), "expected a failure from {src}: {a}");
}

#[test]
fn arithmetic_and_numbers() {
    for src in [
        "(+ 1 2 3)",
        "(* 1/3 3)",
        "(/ 1 3)",
        "(exact->inexact 1/3)",
        "(expt 2 100)",
        "(- (expt 2 64) 1)",
        "(quotient 17 5)",
        "(remainder -17 5)",
        "(modulo -17 5)",
        "(max 1 2.0 3)",
        "(sqrt 16)",
        "(number->string 255 16)",
        "(string->number \"1e3\")",
        "(list (exact? 1/2) (inexact? 1.5) (integer? 2.0))",
    ] {
        agree(src);
    }
}

#[test]
fn closures_and_tail_calls() {
    // Sized here so the loop counts can shrink under `gc-stress` without the
    // programs themselves changing shape.
    let count = format!(
        "(define (count n) (if (= n 0) 'done (count (- n 1)))) (count {})",
        work(300_000)
    );
    let build = format!(
        "(define (build n) (if (= n 0) '() (cons n (build (- n 1))))) (length (build {}))",
        work(50_000)
    );
    for src in [
        "(define (adder n) (lambda (x) (+ x n))) ((adder 3) 4)",
        "(define (compose f g) (lambda (x) (f (g x)))) ((compose car cdr) '(1 2 3))",
        // Deep enough that anything but a proper tail call would be noticed.
        count.as_str(),
        // Non-tail recursion deep enough to overflow a native stack.
        build.as_str(),
        "(define (make-counter) (let ((n 0)) (lambda () (set! n (+ n 1)) n)))
         (define c (make-counter)) (c) (c) (list (c) ((make-counter)))",
        // A closure capturing a closure capturing a mutable binding.
        include_str!("programs/differential/closure-over-closure.scm"),
    ] {
        agree(src);
    }
}

#[test]
fn recursion_shapes() {
    let fib = format!(
        "(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))) (fib {})",
        depth(20)
    );
    for src in [
        "(letrec ((even? (lambda (n) (if (= n 0) #t (odd? (- n 1)))))
                  (odd?  (lambda (n) (if (= n 0) #f (even? (- n 1))))))
           (list (even? 1000) (odd? 1001)))",
        // letrec* order: a later initialiser reads an earlier binding.
        "(letrec ((a 1) (b (+ a 1)) (c (+ b 1))) (list a b c))",
        "(let loop ((i 0) (acc '())) (if (= i 6) (reverse acc) (loop (+ i 1) (cons (* i i) acc))))",
        fib.as_str(),
        include_str!("programs/differential/ackermann.scm"),
    ] {
        agree(src);
    }
}

#[test]
fn continuations() {
    for src in [
        "(+ 1 (call/cc (lambda (k) (k 1) 99)))",
        "(call/cc (lambda (k) (+ 1 (k 41))))",
        // Escaping from inside a fold.
        include_str!("programs/differential/escape-from-fold.scm"),
        // Re-entrant: the continuation is called again after it has returned.
        include_str!("programs/differential/reentrant-continuation.scm"),
        // Winding.
        "(define trace '())
         (define (note x) (set! trace (cons x trace)))
         (dynamic-wind (lambda () (note 'in)) (lambda () (note 'body) 'v) (lambda () (note 'out)))
         (reverse trace)",
        // Escaping through a dynamic-wind runs the after thunk.
        include_str!("programs/differential/escape-through-wind.scm"),
        "(call-with-values (lambda () (values 1 2 3)) list)",
        "(call-with-values (lambda () (values)) (lambda args args))",
        "(+ 1 (call-with-values (lambda () (values 2)) (lambda (x) x)))",
    ] {
        agree(src);
    }
}

#[test]
fn conditions() {
    for src in [
        "(guard (e (#t (list 'caught (error-object-message e) (error-object-irritants e))))
           (error \"boom\" 1 2))",
        "(guard (e ((symbol? e) (list 'sym e)) (else (list 'other e))) (raise 'oops))",
        "(with-exception-handler (lambda (e) (* e 10)) (lambda () (+ 1 (raise-continuable 4))))",
        // A handler that itself escapes.
        "(call/cc (lambda (k) (with-exception-handler (lambda (e) (k (list 'escaped e)))
                                (lambda () (raise 'bad)))))",
        // Unwinding out of a guard still runs after-thunks.
        include_str!("programs/differential/guard-unwinds.scm"),
    ] {
        agree(src);
    }
}

#[test]
fn errors_report_alike() {
    for src in [
        "(car '())",
        "(vector-ref (vector 1 2) 5)",
        "(undefined-variable-name)",
        "((lambda (x) x))",
        "((lambda (x) x) 1 2)",
        "(1 2 3)",
        "(+ 'a 1)",
        "(letrec ((a b) (b 1)) a)",
        "(string-ref \"abc\" 10)",
        "(/ 1 0)",
        // Both engines park the consumer in a control frame while the producer
        // runs, so a producer that is not applicable at all leaves that frame
        // pending. Pinned here because the two get there by different routes.
        "(call-with-values 5 list)",
        "(call-with-values (lambda () (values 1 2)) 7)",
        "(apply + 1 2)",
        "(vector-ref '(1 2) 0)",
    ] {
        agree_failing(src);
    }
}

#[test]
fn data_and_printing() {
    for src in [
        "(list 1 'a \"s\" #\\c #t '() #(1 2) 1/2 2.5)",
        "(let ((x (list 1 2))) (set-cdr! (cdr x) x) (write x) 'done)",
        "`(1 ,(+ 1 1) ,@(list 3 4))",
        "(vector->list (list->vector '(1 2 3)))",
        "(string->list \"héllo\")",
        "(assq 'b '((a 1) (b 2)))",
        "(list (equal? '(1 #(2 3)) '(1 #(2 3))) (eqv? 2.0 2.0) (eq? 'a 'a))",
        "(apply string-append (map symbol->string '(a b c)))",
        "(let ((v (make-vector 3 0))) (vector-fill! v 7) v)",
        "(list (force (delay (+ 1 2))) (force (make-promise 3)))",
        "(display (list 1 \"two\" #\\3)) (newline) 'ok",
    ] {
        agree(src);
    }
}

#[test]
fn higher_order_and_library() {
    for src in [
        "(map + '(1 2 3) '(10 20 30))",
        "(for-each display '(1 2 3)) 'done",
        "(let ((acc '())) (vector-for-each (lambda (x) (set! acc (cons x acc))) #(1 2 3)) acc)",
        "(apply max '(3 1 4 1 5))",
        "(list (member 2 '(1 2 3)) (memq 'c '(a b)))",
        "(list (list-tail '(1 2 3 4) 2) (list-ref '(1 2 3) 1))",
        "(list (string-length \"hello\") (string->list \"ab\") (list->string (list #\\a #\\b)))",
        "(let-values (((q r) (values (quotient 7 2) (remainder 7 2)))) (list q r))",
        "(do ((i 0 (+ i 1)) (a '() (cons i a))) ((= i 4) a))",
        "(case 3 ((1 2) 'low) ((3 4) 'mid) (else 'high))",
        "(cond ((assv 2 '((1 a) (2 b))) => cadr) (else 'none))",
        "(let* ((x 1) (y (+ x 1))) (list x y))",
        "(list (and 1 2 3) (or #f 2) (and) (or))",
        "(when #t 'yes)",
        "(unless #f 'no)",
    ] {
        agree(src);
    }
}

#[test]
fn state_across_forms_in_one_session() {
    // The REPL path: many forms expanded into one arena, each seeing the last.
    let forms = [
        "(define acc '())",
        "(define (push! x) (set! acc (cons x acc)))",
        "(push! 1)",
        "(push! 2)",
        "(define (twice f) (lambda (x) (f (f x))))",
        "((twice (lambda (n) (* n 3))) 2)",
        "acc",
        "(set! acc (reverse acc))",
        "acc",
    ];
    let mut a_session = ast();
    let mut vm = compiled();
    for src in forms {
        let a = outcome(&mut a_session, src);
        let b = outcome(&mut vm, src);
        assert_eq!(a, b, "engines disagree on: {src}");
    }
}

/// Generators built from `call/cc`.
///
/// The hardest thing either engine has to get right. A generator captures a
/// continuation, returns *past* it so the stack shrinks, then re-enters it —
/// so a captured continuation has to survive the frames it was captured under
/// being gone, and the two engines have to agree on what "the rest of the
/// computation" was even though one keeps it in environment chains and the
/// other in stack frames.
#[test]
fn coroutines() {
    // Same-fringe: two trees with different shapes but the same leaves, walked
    // lazily in lockstep. Nothing else in the suite makes control jump between
    // two suspended computations.
    let same_fringe = include_str!("programs/differential/same-fringe.scm");
    agree(same_fringe);

    // A continuation captured inside a loop and re-entered after the loop has
    // finished: the frames it was captured under are long gone.
    //
    // The re-entry counter is defined *before* the capture on purpose. All of
    // these forms are one top-level body, so anything defined after the capture
    // is inside the captured continuation and gets re-initialised on re-entry —
    // a guard declared there would reset itself and loop forever. (It did, in
    // an earlier draft of this test; both engines looped identically, which is
    // its own small piece of evidence.)
    agree(include_str!("programs/differential/reenter-finished-loop.scm"));

    // A continuation used as a value: stored, passed around, applied by `apply`.
    agree(
        "(define ks '())
         (define (collect x) (call/cc (lambda (k) (set! ks (cons k ks)) x)))
         (list (collect 1) (collect 2) (length ks))",
    );
}
