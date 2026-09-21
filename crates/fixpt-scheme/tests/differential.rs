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
    let mut ast = Session::new();
    let mut vm = Session::compiled();
    let a = outcome(&mut ast, src);
    let b = outcome(&mut vm, src);
    assert_eq!(a, b, "engines disagree on: {src}");
    assert!(!a.contains("|!"), "both engines failed on {src}: {a}");
}

/// For cases where failing is the point.
#[track_caller]
fn agree_failing(src: &str) {
    let mut ast = Session::new();
    let mut vm = Session::compiled();
    let a = outcome(&mut ast, src);
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
    for src in [
        "(define (adder n) (lambda (x) (+ x n))) ((adder 3) 4)",
        "(define (compose f g) (lambda (x) (f (g x)))) ((compose car cdr) '(1 2 3))",
        // Deep enough that anything but a proper tail call would be noticed.
        "(define (count n) (if (= n 0) 'done (count (- n 1)))) (count 300000)",
        // Non-tail recursion deep enough to overflow a native stack.
        "(define (build n) (if (= n 0) '() (cons n (build (- n 1))))) (length (build 50000))",
        "(define (make-counter) (let ((n 0)) (lambda () (set! n (+ n 1)) n)))
         (define c (make-counter)) (c) (c) (list (c) ((make-counter)))",
        // A closure capturing a closure capturing a mutable binding.
        "(define (outer)
           (let ((total 0))
             (lambda (x) (let ((step (lambda (d) (set! total (+ total d)))))
                           (step x) total))))
         (define f (outer)) (f 1) (f 2) (f 3)",
    ] {
        agree(src);
    }
}

#[test]
fn recursion_shapes() {
    for src in [
        "(letrec ((even? (lambda (n) (if (= n 0) #t (odd? (- n 1)))))
                  (odd?  (lambda (n) (if (= n 0) #f (even? (- n 1))))))
           (list (even? 1000) (odd? 1001)))",
        // letrec* order: a later initialiser reads an earlier binding.
        "(letrec ((a 1) (b (+ a 1)) (c (+ b 1))) (list a b c))",
        "(let loop ((i 0) (acc '())) (if (= i 6) (reverse acc) (loop (+ i 1) (cons (* i i) acc))))",
        "(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))) (fib 20)",
        "(define (ack m n)
           (cond ((= m 0) (+ n 1))
                 ((= n 0) (ack (- m 1) 1))
                 (else (ack (- m 1) (ack m (- n 1))))))
         (ack 2 3)",
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
        "(define (find-first p xs)
           (call/cc (lambda (return)
             (for-each (lambda (x) (if (p x) (return x))) xs)
             #f)))
         (list (find-first even? '(1 3 4 5)) (find-first even? '(1 3 5)))",
        // Re-entrant: the continuation is called again after it has returned.
        "(define k #f)
         (define n 0)
         (define r (+ 1 (call/cc (lambda (c) (set! k c) 1))))
         (set! n (+ n 1))
         (if (< n 3) (k n))
         (list n r)",
        // Winding.
        "(define trace '())
         (define (note x) (set! trace (cons x trace)))
         (dynamic-wind (lambda () (note 'in)) (lambda () (note 'body) 'v) (lambda () (note 'out)))
         (reverse trace)",
        // Escaping through a dynamic-wind runs the after thunk.
        "(define trace '())
         (call/cc (lambda (k)
           (dynamic-wind (lambda () (set! trace (cons 'in trace)))
                         (lambda () (k 'escaped))
                         (lambda () (set! trace (cons 'out trace))))))
         (reverse trace)",
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
        "(define trace '())
         (guard (e (#t (reverse (cons e trace))))
           (dynamic-wind (lambda () (set! trace (cons 'in trace)))
                         (lambda () (raise 'x))
                         (lambda () (set! trace (cons 'out trace)))))",
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
    let mut ast = Session::new();
    let mut vm = Session::compiled();
    for src in forms {
        let a = outcome(&mut ast, src);
        let b = outcome(&mut vm, src);
        assert_eq!(a, b, "engines disagree on: {src}");
    }
}
