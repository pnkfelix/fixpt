use fixpt_scheme::Session;

fn ev(src: &str) -> String {
    let mut s = Session::new();
    match s.eval_to_string("<test>", src) {
        Ok(v) => v,
        Err(e) => format!("!! {e}"),
    }
}

#[test]
fn arithmetic() {
    assert_eq!(ev("(+ 1 2)"), "3");
    assert_eq!(ev("(* 6 7)"), "42");
    assert_eq!(ev("(/ 1 3)"), "1/3");
    assert_eq!(ev("(expt 2 100)"), "1267650600228229401496703205376");
}

#[test]
fn closures_and_recursion() {
    assert_eq!(ev("(define (fact n) (if (= n 0) 1 (* n (fact (- n 1))))) (fact 20)"),
               "2432902008176640000");
}

#[test]
fn tail_calls_are_proper() {
    // Volume is the point: a leaked frame per call shows up as memory, not as a
    // wrong answer. Under `gc-stress` each call also collects, so 200_000 calls
    // means 200_000 full collections — minutes of work to re-establish
    // something the ordinary run already covers at full size.
    let n = if cfg!(feature = "gc-stress") { 2_000 } else { 200_000 };
    assert_eq!(
        ev(&format!(
            "(define (loop n acc) (if (= n 0) acc (loop (- n 1) (+ acc 1)))) (loop {n} 0)"
        )),
        n.to_string()
    );
}

#[test]
fn derived_forms() {
    assert_eq!(ev("(let loop ((i 0) (acc '())) (if (= i 5) (reverse acc) (loop (+ i 1) (cons i acc))))"),
               "(0 1 2 3 4)");
    assert_eq!(ev("(cond ((assv 2 '((1 a) (2 b))) => cadr) (else 'none))"), "b");
    assert_eq!(ev("(case 3 ((1 2) 'low) ((3 4) 'mid) (else 'high))"), "mid");
    assert_eq!(ev("(do ((i 0 (+ i 1)) (s 0 (+ s i))) ((= i 5) s))"), "10");
}

#[test]
fn quasiquote() {
    assert_eq!(ev("(let ((x 3) (y '(4 5))) `(1 2 ,x ,@y 6))"), "(1 2 3 4 5 6)");
}

#[test]
fn call_cc_escapes() {
    assert_eq!(ev("(+ 1 (call/cc (lambda (k) (k 41) 999)))"), "42");
}

#[test]
fn dynamic_wind_runs_after_on_escape() {
    assert_eq!(
        ev("(let ((log '()))
              (call/cc (lambda (k)
                (dynamic-wind (lambda () (set! log (cons 'in log)))
                              (lambda () (k 'escaped))
                              (lambda () (set! log (cons 'out log))))))
              (reverse log))"),
        "(in out)"
    );
}

#[test]
fn conditions() {
    assert_eq!(
        ev("(guard (e (#t (list 'caught (error-object-message e))))
              (error \"boom\" 1 2))"),
        "(caught \"boom\")"
    );
    assert_eq!(ev("(guard (e (#t 'caught)) (car '()))"), "caught");
}

#[test]
fn records() {
    assert_eq!(
        ev("(define-record-type point (make-point x y) point? (x point-x) (y point-y set-point-y!))
            (define p (make-point 1 2))
            (list (point? p) (point-x p) (begin (set-point-y! p 9) (point-y p)))"),
        "(#t 1 9)"
    );
}

#[test]
fn values() {
    assert_eq!(ev("(call-with-values (lambda () (values 1 2 3)) list)"), "(1 2 3)");
    assert_eq!(ev("(let-values (((a b) (values 1 2))) (+ a b))"), "3");
}

#[test]
fn promises() {
    assert_eq!(ev("(define p (delay (begin 'once 7))) (list (force p) (force p))"), "(7 7)");
}

#[test]
fn strings_chars_vectors() {
    assert_eq!(ev("(string-append \"ab\" \"cd\")"), "\"abcd\"");
    assert_eq!(ev("(list->string (map char-upcase (string->list \"hi\")))"), "\"HI\"");
    assert_eq!(ev("(vector-map + #(1 2) #(10 20))"), "#(11 22)");
}

#[test]
fn errors_report_source_position() {
    let mut s = Session::new();
    let e = s.eval_str("<test>", "(+ 1 (undefined-thing))").unwrap_err();
    assert!(format!("{e}").contains("unbound variable: undefined-thing"), "{e}");
}
