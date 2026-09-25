//! `syntax-rules` and hygiene.
//!
//! Every case runs on both engines, though macros are expanded before either
//! sees the program — agreement here says the expansion is the same program
//! whichever engine runs it.

use fixpt_engine::Backend;
use fixpt_scheme::Session;

fn both(src: &str) -> String {
    let src = src.to_string();
    // The expander recurses on the Rust stack, one level per nested macro use,
    // and a test thread's default stack is smaller than the `fixpt` binary's.
    // Give it the same room the binary has, so the runaway-expansion test
    // reaches the expander's limit rather than the thread's.
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let mut answers = Vec::new();
            for backend in [Backend::Ast, Backend::Bytecode] {
                let mut s = Session::with_backend(backend);
                answers.push(match s.eval_to_string("<test>", &src) {
                    Ok(v) => v,
                    Err(e) => format!("!! {e}"),
                });
            }
            assert_eq!(answers[0], answers[1], "the engines disagree on:\n{src}");
            answers.pop().expect("two answers")
        })
        .expect("spawns")
        .join()
        .unwrap_or_else(|e| std::panic::resume_unwind(e))
}

/// The stack `fixpt` itself runs on.
const STACK: usize = 256 << 20;

// ------------------------------------------- the built-in forms are hygienic

/// These were wrong before M9: the derived forms rewrote to raw `if`,
/// `lambda`, `call-with-current-continuation`… and re-expanded them in the
/// user's environment.
#[test]
fn derived_forms_ignore_local_rebindings_of_what_they_expand_into() {
    assert_eq!(both("(let ((if list)) (cond (#t 'one) (else 'two)))"), "one");
    assert_eq!(both("(let ((lambda 5)) (force (delay 1)))"), "1");
    assert_eq!(
        both(
            "(let ((call-with-current-continuation 0) (raise-continuable 0) (list 0))
               (guard (e (#t (cons 'caught e))) (raise 'boom)))"
        ),
        "(caught . boom)"
    );
    assert_eq!(both("(let ((let 1) (begin 2) (if 3)) (do ((i 0 (+ i 1))) ((= i 3) 'done)))"), "done");
    assert_eq!(both("(let ((cons 0) (append 0) (list 0)) (let ((x '(2 3))) `(1 ,@x ,(car x))))"), "(1 2 3 2)");
}

#[test]
fn a_quoted_rename_is_just_the_symbol() {
    assert_eq!(
        both("(define-syntax q (syntax-rules () ((_) '(if lambda tmp)))) (q)"),
        "(if lambda tmp)"
    );
    assert_eq!(
        both("(define-syntax q (syntax-rules () ((_) 'tmp))) (eq? (q) 'tmp)"),
        "#t"
    );
}

// ------------------------------------------------------------- hygiene

#[test]
fn an_introduced_binding_cannot_capture_the_users_variable() {
    assert_eq!(
        both(
            "(define-syntax swap! (syntax-rules () ((_ a b) (let ((tmp a)) (set! a b) (set! b tmp)))))
             (define tmp 1) (define other 2)
             (swap! tmp other)
             (list tmp other)"
        ),
        "(2 1)"
    );
}

#[test]
fn a_template_means_what_it_meant_where_the_macro_was_defined() {
    assert_eq!(
        both(
            "(define-syntax my-or
               (syntax-rules () ((_) #f) ((_ e) e) ((_ e r ...) (let ((t e)) (if t t (my-or r ...))))))
             (let ((if list) (t 5)) (my-or #f t))"
        ),
        "5"
    );
    // A helper defined after the macro, and shadowed at the use: the template
    // still refers to the global.
    assert_eq!(
        both(
            "(define-syntax call-helper (syntax-rules () ((_ x) (helper x))))
             (define (helper x) (* x 100))
             (list (call-helper 3) (let ((helper (lambda (x) 'captured))) (call-helper 3)))"
        ),
        "(300 300)"
    );
}

#[test]
fn a_literal_matches_by_binding_not_by_name() {
    let def = include_str!("programs/macros/my-cond.scm");
    assert_eq!(both(&format!("{def} (my-cond (#f 1) (else 2))")), "2");
    // Bound locally, `else` is an ordinary variable — here true — and the
    // clause an ordinary clause.
    assert_eq!(both(&format!("{def} (let ((else #t)) (my-cond (#f 1) (else 3)))")), "3");
    assert_eq!(both(&format!("{def} (let ((else #f)) (my-cond (#f 1) (else 3)))")), "none");
}

// ------------------------------------------------------------- patterns

#[test]
fn ellipsis_forms() {
    assert_eq!(
        both("(define-syntax flat (syntax-rules () ((_ (a ...) ...) '(a ... ...)))) (flat (1 2) (3) () (4 5))"),
        "(1 2 3 4 5)"
    );
    assert_eq!(
        both("(define-syntax pairs (syntax-rules () ((_ (k v) ...) '((k . v) ...)))) (pairs (a 1) (b 2))"),
        "((a . 1) (b . 2))"
    );
    // An ellipsis followed by more patterns (R7RS), and a dotted tail.
    assert_eq!(both("(define-syntax last (syntax-rules () ((_ a ... z) 'z))) (last 1 2 3)"), "3");
    // …which needs at least the elements after the ellipsis.
    let out = both("(define-syntax lst (syntax-rules () ((_ a ... y z) '(y z)))) (list (lst 1 2) (lst 1 2 3))");
    assert_eq!(out, "((1 2) (2 3))");
    let out = both("(define-syntax lst (syntax-rules () ((_ a ... y z) '(y z)))) (lst 1)");
    assert!(out.contains("no rule of `lst` matches (lst 1)"), "{out}");
    assert_eq!(both("(define-syntax rest (syntax-rules () ((_ a . r) 'r))) (rest 1 2 3)"), "(2 3)");
    assert_eq!(both("(define-syntax v (syntax-rules () ((_ #(a ...)) (list a ...)))) (v #(1 2 3))"), "(1 2 3)");
    assert_eq!(both("(define-syntax u (syntax-rules () ((_ _ b) b))) (u 1 2)"), "2");
    assert_eq!(
        both("(define-syntax d (syntax-rules () ((_ \"yes\" x) x) ((_ other x) 'no))) (list (d \"yes\" 1) (d 2 3))"),
        "(1 no)"
    );
}

#[test]
fn custom_and_escaped_ellipses() {
    assert_eq!(both("(define-syntax l (syntax-rules ::: () ((_ x :::) (list x :::)))) (l 1 2 3)"), "(1 2 3)");
    // A macro-defining macro: the inner template's ellipsis is escaped from the
    // outer one with `(... ...)`.
    assert_eq!(
        both(
            "(define-syntax def-lister
               (syntax-rules () ((_ name) (define-syntax name (syntax-rules () ((_ x (... ...)) (list 'x (... ...))))))))
             (def-lister lister)
             (lister a b c)"
        ),
        "(a b c)"
    );
}

// ---------------------------------------------------- where macros live

#[test]
fn macros_in_bodies_and_scoped_forms() {
    assert_eq!(
        both(include_str!("programs/macros/macro-in-body.scm")),
        "2"
    );
    assert_eq!(both("(let-syntax ((foo (syntax-rules () ((_ x) (* x 10))))) (foo 4))"), "40");
    // `letrec-syntax`: the macros can refer to each other.
    assert_eq!(
        both(
            "(letrec-syntax ((ev? (syntax-rules () ((_) #t) ((_ x . r) (od? . r))))
                             (od? (syntax-rules () ((_) #f) ((_ x . r) (ev? . r)))))
               (list (ev? a b) (ev? a b c)))"
        ),
        "(#t #f)"
    );
    // `let-syntax`: they cannot — the inner `foo` is the outer one.
    assert_eq!(
        both(
            "(define-syntax foo (syntax-rules () ((_) 'outer)))
             (let-syntax ((foo (syntax-rules () ((_) 'inner)))
                          (bar (syntax-rules () ((_) (foo)))))
               (bar))"
        ),
        "outer"
    );
}

#[test]
fn a_macro_can_expand_into_definitions() {
    let def = "(define-syntax define-two (syntax-rules () ((_ a b v) (begin (define a v) (define b v)))))";
    assert_eq!(both(&format!("{def} (define-two p q 7) (list p q)")), "(7 7)");
    assert_eq!(both(&format!("{def} (define (g) (define-two r s 8) (+ r s)) (g)")), "16");
}

#[test]
fn macros_persist_across_inputs() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = Session::with_backend(backend);
        s.eval_to_string("<1>", "(define-syntax inc! (syntax-rules () ((_ v) (set! v (+ v 1)))))")
            .expect("defines");
        s.eval_to_string("<2>", "(define n 41)").expect("defines");
        assert_eq!(s.eval_to_string("<3>", "(begin (inc! n) n)").ok().as_deref(), Some("42"));
    }
}

// --------------------------------------------------------------- errors

#[test]
fn errors_say_what_went_wrong() {
    let out = both("(define-syntax m (syntax-rules () ((_ a) a))) (m 1 2)");
    assert!(out.contains("no rule of `m` matches (m 1 2)"), "{out}");
    let out = both("(define-syntax m (syntax-rules () ((_ a a) a)))");
    assert!(out.contains("`a` appears twice"), "{out}");
    let out = both("(define-syntax m (syntax-rules () ((_ a ...) a))) (m 1 2)");
    assert!(out.contains("needs `...`"), "{out}");
    let out = both("(define-syntax m (syntax-rules () ((_ a) (a ...)))) (m 1)");
    assert!(out.contains("before this `...`"), "{out}");
    let out = both("(define-syntax m (syntax-rules () ((_ x) (+ 1 (m x))))) (m 1)");
    assert!(out.contains("nested more than"), "{out}");
    let out = both("(define-syntax m (syntax-rules () ((_) 1))) m");
    assert!(out.contains("is syntax"), "{out}");
}

// ------------------------------------------- R7RS 7.3, as library macros

/// R7RS §7.3 defines the derived expression types *as* `syntax-rules`
/// macros. Here they are, verbatim but renamed so as not to replace the
/// built-ins, and checked against them — the M9 demonstration that the derived
/// forms are re-expressible as library macros. `do` exercises string-literal
/// patterns (`"step"`), and `case` the `=>` literal.
const R7RS_DERIVED: &str = include_str!("programs/macros/r7rs-derived.scm");

#[test]
fn r7rs_derived_forms_as_macros_agree_with_the_built_ins() {
    let cases = [
        ("(r-cond (#f 1) ((assv 2 '((1 a) (2 b))) => cadr) (else 'none))", "(cond (#f 1) ((assv 2 '((1 a) (2 b))) => cadr) (else 'none))"),
        ("(r-cond ((+ 1 1)) (else 0))", "(cond ((+ 1 1)) (else 0))"),
        ("(r-case (* 2 3) ((2 3 5 7) 'prime) ((1 4 6 8 9) 'composite))", "(case (* 2 3) ((2 3 5 7) 'prime) ((1 4 6 8 9) 'composite))"),
        ("(r-case 'x ((a) 1) (else => (lambda (k) (list k 'fallback))))", "(case 'x ((a) 1) (else => (lambda (k) (list k 'fallback))))"),
        ("(list (r-and) (r-and 1 2) (r-and 1 #f 3) (r-or) (r-or #f 2) (r-or #f #f))", "(list (and) (and 1 2) (and 1 #f 3) (or) (or #f 2) (or #f #f))"),
        ("(r-let loop ((i 0) (acc '())) (if (= i 4) acc (loop (+ i 1) (cons i acc))))", "(let loop ((i 0) (acc '())) (if (= i 4) acc (loop (+ i 1) (cons i acc))))"),
        ("(r-let* ((x 2) (y (* x 3))) (list x y))", "(let* ((x 2) (y (* x 3))) (list x y))"),
        ("(r-do ((vec (make-vector 5)) (i 0 (+ i 1))) ((= i 5) vec) (vector-set! vec i i))", "(do ((vec (make-vector 5)) (i 0 (+ i 1))) ((= i 5) vec) (vector-set! vec i i))"),
        ("(let ((x '(1 3 5 7 9))) (r-do ((x x (cdr x)) (sum 0 (+ sum (car x)))) ((null? x) sum)))", "(let ((x '(1 3 5 7 9))) (do ((x x (cdr x)) (sum 0 (+ sum (car x)))) ((null? x) sum)))"),
    ];
    for (as_macro, built_in) in cases {
        let got = both(&format!("{R7RS_DERIVED} {as_macro}"));
        let want = both(built_in);
        assert_eq!(got, want, "{as_macro}");
        assert!(!got.starts_with("!!"), "{as_macro}: {got}");
    }
    // And hygienic as macros, too: `r-or`'s `x` is not the user's.
    assert_eq!(both(&format!("{R7RS_DERIVED} (let ((x 5)) (r-or #f x))")), "5");
    // `r-do`'s `loop` is not the user's either.
    assert_eq!(
        both(&format!("{R7RS_DERIVED} (let ((loop 'mine)) (r-do ((i 0 (+ i 1))) ((= i 2) loop)))")),
        "mine"
    );
}

// ------------------------------------------- procedural macros (SRFI 211)

const ER_SWAP: &str = include_str!("programs/macros/er-swap.scm");

#[test]
fn explicit_renaming_is_hygienic_where_it_renames() {
    assert_eq!(
        both(&format!("{ER_SWAP} (define tmp 1) (define other 2) (swap! tmp other) (list tmp other)")),
        "(2 1)"
    );
    // What it renames means what it meant at the definition, whatever the use
    // site has rebound.
    assert_eq!(
        both(&format!("{ER_SWAP} (define x 1) (define y 2) (let ((let 0) (set! 0)) (swap! x y)) (list x y)")),
        "(2 1)"
    );
}

#[test]
fn explicit_renaming_captures_what_it_leaves_bare() {
    assert_eq!(
        both(include_str!("programs/macros/er-aif.scm")),
        "2"
    );
}

#[test]
fn implicit_renaming_renames_everything_but_what_it_injects() {
    let def = include_str!("programs/macros/ir-aif.scm");
    assert_eq!(both(&format!("{def} (aif (assq 'b '((a 1) (b 2))) (cadr it) 'no)")), "2");
    assert_eq!(both(&format!("{def} (let ((if list) (let 'x)) (aif #f 1 2))")), "2");
    // Nothing the template inserts can capture: `tmp` here is the template's.
    assert_eq!(
        both(include_str!("programs/macros/ir-swap.scm")),
        "(2 1)"
    );
}

/// IR's input identifiers are marked, so `eq?` against a bare symbol fails —
/// `compare` or `strip-syntax` is how to look at them.
#[test]
fn implicit_renaming_input_is_marked_and_strip_syntax_unmarks_it() {
    assert_eq!(
        both(include_str!("programs/macros/ir-look.scm")),
        "(#f #t x)"
    );
}

#[test]
fn compare_matches_by_binding() {
    let def = "(define-syntax which
                 (er-macro-transformer
                  (lambda (form rename compare)
                    (if (compare (cadr form) (rename 'else)) ''else-literal ''something-else))))";
    assert_eq!(
        both(&format!("{def} (list (which else) (which other) (let ((else 1)) (which else)))")),
        "(else-literal something-else something-else)"
    );
}

#[test]
fn a_transformer_can_compute() {
    assert_eq!(
        both(include_str!("programs/macros/er-unroll.scm")),
        "4"
    );
}

#[test]
fn begin_for_syntax_defines_helpers_for_transformers() {
    assert_eq!(
        both(
            "(begin-for-syntax (define (twice x) (list x x)))
             (define-syntax dup (er-macro-transformer (lambda (f r c) `(,(r 'quote) ,(twice (cadr f))))))
             (dup hello)"
        ),
        "(hello hello)"
    );
}

/// A procedural macro whose input another macro produced: the input's
/// identifiers keep their identity through the trip into Scheme and back. The
/// `syntax-rules` template's `tmp` is not the global `tmp`, and the ER
/// macro's own renamed `tmp` is neither.
#[test]
fn hygiene_survives_layering_macro_systems() {
    assert_eq!(
        both(&format!(
            "{ER_SWAP}
             (define-syntax use-tmp (syntax-rules () ((_ x) (let ((tmp 'inner)) (swap! tmp x)))))
             (define tmp 'global) (define outer 'outer)
             (use-tmp outer)
             (list outer tmp)"
        )),
        "(inner global)"
    );
}

#[test]
fn procedural_macros_in_scoped_forms() {
    assert_eq!(
        both(
            "(let-syntax ((ten (er-macro-transformer (lambda (f r c) 10))))
               (+ (ten) 1))"
        ),
        "11"
    );
}

#[test]
fn procedural_macro_errors_say_what_went_wrong() {
    // A transformer runs before the input around it: a local is not there.
    let out = both("(let ((k 3)) (let-syntax ((m (er-macro-transformer (lambda (f r c) k)))) (m)))");
    assert!(out.contains("unbound variable: k"), "{out}");
    let out = both("(define-syntax m (er-macro-transformer (lambda (f r c) (error \"bad use\" f)))) (m 1)");
    assert!(out.contains("bad use"), "{out}");
    let out = both("(define-syntax m (er-macro-transformer (lambda (f r c) car))) (m)");
    assert!(out.contains("`m` produced #<primitive:car>, which is not syntax"), "{out}");
    let out = both("(define-syntax m 42)");
    assert!(out.contains("must be `syntax-rules`, `er-macro-transformer` or `ir-macro-transformer`"), "{out}");
}

#[test]
fn procedural_macros_persist_across_inputs() {
    let big = move || {
        for backend in [Backend::Ast, Backend::Bytecode] {
            let mut s = Session::with_backend(backend);
            s.eval_to_string("<1>", ER_SWAP).expect("defines");
            s.eval_to_string("<2>", "(define a 1) (define b 2)").expect("defines");
            // Collections between inputs must not lose the transformer.
            s.eval_to_string("<3>", "(let loop ((i 0)) (if (< i 20000) (begin (cons i i) (loop (+ i 1)))))")
                .expect("runs");
            assert_eq!(s.eval_to_string("<4>", "(begin (swap! a b) (list a b))").ok().as_deref(), Some("(2 1)"));
        }
    };
    std::thread::Builder::new().stack_size(STACK).spawn(big).expect("spawns").join().expect("passes");
}

// ------------------------------------------------ syntax parameters (SRFI 139)

/// SRFI 139's own example.
#[test]
fn srfi_139_abort_from_forever() {
    assert_eq!(
        both(include_str!("programs/macros/srfi-139-forever.scm")),
        "5"
    );
    let out = both(
        "(define-syntax-parameter abort
           (syntax-rules () ((_ . _) (syntax-error \"abort used outside of a loop\"))))
         (abort 1)",
    );
    assert!(out.contains("abort used outside of a loop"), "{out}");
}

const PARAM_AIF: &str = include_str!("programs/macros/param-aif.scm");

/// The anaphoric `if` with nothing captured: `it` is defined once, and `aif`
/// rebinds what it means for the extent of its body.
#[test]
fn a_syntax_parameter_gives_aif_without_capture() {
    assert_eq!(both(&format!("{PARAM_AIF} (aif (assq 'b '((a 1) (b 2))) (cadr it) 'no)")), "2");
    assert_eq!(both(&format!("{PARAM_AIF} (aif 1 (aif 2 (list it) 'no) 'no)")), "(2)");
    // A binding the user writes is lexical, and wins.
    assert_eq!(both(&format!("{PARAM_AIF} (aif 1 (let ((it 'mine)) it) 'no)")), "mine");
    // `(it x)` applies what `it` stands for.
    assert_eq!(both(&format!("{PARAM_AIF} (aif car (it '(9 8)) 'no)")), "9");
    let out = both(&format!("{PARAM_AIF} it"));
    assert!(out.contains("only meaningful inside aif"), "{out}");
}

/// SRFI 139 parameters are dynamic over expansion: a macro whose template
/// mentions the parameter sees the rebinding when used inside the body. That
/// is exactly what name capture could not do safely.
#[test]
fn a_syntax_parameter_reaches_macros_used_in_the_body() {
    assert_eq!(
        both(&format!("{PARAM_AIF} (define-syntax show-it (syntax-rules () ((_) it))) (aif 42 (show-it) 'no)")),
        "42"
    );
}

#[test]
fn identifier_syntax_on_its_own() {
    assert_eq!(
        both("(define hidden 7) (define-syntax seven (identifier-syntax hidden)) (list seven (+ seven 1))"),
        "(7 8)"
    );
}

#[test]
fn syntax_parameter_errors() {
    let out = both("(syntax-parameterize ((car (syntax-rules () ((_) 1)))) (car))");
    assert!(out.contains("`car` is not a syntax parameter"), "{out}");
    let out = both("(define-syntax m (syntax-rules () ((_) 1))) (set! m 5)");
    assert!(out.contains("cannot `set!` a syntactic keyword"), "{out}");
    let out = both("(syntax-error \"custom failure\" (a b))");
    assert!(out.contains("custom failure: (a b)"), "{out}");
}
