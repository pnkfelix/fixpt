//! Bidirectional checking (`docs/fx26.md`, plan step 4): signatures on
//! definitions, parameter types from what a `lambda` is checked against, and
//! projections inferred at applications. Every program here also checks with
//! everything written out; the point is that it need not be.

use fixpt_fx26::Checker;

fn check(program: &str) -> String {
    let mut c = Checker::new();
    let k = c.check_program(program).unwrap_or_else(|e| panic!("does not check: {e}\n{program}"));
    format!("{} ! {}", c.show_ty(k.ty), c.show_effect(&k.effect))
}

fn rejects(program: &str) -> String {
    let mut c = Checker::new();
    match c.check_program(program) {
        Ok(k) => panic!("checks as {}, and should not:\n{program}", c.show_ty(k.ty)),
        Err(e) => e.message,
    }
}

// ------------------------------------------------------------- signatures

#[test]
fn a_signature_types_the_lambdas_parameters() {
    let p = "(define inc (subr pure (int) int) (lambda (x) (+ x 1))) (inc 2)";
    assert_eq!(check(p), "int ! (read (globals inc))");
}

#[test]
fn a_lambda_with_nothing_to_go_on_needs_its_types() {
    let err = rejects("(lambda (x) x)");
    assert!(err.contains("the type of parameter `x` cannot be known here"), "{err}");
}

/// The expected type reaches through `if`, `let` and `begin` to the
/// expressions that need it.
#[test]
fn what_is_expected_flows_into_branches_and_bodies() {
    let p = "(define f (subr pure (bool) (subr pure (int) int))
               (lambda (b) (let ((one 1)) (if b (lambda (x) (+ x one)) (begin 0 (lambda (y) y))))))
             ((f #t) 2)";
    assert_eq!(check(p), "int ! (read (globals f))");
}

/// A polymorphic signature, and no `plambda`: the definition is checked
/// with the binders held abstract, and then used at two types without a
/// `proj`.
#[test]
fn a_polymorphic_signature_needs_no_plambda() {
    let def = "(define id (poly ((t type)) (subr pure (t) t)) (lambda (x) x))";
    assert_eq!(check(&format!("{def} (id 3)")), "int ! (read (globals id))");
    assert_eq!(check(&format!("{def} (id #t)")), "bool ! (read (globals id))");
    assert_eq!(check(include_str!("programs/bidirectional/twice.fx")), "int ! (read (globals twice))");
}

/// A definition that does not meet its signature says which signature.
#[test]
fn a_definition_is_checked_against_its_signature() {
    let err = rejects("(define f (subr pure (int) int) (lambda (x) #t))");
    assert!(err.contains("a int is expected here, and this is a bool"), "{err}");
    let err = rejects("(define n int #t)");
    assert!(err.contains("`n` is declared a int"), "{err}");
}

/// A polymorphic value is pure, as a `plambda` body must be.
#[test]
fn a_polymorphic_definition_must_be_pure() {
    let cell = "(define r (poly ((q region)) (ref int q)) (new 0))";
    let err = rejects(&format!("{cell} 1"));
    assert!(err.contains("must be pure"), "{err}");
}

// ----------------------------------------------------- inferred projections

/// Types from the arguments; the region, which no argument names, fresh —
/// so the pair is private and its allocation and read are masked.
#[test]
fn a_projection_is_inferred_from_the_arguments() {
    assert_eq!(check("(car (cons 1 #t))"), "int ! pure");
    let pair = check("(cons 1 #t)");
    assert!(pair.starts_with("(pairof int bool @r."), "{pair}");
    assert!(pair.contains("! (alloc @r."), "{pair}");
}

/// A binder the arguments do not fix comes from the expected type.
#[test]
fn a_projection_is_inferred_from_what_is_expected() {
    let p = "(define empty (listof int @l) nil) ((proj (proj car @l) int (listof int @l)) empty)";
    assert_eq!(check(p), "int ! (maxeff (read @l) (read (globals empty)))");
    assert_eq!(check("(null? (the (listof int @l) nil))"), "bool ! pure");
}

#[test]
fn a_type_nothing_determines_is_an_error() {
    let err = rejects("(car nil)");
    assert!(err.contains("not yet known here") || err.contains("cannot be inferred"), "{err}");
}

/// `nil`, where nothing else says which list, is of the type `nil`
/// (`TODO.md` §48), and an `if` or `tagcase` with `nil` in one branch is what
/// the others are.
#[test]
fn nil_is_of_the_type_nil_where_nothing_says_which_list() {
    assert_eq!(check("(null? nil)"), "bool ! pure");
    assert_eq!(check("(let ((xs nil)) (null? xs))"), "bool ! pure");
    // A new pair's tail, `nil`, is widened to a list: `(cons 1 nil)` is a
    // list, which may be written as one.
    assert_eq!(check("(cons 1 nil)"), "(pairof int (listof int @r.1) @r.1) ! (alloc @r.1)");
    assert_eq!(check("(cdr (cons 1 nil))"), "(listof int @r.1) ! (alloc @r.1)");
    let written = "(let ((p (cons 1 nil))) (begin (set-cdr! p (cons 2 nil)) p))";
    assert_eq!(check(written), "(pairof int (listof int @r.1) @r.1) ! (alloc @r.1)");
    // Where a pair's tail is expected to be `nil`, it stays `nil`.
    assert_eq!(check("(define p (pairof int nil @heap) (cons 1 nil)) (cdr p)"), "nil ! (maxeff (read @heap) (read (globals p)))");
    let xs = "(define xs (listof int @heap) (list 1 2)) (define c bool #t)";
    assert_eq!(check(&format!("{xs} (if c nil xs)")), "(listof int @heap) ! (read (globals c xs))");
    assert_eq!(check(&format!("{xs} (if c xs nil)")), "(listof int @heap) ! (read (globals c xs))");
    assert_eq!(check(&format!("{xs} (if c nil nil)")), "nil ! (read (globals c))");
    assert_eq!(check(&format!("{xs} (cond ((= 1 2) nil) (else xs))")), "(listof int @heap) ! (read (globals xs))");
    // Beside a pair, `nil` makes the pair one that may be `nil`.
    assert_eq!(
        check(&format!("{xs} (if c (cons 1 nil) nil)")),
        "(union nil (pairof int (listof int @r.1) @r.1)) ! (maxeff (alloc @r.1) (read (globals c)))"
    );
}

/// A message names `datum`, not its union written out (substitution keeps
/// the standard `datum` itself).
#[test]
fn a_message_names_datum() {
    let err = rejects("(define d datum 1) (define x int (car d))");
    assert!(err.ends_with("a int is expected here, and this is a datum"), "{err}");
}

/// A datatype keeps its name through an instantiation (`cons`'s): data
/// that mentions no variable is left itself by substitution
/// (`closed_named`), declared ahead or not.
#[test]
fn a_message_names_a_datatype_through_instantiation() {
    let p = "(define-datatype tree (leaf int) (node tree tree))
             (define* f (subr pure (int) int) (lambda (x) x))
             (define l (listof tree @heap) (list (leaf 1)))
             (f (cons (leaf 2) l))";
    let err = rejects(p);
    assert!(err.contains("this is a (pairof tree (listof tree @heap) r)"), "{err}");
}

/// The effect binder of a higher-order operator is the latent effect of the
/// subroutine passed to it.
#[test]
fn an_effect_binder_takes_the_latent_effect_of_the_argument() {
    let def = "(define apply1 (poly ((e effect)) (subr e ((subr e (int) int) int) int))
                 (lambda (f x) (f x)))";
    assert_eq!(check(&format!("{def} (apply1 (lambda ((n int)) n) 3)")), "int ! (read (globals apply1))");
    let reading = format!("{def} (define c (ref int @c) (new 0)) (apply1 (lambda ((n int)) (get c)) 3)");
    assert_eq!(check(&reading), "int ! (maxeff (read @c) (read (globals apply1 c)))");
}

/// An argument of the wrong type is reported as that argument, in the
/// program's terms.
#[test]
fn a_wrong_argument_is_named() {
    let err = rejects("(car 5)");
    assert!(err.contains("argument 1 is a int"), "{err}");
}

// ------------------------------------------------------------ control

/// The control cases of step 3, with every projection left out.
#[test]
fn delimited_control_needs_no_projections() {
    assert_eq!(check(include_str!("programs/bidirectional/own-abort.fx")), "int ! (read (globals t))");
    assert_eq!(check(include_str!("programs/bidirectional/capture-and-resume.fx")), "int ! (read (globals t))");
}

/// PLDI '89's C3: `cwcc` instantiated with a region of its own, so its
/// control effects are masked, as the paper's own explicit version's are.
#[test]
fn cwcc_with_a_fresh_region_is_masked() {
    assert_eq!(check(include_str!("programs/bidirectional/cwcc.fx")), "int ! pure");
}
