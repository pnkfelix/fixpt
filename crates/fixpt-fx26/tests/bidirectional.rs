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
    // Its read kept, the region being the result's (Heist's report,
    // 2026-10-29: masking keeps `read` and `write` there).
    assert_eq!(check("(cdr (cons 1 nil))"), "(listof int @r.1) ! (maxeff (read @r.1) (alloc @r.1))");
    let written = "(let ((p (cons 1 nil))) (begin (set-cdr! p (cons 2 nil)) p))";
    assert_eq!(check(written), "(pairof int (listof int @r.1) @r.1) ! (maxeff (write @r.1) (alloc @r.1))");
    // Where a pair's tail is expected to be `nil`, it stays `nil`.
    assert_eq!(check("(define p (pairof int nil @heap) (cons 1 nil)) (cdr p)"), "nil ! (maxeff (read @heap) (read (globals p)))");
    let xs = "(define xs (listof int @heap) (list 1 2)) (define c bool #t)";
    assert_eq!(check(&format!("{xs} (if c nil xs)")), "(listof int @heap) ! (read (globals c xs))");
    assert_eq!(check(&format!("{xs} (if c xs nil)")), "(listof int @heap) ! (read (globals c xs))");
    assert_eq!(check(&format!("{xs} (if c nil nil)")), "nil ! (read (globals c))");
    assert_eq!(check(&format!("{xs} (cond ((= 1 2) nil) (else xs))")), "(listof int @heap) ! (read (globals xs))");
    // Beside a pair, `nil` makes the pair one that may be `nil`: a pair
    // whose tail is a list of the same, which is that list, and shows so
    // (Heist's report, 2026-10-28).
    assert_eq!(check(&format!("{xs} (if c (cons 1 nil) nil)")), "(listof int @r.1) ! (maxeff (alloc @r.1) (read (globals c)))");
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

/// An `i32` or `u32` goes where an `int` is wanted, and a literal in its
/// range is one (`programs/sizes/fixed-width-literals.fx`); one past it is
/// refused.
#[test]
fn fixed_widths_are_ints_and_have_literals() {
    let p = include_str!("programs/sizes/fixed-width-literals.fx");
    assert_eq!(check(p), "int ! (read (globals bump x y))");
    let err = rejects(include_str!("programs/sizes/fixed-width-literal-too-big.fx"));
    assert!(err.contains("4294967296 is not a u32: its range is 0 to 4294967295"), "{err}");
}

/// `length` of a list at `acyclic`, a `nlist` of some length; of one at
/// a region, which may be written, refused, `list-length` named (kayak's
/// report, 2026-10-11).
#[test]
fn length_of_an_acyclic_list() {
    assert_eq!(check(include_str!("programs/sizes/length-of-a-list.fx")), "nat ! (read (globals l))");
    let err = rejects("(length (list 1 2))");
    let hint = "where a (nlist ? n) is expected; a `listof` is no `nlist`, whose length is in its type: `list-length` measures a list";
    assert!(err.contains(hint), "{err}");
    assert_eq!(check("(list-length (list 1 2))"), "nat ! pure");
}

/// An `i64` or `u64` literal likewise, past a fixnum too
/// (`programs/sizes/fixed-width-64-literals.fx`); one out of its type's
/// range refused, the range said (kayak's request, 2026-10-11).
#[test]
fn literals_check_against_any_fixed_width() {
    assert_eq!(check("(i64+ 1 2)"), "i64 ! pure");
    assert_eq!(check("(define x i64 5) x"), "i64 ! (read (globals x))");
    let p = include_str!("programs/sizes/fixed-width-64-literals.fx");
    assert_eq!(check(p), "(listof int @r.1) ! (maxeff (alloc @r.1) (read (globals add big neg x)))");
    for (p, want) in [
        ("(define y u32 -1)", "-1 is not a u32: its range is 0 to 4294967295"),
        ("(define y i32 2147483648)", "2147483648 is not a i32: its range is -2147483648 to 2147483647"),
        ("(define y u64 18446744073709551616)", "18446744073709551616 is not a u64: its range is 0 to 18446744073709551615"),
        ("(define y i64 -9223372036854775809)", "-9223372036854775809 is not a i64: its range is -9223372036854775808 to 9223372036854775807"),
        ("(i64+ 9223372036854775808 1)", "9223372036854775808 is not a i64"),
    ] {
        let err = rejects(p);
        assert!(err.contains(want), "{p}: {err}");
    }
    // A sum written out is no literal, past a fixnum or not.
    assert!(rejects("(define y i64 (+ 1 2))").contains("a i64 is expected here, and this is a (nat 3)"));
}

// ----------------------------------------------------------------- arrows

/// `(-> (param …) result)` is `(subr pure (param …) result)`, wherever a
/// type is written, and so is as strict: one that may not end, or that
/// calls a global (which reads it), is refused.
#[test]
fn an_arrow_is_a_pure_subroutine() {
    assert_eq!(
        check(include_str!("programs/bidirectional/arrow.fx")),
        "int ! (read (globals adder inc pick same twice))"
    );
    assert_eq!(check("(the (-> ((-> (int) int)) (-> () int)) (lambda (f) (lambda () (f 1))))"), "(subr pure ((subr pure (int) int)) (subr pure () int)) ! pure");
    let err = rejects(include_str!("programs/terminate/arrow-spins.fx"));
    assert!(err.contains("it may not end"), "{err}");
    let err = rejects(include_str!("programs/terminate/arrow-reads-globals.fx"));
    assert!(err.contains("it has (read (globals inc))"), "{err}");
    assert!(rejects("(the (-> (int)) 0)").contains("`(-> (param …) result)`"));
}

/// `(->* (param …) result)` finds its effect from its `lambda`, once: a
/// call of itself stands for nothing more while the body is checked, since
/// the effect found already holds what such a call does; then it is checked
/// again at the type found, which refuses what that type does not allow.
#[test]
fn an_arrow_star_finds_its_effect() {
    let mut c = Checker::new();
    let program = include_str!("programs/bidirectional/arrow-star.fx");
    c.check_program(program).unwrap_or_else(|e| panic!("does not check: {e}"));
    let shown = |c: &mut Checker, n: &str| {
        let t = c.check_program(n).expect("a name");
        c.show_ty(t.ty)
    };
    assert_eq!(shown(&mut c, "inc2"), "(subr (read (globals inc)) (int) int)");
    assert_eq!(shown(&mut c, "count"), "(subr (maxeff spin (read (globals count))) (int) int)");
    assert_eq!(shown(&mut c, "mk"), "(subr (alloc @h) (int) (listof int @h))");
    assert_eq!(shown(&mut c, "ap"), "(poly ((t type)) (subr pure ((subr pure (t) t) t) t))");
    let err = rejects(include_str!("programs/arrows/star-passed-as-pure.fx"));
    assert!(err.starts_with("`->*` found `f` to be a (subr (maxeff spin (read (globals f twice))) (int) int)"), "{err}");
    for (program, says) in [
        (include_str!("programs/arrows/star-as-parameter.fx"), "is only the type a definition declares"),
        (include_str!("programs/arrows/star-not-lambda.fx"), "from its `lambda`: define it as one"),
        (include_str!("programs/arrows/star-group-not-lambda.fx"), "from its `lambda`: define it as one"),
        (include_str!("programs/arrows/star-and-define-star.fx"), "each find what a procedure does"),
    ] {
        let err = rejects(program);
        assert!(err.contains(says), "{err}");
    }
}

/// `->*` in a group: each member's effect found once, then with those of
/// the members it reaches through the group (a member it does not reach
/// adds nothing), `spin` if it may not end, or at top level reads a
/// member's global; then the group checked again at the types found.
#[test]
fn an_arrow_star_group_finds_each_effect() {
    let mut c = Checker::new();
    c.check_program(include_str!("programs/bidirectional/arrow-star-groups.fx")).unwrap_or_else(|e| panic!("does not check: {e}"));
    let mut shown = |n: &str| {
        let t = c.check_program(n).expect("a name");
        c.show_ty(t.ty)
    };
    assert_eq!(shown("ev?"), "(subr (maxeff spin (read (globals ev? od?))) (nat) bool)");
    assert_eq!(shown("get-noisy"), "(subr (maxeff spin (read (globals noisy))) () (subr (read (globals inc)) (int) int))");
    assert_eq!(shown("total"), "(subr pure (nat) int)");
    assert_eq!(shown("parts"), "(subr (read (globals inc twice)) (nat) int)");
    assert_eq!(shown("loops"), "(subr spin (int) int)");
    let err = rejects(include_str!("programs/arrows/star-group-passed-as-pure.fx"));
    assert!(err.contains("argument 1 is a (subr (maxeff spin (read (globals twice))) (int) int)"), "{err}");
}

/// `->*` in a module: every such lambda's effect found before any of the
/// module's lambdas is checked; a value made by calling one is refused, as
/// the lambda is still at its placeholder then.
#[test]
fn an_arrow_star_in_a_module_finds_its_effect() {
    assert_eq!(
        check(include_str!("programs/bidirectional/arrow-star-module.fx")),
        "int ! (maxeff (read @h) (write @h) (read (globals counter)))"
    );
    let err = rejects(include_str!("programs/arrows/star-module-value.fx"));
    assert!(err.contains("`y` names `f` as it is made"), "{err}");
    let err = rejects(include_str!("programs/arrows/star-module-not-lambda.fx"));
    assert!(err.contains("from its `lambda`: define it as one"), "{err}");
    let err = rejects(include_str!("programs/arrows/star-module-define-star.fx"));
    assert!(err.contains("each find what a procedure does"), "{err}");
}
