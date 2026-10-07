//! FX-91's immutable data in FX-26 (`PLAN.md` §11, step 7): products, sums,
//! `tagcase`, and `define-datatype`, which are frozen bloblets at run time.

use fixpt_engine::Backend;
use fixpt_fx26::Checker;
use fixpt_fx26::session::Fx26Session;

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

#[test]
fn products_are_immutable_so_pure() {
    assert_eq!(check("(product (x 1) (y #t))"), "(productof (x int) (y bool)) ! pure");
    assert_eq!(check("(extract (product (x 1) (y #t)) y)"), "bool ! pure");
    let err = rejects("(extract (product (x 1)) z)");
    assert!(err.contains("has no `z`"), "{err}");
    assert_eq!(run("(extract (product (x 1) (y \"two\")) y)"), "\"two\"");
}

#[test]
fn a_sum_with_fewer_tags_fits_one_with_more() {
    assert_eq!(check("(sum a 1)"), "(sumof (a int)) ! pure");
    assert_eq!(check("(the (sumof (a int) (b bool)) (sum b #f))"), "(sumof (a int) (b bool)) ! pure");
    let err = rejects("(the (sumof (a int)) (sum b #f))");
    assert!(err.contains("is expected here"), "{err}");
}

#[test]
fn tagcase_covers_every_tag_or_has_an_else() {
    let t = "(define-type ab (sumof (a int) (b bool)))";
    assert_eq!(check(&format!("{t} (tagcase (the ab (sum a 1)) (a n n) (b x 0))")), "int ! pure");
    let err = rejects(&format!("{t} (tagcase (the ab (sum a 1)) (a n n))"));
    assert!(err.contains("no arm for b"), "{err}");
    let err = rejects(&format!("{t} (tagcase (the ab (sum a 1)) (c n n) (else r 0))"));
    assert!(err.contains("has no tag `c`"), "{err}");
    let err = rejects(&format!("{t} (tagcase (the ab (sum a 1)) (a (x y) x) (b x 0))"));
    assert!(err.contains("cannot be taken apart"), "{err}");
    assert_eq!(run(include_str!("programs/bloblet/else-narrows.fx")), "42");
}

#[test]
fn define_datatype_makes_constructors_for_tagcase() {
    assert_eq!(run(include_str!("programs/bloblet/expr.fx")), "42");
    // A value is a frozen bloblet of kind `sum`: the tag, then the product.
    assert_eq!(run("(define-datatype t (leaf int)) (leaf 1)"), "#<sum leaf>");
    assert_eq!(run("(product (a 1) (b 2))"), "#<product of 2>");
}

#[test]
fn a_type_abbreviation_may_take_parameters() {
    let d = "(define-type (pair-of (a type) (r region)) (pairof a a r))";
    assert_eq!(check(&format!("{d} (the (pair-of int @p) (cons 1 2))")), "(pairof int int @p) ! (alloc @p)");
    let err = rejects(&format!("{d} (the (pair-of int) (cons 1 2))"));
    assert!(err.contains("takes 2 description(s), and has 1"), "{err}");
    // Mentioning itself with the same descriptions: a knot.
    assert_eq!(
        check("(define-type (loop (a type)) (union nil (pairof (loop a) a @r))) (the (loop int) no-pair)"),
        "(mu %1 (union nil (pairof %1 int @r))) ! pure"
    );
    // With others, an expansion that would never end.
    let err = rejects("(define-type (grow (a type)) (pairof (grow (listof a @r)) a @r)) (the (grow int) nil)");
    assert!(err.contains("may mention itself only with the same descriptions"), "{err}");
}
