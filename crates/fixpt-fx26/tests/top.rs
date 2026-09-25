//! The top level: definitions that stay in scope, and checking that does not.

use fixpt_fx26::{Checker, Top};
use fixpt_read::FileId;

fn top(c: &mut Checker, text: &str) -> Result<Top, String> {
    let forms = c.read_in(FileId(0), text).map_err(|e| e.message)?;
    c.top(&forms[0]).map_err(|e| e.message)
}

fn ty_of(c: &mut Checker, text: &str) -> String {
    match top(c, text) {
        Ok(Top::Exp(k)) => format!("{} ! {}", c.show_ty(k.ty), c.show_effect(&k.effect)),
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_definition_stays_in_scope() {
    let mut c = Checker::new();
    top(&mut c, "(define double (subr pure (int) int) (lambda ((x int)) (+ x x)))").expect("defines");
    assert_eq!(ty_of(&mut c, "(double 4)"), "int ! pure");
}

#[test]
fn a_typed_definition_may_be_recursive() {
    let mut c = Checker::new();
    let src = "(define count (subr pure (int) int)
                 (lambda ((n int)) (if (= n 0) 0 (count (- n 1)))))";
    top(&mut c, src).expect("defines");
    assert_eq!(ty_of(&mut c, "(count 3)"), "int ! pure");
}

#[test]
fn an_untyped_definition_takes_its_expressions_type() {
    let mut c = Checker::new();
    top(&mut c, "(define three 3)").expect("defines");
    assert_eq!(ty_of(&mut c, "(+ three 1)"), "int ! pure");
}

#[test]
fn a_definition_that_does_not_match_its_type_is_rejected_and_not_kept() {
    let mut c = Checker::new();
    let err = top(&mut c, "(define x int #t)").expect_err("mismatch");
    assert!(err.contains("declared a int"), "{err}");
    assert!(top(&mut c, "x").is_err(), "a rejected definition stayed in scope");
}

#[test]
fn a_type_abbreviation_may_mention_itself() {
    let mut c = Checker::new();
    top(&mut c, "(define-type K (subr (goto @k) (K) void))").expect("defines");
    let written_out = c.type_of_str("(dletrec ((k (subr (goto @k) (k) void))) k)").expect("a type");
    let named = c.type_of_str("K").expect("a type");
    assert!(c.subtype(named, written_out) && c.subtype(written_out, named));
}

#[test]
fn a_type_abbreviation_that_is_only_a_name_is_rejected() {
    let mut c = Checker::new();
    let err = top(&mut c, "(define-type L L)").expect_err("ungrounded");
    assert!(err.contains("constructor"), "{err}");
    assert!(c.type_of_str("L").is_err(), "a rejected abbreviation stayed in scope");
}

#[test]
fn trying_a_form_leaves_nothing_behind() {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), "(define y 5) (define-type T (ref int @r))").expect("reads");
    for f in &forms {
        let ok = c.try_top(f, |_, r| r.is_ok());
        assert!(ok);
    }
    assert!(top(&mut c, "y").is_err(), "a tried definition stayed");
    assert!(c.type_of_str("T").is_err(), "a tried abbreviation stayed");
}

#[test]
fn the_argument_a_subroutine_wants() {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), "(+ 1 2) (cons 1 2)").expect("reads");
    let items = |f: &fixpt_read::Syntax| f.as_proper_list().expect("a list").to_vec();
    assert_eq!(c.describe_argument(&items(&forms[0]), 2).as_deref(), Some("int"));
    // Only what the other arguments determine is filled in.
    assert_eq!(c.describe_argument(&items(&forms[1]), 2).as_deref(), Some("t2"));
}
