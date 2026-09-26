//! Recursion without a knot anyone can see (docs/research/recursion-and-
//! initialization.md): a `letrec` binds only lambdas, so nothing runs
//! before every binding exists. The programs here are also checked by the
//! checker written in FX-26 (`tests/checker.rs`, which reads every test's
//! string literals), which must say the same.

use fixpt_fx26::Checker;
use fixpt_read::FileId;

fn check(program: &str) -> Result<(), String> {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), program).map_err(|e| e.message)?;
    let done = c.declare_ahead(&forms).map_err(|e| e.message)?;
    for (f, done) in forms.iter().zip(done) {
        if !done {
            c.top(f).map_err(|e| e.message)?;
        }
    }
    Ok(())
}

#[test]
fn a_letrec_binds_lambdas() {
    assert_eq!(check("(letrec ((f (subr pure (int) int) (lambda (n) (if (= n 0) 0 (f (- n 1)))))) (f 3))"), Ok(()));
    // Under an ascription or a type abstraction, still a lambda.
    assert_eq!(check("(letrec ((f (subr pure (int) int) (the (subr pure (int) int) (lambda (n) n)))) (f 3))"), Ok(()));
}

#[test]
fn a_letrec_binding_that_is_not_a_lambda_is_rejected() {
    let why = "`x` is bound recursively, so it must be a lambda: nothing may run before every binding exists";
    // Its value would be computed by calling into the group before the
    // group exists.
    assert_eq!(
        check("(letrec ((f (subr pure () int) (lambda () x)) (x int (f))) x)"),
        Err(why.to_string())
    );
    assert_eq!(check("(letrec ((x int 1)) x)"), Err(why.to_string()));
}

#[test]
fn a_group_defines_procedures_that_call_each_other() {
    assert_eq!(
        check(
            "(define-rec
               (ev (subr pure (int) bool) (lambda (n) (if (= n 0) #t (od (- n 1)))))
               (od (subr pure (int) bool) (lambda (n) (if (= n 0) #f (ev (- n 1))))))
             (ev 10)"
        ),
        Ok(())
    );
}

#[test]
fn a_group_binds_only_lambdas() {
    assert_eq!(
        check("(define-rec (f (subr pure () int) (lambda () x)) (x int (f))) x"),
        Err("`x` is bound recursively, so it must be a lambda: nothing may run before every binding exists".to_string())
    );
}

#[test]
fn a_group_is_checked_against_its_types() {
    let e = check("(define-rec (f (subr pure (int) int) (lambda (n) (g n))) (g (subr pure (int) bool) (lambda (n) #t))) 1");
    assert!(e.is_err(), "{e:?}");
}
