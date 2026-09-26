//! `letrena` and `letreap` (PLAN.md, "Regions that end"): a region that
//! lives while its body runs, as an arena or as a heap of its own. The two
//! share their typing rule, which both checkers apply (`tests/checker.rs`
//! reads these programs and compares them); for now a region's allocation
//! is the heap's, so every back end just runs the body.

use fixpt_fx26::Checker;
use fixpt_read::FileId;

fn check(program: &str) -> Result<Vec<String>, String> {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), program).map_err(|e| e.message)?;
    let done = c.declare_ahead(&forms).map_err(|e| e.message)?;
    let mut out = Vec::new();
    for (f, done) in forms.iter().zip(done) {
        if !done {
            if let fixpt_fx26::Top::Exp(k) = c.top(f).map_err(|e| e.message)? {
                out.push(format!("{} ! {}", c.show_ty(k.ty), c.show_effect(&k.effect)));
            }
        }
    }
    Ok(out)
}

/// A body that allocates in its region, and gives back only what does not
/// mention it: pure, since nothing outside can see the region.
#[test]
fn what_happens_in_a_region_is_masked() {
    assert_eq!(
        check("(letrena r (let ((xs (the (listof int r) (cons 1 (cons 2 nil))))) (+ (car xs) (car (cdr xs)))))"),
        Ok(vec!["int ! pure".to_string()])
    );
    assert_eq!(
        check("(define add-to (subr pure (int) int) (lambda (n) (letreap r (let ((b (the (ref int r) (new 0)))) (begin (set b (+ (get b) n)) (get b)))))) (add-to 41)"),
        Ok(vec!["int ! pure".to_string()])
    );
}

/// What would carry the region out is rejected.
#[test]
fn a_region_cannot_escape_in_the_value() {
    assert_eq!(
        check("(letrena r (the (listof int r) (cons 1 nil)))"),
        Err("the value of `letrena r` would outlive its region: its type is (listof int r)".to_string())
    );
    let e = check("(letreap r (let ((b (the (ref int r) (new 0)))) (lambda () (get b))))");
    assert!(e.as_ref().is_err_and(|m| m.contains("would outlive its region")), "{e:?}");
}

/// A continuation captured inside, up to a prompt outside, could be resumed
/// after the region is gone: rejected.
#[test]
fn no_continuation_may_outlive_a_region() {
    let e = check(include_str!("programs/regions/continuation-escapes.fx"));
    assert!(e.as_ref().is_err_and(|m| m.contains("a continuation captured in `letreap r`")), "{e:?}");
}

#[test]
fn a_region_is_named_without_at() {
    assert_eq!(check("(letrena @r 1)"), Err("a `letrena` binds a region variable's name, without `@`".to_string()));
    assert_eq!(check("(letreap @r 1)"), Err("a `letreap` binds a region variable's name, without `@`".to_string()));
}
