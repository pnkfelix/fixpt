//! `letrena` and `letreap` (PLAN.md, "Regions that end"): a region that
//! lives while its body runs, as an arena or as a heap of its own. The two
//! share their typing rule, which both checkers apply (`tests/checker.rs`
//! reads these programs and compares them). Register code makes a
//! `letrena`'s allocations in a region of the heap's where it can
//! (`tests/register_code.rs`); otherwise, and in every other back end, a
//! region's allocation is the heap's, and the body just runs.

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

/// A region's name is also a value, `(place r)`, which `rcons` allocates
/// in; like anything that mentions the region, it cannot leave the body,
/// and a closure over it is as bound to the region as the region is.
#[test]
fn a_region_is_a_value_to_allocate_in() {
    assert_eq!(check("(letrena r (car (the (listof int r) (rcons r 1 nil))))"), Ok(vec!["int ! pure".to_string()]));
    assert_eq!(check("(letreap r (car (cdr (the (listof int r) (rcons r 1 (rcons r 2 nil))))))"), Ok(vec!["int ! pure".to_string()]));
    assert_eq!(
        check("(letrena r r)"),
        Err("the value of `letrena r` would outlive its region: its type is (place r)".to_string())
    );
    let e = check("(letrena r (lambda ((x int)) (the (listof int r) (rcons r x nil))))");
    assert!(e.as_ref().is_err_and(|m| m.contains("would outlive its region")), "{e:?}");
    assert_eq!(
        check("(define f (subr pure (int) int) (lambda (n) (letrena r (let ((k (lambda ((x int)) (the (listof int r) (rcons r x nil))))) (car (k n)))))) (f 3)"),
        Ok(vec!["int ! pure".to_string()])
    );
}

/// Each allocator has a version that takes the region to allocate in, whose
/// result is in that region.
#[test]
fn every_allocator_takes_a_region() {
    assert_eq!(check("(letrena r (get (rnew r 1)))"), Ok(vec!["int ! pure".to_string()]));
    assert_eq!(check("(letrena r (array-length (the (arrayof int r) (rmake-array r 3 0))))"), Ok(vec!["int ! pure".to_string()]));
    assert_eq!(check("(letrena r (bloblet-ref (rmake-bloblet r 0 7) 0))"), Ok(vec!["int ! pure".to_string()]));
    assert_eq!(
        check("(letrena r (rmake-bloblet r 0 7))"),
        Err("the value of `letrena r` would outlive its region: its type is (bloblet (fields int) r)".to_string())
    );
    assert_eq!(check("(rmake-bloblet 1 0 7)"), Err("a region is expected here, and this is a int".to_string()));
}

/// A closure made in a region reads the region when called, so its type
/// mentions the region, and it cannot leave; a `plambda` may make one,
/// its only effect allocating, though nothing else that allocates.
#[test]
fn closures_in_a_region() {
    assert_eq!(check("(letrena r ((rlambda r ((x int)) (+ x 1)) 2))"), Ok(vec!["int ! pure".to_string()]));
    assert_eq!(
        check("(letrena r (rlambda r ((x int)) x))"),
        Err("the value of `letrena r` would outlive its region: its type is (subr (read r) (int) int)".to_string())
    );
    let e = check("(letrena r (let ((f (the (subr pure (int) int) (rlambda r ((x int)) x)))) (f 1)))");
    assert!(e.is_err(), "a closure in r is not pure to call: {e:?}");
    assert_eq!(
        check("(letrena r ((proj (plambda ((t type)) (rlambda r ((x t)) x)) int) 3))"),
        Ok(vec!["int ! pure".to_string()])
    );
    let e = check("(letrena r (get (proj (plambda ((t type)) (rnew r 1)) int)))");
    assert!(e.as_ref().is_err_and(|m| m.contains("a `plambda` body must be pure")), "{e:?}");
}

/// `letregion` binds a region for analysis only: its body is masked as a
/// `letrena`'s is, nothing mentioning it may leave, and its name is no
/// value, since it makes no place.
#[test]
fn a_letregion_is_a_region_with_no_place() {
    assert_eq!(check("(letregion r (car (the (listof int r) (cons 1 nil))))"), Ok(vec!["int ! pure".to_string()]));
    assert!(check("(letregion r (the (listof int r) (cons 1 nil)))").unwrap_err().contains("would outlive its region"));
    assert!(check("(letregion r (car (the (listof int r) (rcons r 1 nil))))").unwrap_err().contains("unbound variable `r`"));
    assert_eq!(check("(letrena r r)"), Err("the value of `letrena r` would outlive its region: its type is (place r)".to_string()));
}

/// `letfreeze` binds a region for analysis, as `letregion` does, and its
/// value leaves with that region made `const`: frozen data, which reading is
/// pure and nothing may write. What leaves may not keep a way to write it.
#[test]
fn a_letfreeze_freezes_its_regions_data() {
    let build = "(letfreeze r (let ((xs (the (listof int r) (cons 1 nil)))) (begin (set-car! xs 2) xs)))";
    assert_eq!(check(build), Ok(vec!["(listof int const) ! pure".to_string()]));
    assert_eq!(check(&format!("(car {build})")), Ok(vec!["int ! pure".to_string()]));
    assert_eq!(check(&format!("(set-car! {build} 3)")), Err("this writes frozen data, whose region is `const`".to_string()));
    assert!(check("(letfreeze r (let ((xs (the (listof int r) (cons 1 nil)))) (lambda () (set-car! xs 2))))")
        .unwrap_err()
        .contains("could still write its region's data"));
}
