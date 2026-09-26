//! Bloblets in FX-26 (`PLAN.md` §11, step 6): their types and effects, and
//! running them on both engines.

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
fn a_new_bloblet_has_its_fields_types_and_allocates() {
    // Nothing else sees the new region, and it escapes in the result, so
    // the allocation stays.
    assert_eq!(check("(make-bloblet 8 1 #t)"), "(bloblet (fields int bool) bloblet.1) ! (alloc bloblet.1)");
    // Checked against a type, it takes that type's region.
    assert_eq!(check("(the (bloblet (fields int) @r) (make-bloblet 0 1))"), "(bloblet (fields int) @r) ! (alloc @r)");
}

#[test]
fn reading_and_writing_fields_are_effects_on_the_region() {
    let b = "(define b (bloblet (fields int string) @r) (make-bloblet 0 1 \"x\"))";
    assert_eq!(check(&format!("{b} (bloblet-ref b 1)")), "string ! (read @r)");
    assert_eq!(check(&format!("{b} (bloblet-set! b 0 5)")), "unit ! (write @r)");
    assert_eq!(check(&format!("{b} (bloblet-byte b 0)")), "int ! (read @r)");
    assert_eq!(check(&format!("{b} (bloblet-bytes b)")), "int ! pure");
}

#[test]
fn frozen_fields_read_purely_and_cannot_be_written() {
    let b = "(define b (bloblet (frozen int) @r) (bloblet-freeze (the (bloblet (fields int) @r) (make-bloblet 0 1))))";
    assert_eq!(check(&format!("{b} (bloblet-ref b 0)")), "int ! pure");
    let err = rejects(&format!("{b} (bloblet-set! b 0 2)"));
    assert!(err.contains("its fields are frozen"), "{err}");
    // Freezing is a change of type, not a subtype.
    let err = rejects("(the (bloblet (frozen int) @r) (the (bloblet (fields int) @r) (make-bloblet 0 1)))");
    assert!(err.contains("is expected here"), "{err}");
}

#[test]
fn fields_are_checked() {
    let b = "(define b (bloblet (fields int) @r) (make-bloblet 0 1))";
    let err = rejects(&format!("{b} (bloblet-ref b 1)"));
    assert!(err.contains("has no field 1"), "{err}");
    let err = rejects(&format!("{b} (bloblet-set! b 0 #t)"));
    assert!(err.contains("int is expected"), "{err}");
    let err = rejects("(bloblet-ref 5 0)");
    assert!(err.contains("a bloblet is expected"), "{err}");
    let err = rejects("(define b (bloblet (fields int) @r) (make-bloblet 0 #f))");
    assert!(err.contains("int is expected"), "{err}");
}

#[test]
fn a_bloblet_used_only_inside_masks_its_effects() {
    // The region is fresh and appears nowhere outside: all of it masks.
    assert_eq!(check("(let ((b (make-bloblet 0 1))) (bloblet-ref b 0))"), "int ! pure");
}

#[test]
fn bloblets_run() {
    assert_eq!(run(include_str!("programs/bloblet/point.fx")), "17");
    assert_eq!(run(include_str!("programs/bloblet/bytes.fx")), "259");
    assert_eq!(run("(bloblet-ref (bloblet-freeze (make-bloblet 0 \"hi\")) 0)"), "\"hi\"");
    // Frozen at run time as well: the flag is in the header.
    assert_eq!(run("(let ((b (make-bloblet 2 1))) (bloblet-freeze b))"), "#<bloblet 2 fields 2 bytes>");
}
