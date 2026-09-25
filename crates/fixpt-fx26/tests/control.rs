//! Delimited control, typed: prompts, composable continuations and marks.
//!
//! The rules are this project's own (`docs/fx26.md`, "Control, typed"), so
//! each case is here because the rule could get it wrong. For each one, the
//! comment says which rule it tests and what a wrong rule would do. The
//! programs are in `programs/control/`.

use fixpt_fx26::Checker;

const TAG: &str = "(prompt-tag int int pure @p)";
/// A tag whose aborts carry a continuation back to the handler.
const K_TAG: &str = "(prompt-tag int (composable int int pure @p) pure @p)";

fn checker() -> Checker {
    let mut c = Checker::new();
    c.bind("t", TAG).expect("binds");
    c.bind("u", TAG).expect("binds");
    c.bind("s", K_TAG).expect("binds");
    c
}

/// The type and effect of `program`, printed.
fn check(c: &mut Checker, program: &str) -> String {
    let k = c.check_program(program).unwrap_or_else(|e| panic!("does not check: {e}\n{program}"));
    format!("{} ! {}", c.show_ty(k.ty), c.show_effect(&k.effect))
}

fn rejects(c: &mut Checker, program: &str) -> String {
    match c.check_program(program) {
        Ok(k) => panic!("checks as {}, and should not:\n{program}", c.show_ty(k.ty)),
        Err(e) => e.message,
    }
}

// ------------------------------------------------------ the prompt delimits

/// Delimiting: without the prompt the abort has `(goto @p)`; with it, the
/// prompt catches it. A rule that never delimited would leave the `goto`.
#[test]
fn a_prompt_catches_an_abort_to_its_own_tag() {
    let mut c = checker();
    let bare = "(+ 1 ((proj (proj abort-current-continuation @p) int int pure) t 5))";
    assert_eq!(check(&mut c, bare), "int ! (goto @p)");
    assert_eq!(check(&mut c, include_str!("programs/control/own-abort.fx")), "int ! pure");
}

/// The condition on delimiting: a region holds many tags, and an abort to
/// another one passes through. A rule that delimited every control effect on
/// the tag's region would remove this `goto`, and be unsound.
#[test]
fn an_abort_to_another_tag_in_the_region_passes_through() {
    let mut c = checker();
    assert_eq!(check(&mut c, include_str!("programs/control/other-tag.fx")), "int ! (goto @p)");
}

/// The same through a subroutine: `g` may abort to any tag in `@p`, so it
/// counts as reaching the region.
#[test]
fn a_subroutine_that_aborts_passes_through() {
    let mut c = checker();
    c.bind("g", "(subr (goto @p) () int)").expect("binds");
    assert_eq!(check(&mut c, "(prompt t (g) (lambda ((v int)) v))"), "int ! (goto @p)");
}

/// A tag made on the spot, rather than named: the body cannot mention it,
/// so it reaches `@p` only through `u`, and the `goto` stays — as does the
/// tag's allocation, since `u` makes `@p` visible. When nothing in the body
/// reaches `@p`, the prompt is pure.
#[test]
fn a_fresh_tag_delimits_only_what_cannot_reach_other_tags() {
    let mut c = checker();
    assert_eq!(
        check(&mut c, include_str!("programs/control/fresh-tag.fx")),
        "int ! (maxeff (alloc @p) (goto @p))"
    );
    let alone = "(prompt ((proj (proj make-continuation-prompt-tag @p) int int pure))
                   5 (lambda ((v int)) v))";
    assert_eq!(check(&mut c, alone), "int ! pure");
}

// ------------------------------------------------- the tag fixes the types

/// The answer type: every prompt for a tag delivers the tag's `A`.
#[test]
fn the_body_must_produce_the_tags_answer_type() {
    let mut c = checker();
    let err = rejects(&mut c, "(prompt t #t (lambda ((v int)) v))");
    assert!(err.contains("deliver a int, and this body is a bool"), "{err}");
}

/// The payload type: an abort carries an `H`, so the handler must take one.
#[test]
fn the_handler_must_take_the_payload_to_the_answer() {
    let mut c = checker();
    let err = rejects(&mut c, "(prompt t 1 (lambda ((v bool)) 1))");
    assert!(err.contains("the handler must take a int to a int"), "{err}");
    let err = rejects(&mut c, "(prompt t 1 (lambda ((v int)) #f))");
    assert!(err.contains("the handler must take a int to a int"), "{err}");
    let err = rejects(&mut c, "((proj (proj abort-current-continuation @p) int int pure) t #t)");
    assert!(err.contains("argument 2 is a bool"), "{err}");
}

/// `shift k k`, which would change the answer type, is rejected; the same
/// capture with the answer type kept is not. A rule that let the handler's
/// result differ from the tag's answer would accept both.
#[test]
fn a_fixed_answer_type_rules_out_answer_type_modification() {
    let mut c = checker();
    let err = rejects(&mut c, include_str!("programs/control/shift-k-k.fx"));
    assert!(err.contains("the handler must take"), "{err}");
    // The handler runs after the prompt, so its call of `k` is not delimited.
    assert_eq!(
        check(&mut c, include_str!("programs/control/shift-k-apply.fx")),
        "int ! (maxeff (goto @p) (comefrom @p))"
    );
}

/// The bound: a tag's `D` is what a continuation captured up to one of its
/// prompts is said to do when called, so a body may not do more. Without the
/// check, a continuation's latent effect would be a lie.
#[test]
fn the_body_must_stay_within_the_tags_effect() {
    let mut c = checker();
    c.bind("cell", "(ref int @x)").expect("binds");
    let body = "(prompt t ((proj (proj get @x) int) cell) (lambda ((v int)) v))";
    let err = rejects(&mut c, body);
    assert!(err.contains("allows its delimited computations pure, and this body also has (read @x)"), "{err}");
    c.bind("t", "(prompt-tag int int (read @x) @p)").expect("binds");
    assert_eq!(check(&mut c, body), "int ! (read @x)");
}

// ------------------------------------------------- composable continuations

/// Captured and resumed inside its prompt: all the control is delimited.
#[test]
fn a_continuation_resumed_inside_its_prompt_is_delimited() {
    let mut c = checker();
    assert_eq!(check(&mut c, include_str!("programs/control/capture-and-resume.fx")), "int ! pure");
}

/// A composable continuation is called like a subroutine, with its tag's
/// bound and the control effects on its region as the latent effect.
#[test]
fn a_composable_continuation_is_a_subroutine() {
    let mut c = checker();
    let k = c.type_of_str("(composable int bool (read @x) @p)").expect("a type");
    let as_subr = c.type_of_str("(subr (maxeff (read @x) (goto @p) (comefrom @p)) (int) bool)").expect("a type");
    let too_small = c.type_of_str("(subr (read @x) (int) bool)").expect("a type");
    assert!(c.subtype(k, as_subr));
    assert!(!c.subtype(k, too_small), "its control effects were forgotten");
    assert!(!c.subtype(as_subr, k), "any subroutine passed as a continuation");
}

// -------------------------------------------------------------------- marks

/// A mark key is a location in the dynamic context: made privately, its
/// writes and reads are masked, as a private cell's are.
#[test]
fn marks_on_a_private_key_are_masked() {
    let mut c = checker();
    assert_eq!(check(&mut c, include_str!("programs/control/private-mark.fx")), "int ! pure");
}

#[test]
fn marks_on_a_shared_key_are_effects() {
    let mut c = checker();
    c.bind("key", "(mark-key int @m)").expect("binds");
    assert_eq!(
        check(&mut c, include_str!("programs/control/shared-mark.fx")),
        "int ! (maxeff (read @m) (write @m))"
    );
}

/// Reading a captured continuation's marks gives a fresh list: FX-87's
/// `listof`, a pair whose tail is itself, which `nil` also inhabits.
#[test]
fn the_marks_of_a_continuation_are_a_list() {
    let mut c = checker();
    c.bind("k", "(composable int int pure @p)").expect("binds");
    c.bind("key", "(mark-key int @m)").expect("binds");
    let marks = "((proj (proj marks-of @m @p @l) int int int pure) k key)";
    assert_eq!(check(&mut c, marks), "(listof int @l) ! (maxeff (read @m) (alloc @l))");
    let empty = "((proj (proj null? @l) int (listof int @l)) (proj (proj nil @l) int (listof int @l)))";
    assert_eq!(check(&mut c, empty), "bool ! pure");
}

/// A prompt needs a tag.
#[test]
fn a_prompt_needs_a_tag() {
    let mut c = checker();
    let err = rejects(&mut c, "(prompt 3 1 (lambda ((v int)) v))");
    assert!(err.contains("a prompt needs a prompt tag, not a int"), "{err}");
}
