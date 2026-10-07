//! Jouvelot & Gifford, *Reasoning about Continuations with Control Effects*,
//! PLDI '89 — the cases in `tests/conformance/fx26/pldi89-cases.md`, which
//! were written down and reviewed before this checker existed.
//!
//! Each assertion says what it rests on, in the document's terms: STATED
//! (the paper says it), DERIVED (from its rules), and where the typed program
//! is TRANSCRIBED from the paper's untyped Scheme. Page numbers are PDF pages.

use fixpt_fx26::ast::{Atom, Effect};
use fixpt_fx26::Checker;

/// `K`: a continuation returned as its own result (C4, C5).
const K: &str = "(dletrec ((k (subr (goto @k) (k) void))) k)";

fn atom(c: &mut Checker, text: &str) -> Atom {
    let e = c.effect_of_str(text).expect("an effect");
    *e.0.iter().next().expect("one atom")
}

fn effect_is(c: &mut Checker, got: &Effect, want: &str) {
    let want_e = c.effect_of_str(want).expect("an effect");
    assert_eq!(got, &want_e, "got {}, want {want}", c.show_effect(got));
}

fn has(c: &mut Checker, got: &Effect, a: &str) -> bool {
    let a = atom(c, a);
    got.contains(a)
}

// ------------------------------------------------------------------- C1

/// KFX without control: the kernel reproduces the paper's own example.
#[test]
fn c1_twice() {
    let mut c = Checker::new();
    let got = c
        .check_str(
            "(plambda ((t type))
               (plambda ((e effect))
                 (lambda ((f (subr e (t) t)))
                   (lambda ((x t)) (f (f x))))))",
        )
        .expect("checks");
    // STATED, p. 3.
    let want = "(poly ((t type)) (poly ((e effect)) (subr pure ((subr e (t) t)) (subr e (t) t))))";
    assert_eq!(c.show_ty(got.ty), want);
    let want_ty = c.type_of_str(want).expect("a type");
    assert!(c.subtype(got.ty, want_ty) && c.subtype(want_ty, got.ty));
    // DERIVED: the `plambda` rule (p. 3).
    assert!(got.effect.is_pure());
}

// ------------------------------------------------------------------- C2

#[test]
fn c2_cwcc_has_the_papers_type() {
    let mut c = Checker::new();
    // STATED, p. 4 (binders parenthesised, FX-87 style).
    let want = c
        .type_of_str(
            "(poly ((r region)) (poly ((t type)) (poly ((e effect))
               (subr (maxeff (comefrom r) e) ((subr e ((subr (goto r) (t) void)) t)) t))))",
        )
        .expect("a type");
    // Its binding's: `cwcc` is named only to call it (F15).
    let name = c.interner.intern("cwcc");
    let got = c.type_of_name(name).expect("bound");
    assert!(c.subtype(got, want) && c.subtype(want, got), "{}", c.show_ty(got));
}

// ------------------------------------------------------------------- C3

const C3: &str = "(+ ((proj (proj (proj cwcc @k) int) (goto @k))
                      (lambda ((f (subr (goto @k) (int) void))) (f 0)))
                     1)";

/// A well-behaved use: both control effects, then masked away.
#[test]
fn c3_well_behaved_control_is_masked() {
    let mut c = Checker::new();
    c.masking = false;
    let before = c.check_str(C3).expect("checks");
    // STATED (p. 5), exact form DERIVED by the application rule (p. 3).
    effect_is(&mut c, &before.effect, "(maxeff (comefrom @k) (goto @k))");

    let mut c = Checker::new();
    let after = c.check_str(C3).expect("checks");
    // STATED: "its control effects can thus be masked" (p. 5).
    assert!(after.effect.is_pure(), "{}", c.show_effect(&after.effect));
    // DERIVED: `cwcc`'s result type, projected to `int`.
    assert_eq!(c.show_ty(after.ty), "int");
}

/// C3 needs `void` to be the bottom type: `(f 0)` stands where `int` is
/// expected. Settled in review.
#[test]
fn c3_needs_void_below_int() {
    let mut c = Checker::new();
    let void = c.type_of_str("void").expect("a type");
    let int = c.type_of_str("int").expect("a type");
    assert!(c.subtype(void, int));
    assert!(!c.subtype(int, void));
}

// ------------------------------------------------------------------- C4

/// `(f g)` calls a continuation, so it has a `goto`, and nothing may be moved
/// past it.
#[test]
fn c4_calling_a_continuation_has_a_goto() {
    let mut c = Checker::new();
    c.bind("f", K).expect("binds");
    c.bind("g", K).expect("binds");
    let call = c.check_str("(f g)").expect("checks");
    // DERIVED: `f`'s latent effect is `(goto @k)` (p. 3, p. 4). It stays after
    // masking: `f` and `g` are free and their types mention `@k`. And, beyond
    // the paper: `K` is a recursive type, through which a continuation can be
    // given itself, so a call through it may spin.
    effect_is(&mut c, &call.effect, "(maxeff (goto @k) spin)");
}

#[test]
fn c4_the_argument_keeps_both_control_effects() {
    let mut c = Checker::new();
    c.bind("h", "(subr pure () unit)").expect("binds");
    // TRANSCRIBED: only the outer `cwcc`'s argument (the whole `let` does not
    // type — it passes `0` to a continuation).
    let got = c
        .check_program(include_str!("programs/pldi89/c4-argument.fx"))
        .expect("checks");
    let fixpt_fx26::ast::Ty::Subr { effect, .. } = c.arena.get(got.ty).clone() else {
        panic!("a subroutine: {}", c.show_ty(got.ty));
    };
    // DERIVED: the body imports `f`, whose type mentions `@k`, so neither
    // control effect is masked from the latent effect.
    assert!(has(&mut c, &effect, "(goto @k)"), "{}", c.show_effect(&effect));
    assert!(has(&mut c, &effect, "(comefrom @k)"), "{}", c.show_effect(&effect));
}

// ------------------------------------------------------------------- C5

/// Calls to `cwcc` are not pure, so they cannot be common-subexpression
/// eliminated.
#[test]
fn c5_cwcc_calls_are_not_pure() {
    let mut c = Checker::new();
    let got = c
        .check_str(&format!("((proj (proj (proj cwcc @k) {K}) pure) (lambda ((x {K})) x))"))
        .expect("checks");
    // STATED: "cannot be pure" (p. 4). Exact form DERIVED with `e = pure`, and
    // it survives masking because the result type `K` mentions `@k` (p. 6).
    // FX-26's own: `spin`, since the continuation, returned, can be called
    // after `cwcc` has returned, and come back to it again
    // (`docs/research/soundness-findings.md`, F3).
    effect_is(&mut c, &got.effect, "(maxeff (comefrom @k) spin)");
}

// ------------------------------------------------------------------- C6

const C6: &str = include_str!("programs/pldi89/c6.fx");

fn c6_checker(masking: bool) -> Checker {
    let mut c = Checker::new();
    c.masking = masking;
    c.bind("x", "(ref (subr pure () (subr (goto @k) (unit) void)) @x)").expect("binds");
    c.bind("h", "(subr pure () unit)").expect("binds");
    c
}

/// Storing a continuation where the caller can reach it: `comefrom` cannot
/// be masked.
#[test]
fn c6_a_stored_continuation_keeps_its_comefrom() {
    let mut c = c6_checker(false);
    let before = c.check_str(C6).expect("checks");
    // DERIVED by the application rule (p. 3); and FX-26's own `spin`, since
    // the continuation is kept, and could be called after `cwcc` returns (F3).
    effect_is(&mut c, &before.effect, "(maxeff (comefrom @k) (write @x) spin)");

    let mut c = c6_checker(true);
    let after = c.check_str(C6).expect("checks");
    // DERIVED from the `comefrom` masking theorem (p. 6): `x` is imported and
    // its type mentions `@k`. The typed form of the STATED "isn't
    // continuation discarding" (p. 6).
    assert!(has(&mut c, &after.effect, "(comefrom @k)"), "{}", c.show_effect(&after.effect));
    // FX-87's memory masking: `x`'s type mentions `@x`.
    assert!(has(&mut c, &after.effect, "(write @x)"), "{}", c.show_effect(&after.effect));
}

// ------------------------------------------------------------------- C7

/// The contrived example: a `goto` that must not be masked although the
/// expression has no free variables.
///
/// REVIEWER'S SKEPTICISM (kept deliberately, review 2026-09-25): the claim is
/// STATED (p. 7), but the typed program is TRANSCRIBED — the recursive types,
/// the choice of one region for both `cwcc`s and every projected latent effect
/// are a reconstruction the paper never gives. If this test fails, suspect the
/// transcription before the checker.
#[test]
fn c7_goto_not_masked_without_free_variables() {
    let mut c = Checker::new();
    let got = c
        .check_program(include_str!("programs/pldi89/c7.fx"))
        .unwrap_or_else(|e| panic!("C7 does not check: {e}"));
    // STATED (p. 7): not maskable. The condition that blocks it is the result
    // type, which mentions `@k` (p. 6) — there are no free variables to blame.
    assert!(has(&mut c, &got.effect, "(goto @k)"), "{}", c.show_effect(&got.effect));
}

// ---------------------------------------------- FX-87's memory masking kept

/// FX-26 starts from FX-87's masking rule for memory, before adding control;
/// these are its cases (`crates/fixpt-fx87/src/mask.rs`).
#[test]
fn memory_masking_is_fx87s() {
    let mut c = Checker::new();
    // A private cell nobody can see: its allocation vanishes.
    let got = c.check_str("(let ((r ((proj (proj new @private) int) 3))) 3)").expect("checks");
    assert!(got.effect.is_pure(), "{}", c.show_effect(&got.effect));
    // The cell escapes in the result: its allocation stays.
    let got = c.check_str("(let ((r ((proj (proj new @private) int) 3))) r)").expect("checks");
    effect_is(&mut c, &got.effect, "(alloc @private)");
    // Written through a parameter the caller passed: the write stays.
    let got = c
        .check_str("(lambda ((v (ref int @shared))) ((proj (proj set @shared) int) v 1))")
        .expect("checks");
    let fixpt_fx26::ast::Ty::Subr { effect, .. } = c.arena.get(got.ty).clone() else {
        panic!("a subroutine");
    };
    effect_is(&mut c, &effect, "(write @shared)");
}

#[test]
fn a_plambda_body_must_be_pure() {
    let mut c = Checker::new();
    let err = c
        .check_str("(plambda ((r region)) ((proj (proj new @shared) int) 1))")
        .expect_err("impure");
    assert!(err.message.contains("must be pure"), "{err}");
}
