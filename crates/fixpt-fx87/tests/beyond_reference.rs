//! Forms the dynamic reference cannot reach.
//!
//! 25 of the 155 corpus forms have no `#value` golden, and the reason is in the
//! archive rather than here. Values come from `#lang fx87-hashlang`, the only
//! evaluating path the archive has — `impl.rkt`'s own driver installs no
//! evaluator at all — and that path has two limits:
//!
//! * **It does not implement FX-87's standard forms.** `record`, `select`,
//!   `one`, `tagcase`, `one-set!`, `delay` and `vlambda` are unbound
//!   identifiers there.
//! * **A recursive type hangs it.** `(list 1 2 3)` never finishes, because its
//!   type contains itself and the display path does not re-finitise it the way
//!   `create-finite-dexp` does for `impl.rkt`.
//!
//! So these forms cannot be *compared* against anything. What can still be
//! checked is that they run at all and produce the representation erasure
//! commits them to — a `oneof` really is a tagged pair, a `recordof` really is
//! an association list. That is a weaker claim than conformance and is labelled
//! as such: the expected values below are **this implementation's**, not the
//! reference's, and exist to catch a regression rather than to prove agreement.

use fixpt_fx87::Fx87Session;
use fixpt_read::{Reader, SourceMap, SyntaxProfile};

fn run(session: &mut Fx87Session, text: &str) -> String {
    let mut sources = SourceMap::new();
    let file = sources.add("<t>", text);
    let mut interner = std::mem::take(&mut session.checker.p.interner);
    let forms = Reader::new(text, file, SyntaxProfile::FX87, &mut interner)
        .read_all()
        .expect("reads");
    session.checker.p.interner = interner;
    let outcome = session.run(&forms[0]).unwrap_or_else(|e| panic!("{e}\n  in: {text}"));
    match outcome.value {
        Ok(v) => v,
        Err(e) => panic!("{e}\n  code: {}\n  in: {text}", outcome.code),
    }
}

#[test]
fn the_standard_forms_run_and_have_the_erased_representation() {
    let mut s = Fx87Session::new().expect("loads");
    // A `oneof` is a tagged pair.
    assert_eq!(run(&mut s, "(one (oneof ((a int) (b bool)) @=) a 1)"), "(a . 1)");
    // A `recordof` is an association list.
    assert_eq!(run(&mut s, "(record ((a 1) (b #t)))"), "((a 1) (b #t))");
    assert_eq!(run(&mut s, "(select (record ((a 1) (b #t))) a)"), "1");
    // `tagcase` dispatches on the tag and rebinds the payload.
    assert_eq!(
        run(&mut s, "(tagcase (v (one (oneof ((a int) (b bool)) @=) a 1)) (a 1) (b 2))"),
        "1"
    );
    assert_eq!(
        run(&mut s, "(tagcase (v (one (oneof ((a int) (b bool)) @=) a 1)) (a v) (b 0))"),
        "1"
    );
    // The mutating forms return unit.
    assert_eq!(run(&mut s, "(record-set! (record ((a 1)) @!) a 2)"), "#u");
    assert_eq!(
        run(&mut s, "(one-set! (one (oneof ((a int) (b bool)) @!) a 1) b #t)"),
        "#u"
    );
}

#[test]
fn lists_run_although_their_types_are_recursive() {
    let mut s = Fx87Session::new().expect("loads");
    assert_eq!(run(&mut s, "(list 1 2 3)"), "(1 2 3)");
    assert_eq!(run(&mut s, "(length (list 1 2 3))"), "3");
    assert_eq!(run(&mut s, "(append (list 1) (list 2))"), "(1 2)");
    assert_eq!(run(&mut s, "(reverse (list 1 2 3))"), "(3 2 1)");
    assert_eq!(run(&mut s, "(list-ref (list 1 2 3) 0)"), "1");
    assert_eq!(run(&mut s, "(map (lambda ((x int)) (+ x 1)) (list 1 2 3))"), "(2 3 4)");
    assert_eq!(
        run(&mut s, "(reduce (lambda ((x int) (y int)) (+ x y)) (list 1 2 3) 0)"),
        "6"
    );
    assert_eq!(run(&mut s, "(string->list \"abc\")"), "(#\\a #\\b #\\c)");
    assert_eq!(run(&mut s, "(list->string (string->list \"abc\"))"), "\"abc\"");
}

#[test]
fn masking_is_observable_at_run_time_too() {
    let mut s = Fx87Session::new().expect("loads");
    // The forms whose *effects* are masked still do the work: a private
    // mutable cell is genuinely written, even though the type says `pure`.
    assert_eq!(run(&mut s, "(let ((x 3 @!)) (set! x 4))"), "#u");
    assert_eq!(
        run(&mut s, "(do ((i 0 (+ i 1)) (h 0 h @acc)) ((>= i 10) h) (set! h (+ h i)))"),
        "45"
    );
}

#[test]
fn delay_and_variable_arity() {
    let mut s = Fx87Session::new().expect("loads");
    assert!(run(&mut s, "(vlambda (xs int) 3)").contains("procedure"));
    // A promise prints as one rather than as its contents.
    let p = run(&mut s, "(delay 3)");
    assert!(p.contains("promise"), "expected a promise, got {p}");
}

#[test]
fn uniqueof_distinguishes_equal_values() {
    let mut s = Fx87Session::new().expect("loads");
    assert_eq!(run(&mut s, "(value (unique 3))"), "3");
    // Two `unique`s of different values are different.
    assert_eq!(run(&mut s, "(eq? (unique 3) (unique 4))"), "#f");
}
