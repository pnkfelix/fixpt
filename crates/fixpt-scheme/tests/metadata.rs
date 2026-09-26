//! Front-end metadata, carried as inert data in ordinary Scheme.
//!
//! The encoding is Twobit's (`pass2.aux.sch`): a quoted constant in a position
//! where its value is discarded, so the program remains one any Scheme can run.
//! These tests hold the two properties that make it worth doing — the
//! annotation changes *how* code compiles and never changes *what* it means,
//! and an engine that ignores it is still correct.

use fixpt_engine::Backend;
use fixpt_scheme::Session;

fn eval(backend: Backend, src: &str) -> String {
    let mut s = Session::with_backend(backend);
    s.eval_to_string("<t>", src).unwrap_or_else(|e| panic!("{e}\n  in: {src}"))
}

const NOTE: &str = "'(%fx-note (integrable +) (basis checked) (because \"immutable\"))";

#[test]
fn an_annotation_never_changes_the_answer() {
    // The same expression, annotated and not, on both engines.
    for backend in [Backend::Ast, Backend::Bytecode] {
        let plain = eval(backend, "(+ 1 2)");
        let noted = eval(backend, &format!("(begin {NOTE} (+ 1 2))"));
        assert_eq!(plain, "3");
        assert_eq!(noted, "3", "{backend:?} changed the answer");
    }
}

#[test]
fn an_unknown_annotation_is_simply_data() {
    // A note this engine has never heard of must be inert, not an error —
    // that is what lets a front end emit richer metadata than the back end
    // understands.
    assert_eq!(
        eval(Backend::Bytecode, "(begin '(%fx-note (telepathy 3) (basis asserted)) (* 6 7))"),
        "42"
    );
    // And so must a quoted datum that merely looks like one.
    assert_eq!(eval(Backend::Bytecode, "(begin '(not-a-note) 7)"), "7");
}

/// The claim only licenses anything when it is `checked`.
///
/// This is the distinction Twobit could not express: `.+:fix:fix` and an
/// unverified declaration look identical downstream. Here an `inferred` or
/// `asserted` claim is kept — a debug build could test it — but does not
/// license removing the indirection.
#[test]
fn only_a_checked_claim_is_acted_on() {
    use fixpt_engine::compile::disassemble;
    use fixpt_heap::ObjType;

    fn instructions(src: &str) -> String {
        let mut s = Session::with_backend(Backend::Bytecode);
        s.eval_str("<t>", &format!("(define (f a b) {src})")).expect("compiles");
        let sym = s.rt.heap.intern_existing("f").expect("defined");
        let v = s.rt.heap.global(s.rt.heap.symbol_global_slot(sym));
        let code = s.rt.heap.closure_code(v);
        assert!(s.rt.heap.is_a(code, ObjType::Code));
        disassemble(&s.rt.heap, code)
    }

    let plain = instructions("(+ a b)");
    assert!(plain.contains("global"), "an ordinary call loads the operator:\n{plain}");
    assert!(plain.contains("tail-call"), "{plain}");

    let checked = instructions(&format!("(begin {NOTE} (+ a b))"));
    assert!(checked.contains("prim"), "a checked claim compiles to a direct call:\n{checked}");
    assert!(!checked.contains("global"), "the global load should be gone:\n{checked}");

    let guessed = instructions(
        "(begin '(%fx-note (integrable +) (basis inferred)) (+ a b))",
    );
    assert!(
        guessed.contains("global") && !guessed.contains("prim"),
        "an inferred claim must not license the optimisation:\n{guessed}"
    );
}

/// A claim about a name this engine has no primitive for is ignored, not
/// obeyed — the front end's vocabulary is its own.
#[test]
fn a_claim_about_an_unknown_primitive_is_ignored() {
    assert_eq!(
        eval(
            Backend::Bytecode,
            "(define (g x) (* x 2))
             (begin '(%fx-note (integrable g) (basis checked)) (g 21))"
        ),
        "42"
    );
}


/// A proved-pure expression whose value is discarded is not evaluated at all.
///
/// The observable consequence: if the dropped expression would have printed,
/// nothing is printed. That is only sound because the claim is `checked` — a
/// `display` is *not* pure, and annotating it as such is a lie the compiler is
/// entitled to believe. So the test asserts both halves: the lie is obeyed, and
/// the same lie marked `inferred` is not.
#[test]
fn a_pure_unused_expression_is_dropped() {
    fn printed(src: &str) -> String {
        let mut s = Session::with_backend(Backend::Bytecode);
        let (out, r) = s.eval_capturing("<t>", src);
        r.unwrap_or_else(|e| panic!("{e}"));
        out
    }

    // Without a claim, the call happens.
    assert_eq!(printed("(begin (display \"x\") 1)"), "x");

    // With a checked claim that it is pure, it does not.
    assert_eq!(
        printed(
            "(begin (begin '(%fx-note (pure) (basis checked) (because \"effect pure\")) \
             (display \"x\")) 1)"
        ),
        "",
        "a checked purity claim should let the call be dropped"
    );

    // Marked as a guess, it is kept.
    assert_eq!(
        printed(
            "(begin (begin '(%fx-note (pure) (basis inferred)) (display \"x\")) 1)"
        ),
        "x",
        "an inferred claim must not license removing code"
    );
}

/// The value of the sequence is unaffected either way.
#[test]
fn dropping_a_pure_expression_keeps_the_answer() {
    for note in ["(basis checked)", "(basis inferred)"] {
        let src = format!(
            "(begin (begin '(%fx-note (pure) {note}) (+ 1 1)) (* 6 7))"
        );
        assert_eq!(eval(Backend::Bytecode, &src), "42");
        assert_eq!(eval(Backend::Ast, &src), "42");
    }
}
