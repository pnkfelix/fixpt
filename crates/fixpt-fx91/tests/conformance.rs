//! FX-91 conformance, reported as a running count.
//!
//! The front end is built in stages, so this reports progress rather than
//! simply passing or failing: at each stage the assertion is a *floor* that
//! must not regress, and the printed summary shows how far the current stage
//! has got. Partial work then reads as partial work.

use fixpt_conform::{normalize, parse_goldens, Outcome, Report, Verdict};
use fixpt_fx91::check::Checker;
use fixpt_fx91::{Arena, Parser};
use fixpt_read::{Interner, Reader, SourceMap, SyntaxProfile};

const GOLDENS: &str = include_str!("../../../tests/conformance/fx91/tests.expected");
const SOURCE: &str = include_str!("../../../tests/conformance/fx91/cases/tests.fx");

fn read_forms() -> (Vec<fixpt_read::Syntax>, Interner) {
    let mut sources = SourceMap::new();
    let mut interner = Interner::new();
    let file = sources.add("tests.fx", SOURCE);
    let forms = Reader::new(SOURCE, file, SyntaxProfile::FX91, &mut interner)
        .read_all()
        .expect("the FX-91 test suite reads");
    (forms, interner)
}

#[test]
fn every_form_parses() {
    let (forms, mut interner) = read_forms();
    let cases = parse_goldens(GOLDENS).expect("goldens parse");
    assert_eq!(forms.len(), cases.len(), "corpus and goldens must line up");

    let mut arena = Arena::new();
    let mut report = Report::default();
    for (form, case) in forms.iter().zip(&cases) {
        let mut parser = Parser::new(&mut arena, &mut interner);
        let alpha = parser.init_alpha;
        let verdict = match parser.parse_exp(alpha, form) {
            Ok(_) => Verdict::Match,
            Err(e) => Verdict::Error { message: e.to_string() },
        };
        report.record(case, verdict);
    }
    println!("{}", report.summary("fx91 parse"));
    print!("{}", report.detail(8));
    assert_eq!(report.matched.len(), 182, "all 182 forms must parse\n{}", report.detail(8));
}

/// The built-in `fx` module has to load before anything else can be checked.
#[test]
fn the_fx_module_bootstraps() {
    let mut arena = Arena::new();
    let mut interner = Interner::new();
    let checker = Checker::new(&mut arena, &mut interner).expect("the fx module loads");
    // A representative sample of what the signature must have published.
    for name in ["int", "bool", "listof", "sexp", "refof"] {
        let sym = checker.p.interner.get(name).unwrap_or_else(|| panic!("{name} interned"));
        let _ = sym;
    }
    assert!(arena.len() > 500, "the fx signature builds a substantial arena");
}

#[test]
fn types_and_effects_match_the_reference() {
    let (forms, mut interner) = read_forms();
    let cases = parse_goldens(GOLDENS).expect("goldens parse");
    let mut arena = Arena::new();
    let mut checker = Checker::new(&mut arena, &mut interner).expect("the fx module loads");
    checker.load_base = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/conformance/fx91/cases");

    let mut report = Report::default();
    for (form, case) in forms.iter().zip(&cases) {
        checker.reset();
        let alpha = checker.p.init_alpha;
        let verdict = match checker.p.parse_exp(alpha, form) {
            Err(e) => Verdict::Error { message: format!("parse: {e}") },
            Ok(node) => match checker.type_effect_of_exp(node) {
                Ok((ty, effect)) => {
                    let got_ty = normalize(&checker.render_dexp(ty));
                    let got_effect = normalize(&checker.render_dexp(effect));
                    match &case.outcome {
                        Outcome::Typed { ty: want_ty, effect: want_effect } => {
                            let want = (normalize(want_ty), normalize(want_effect));
                            if (got_ty.clone(), got_effect.clone()) == want {
                                Verdict::Match
                            } else {
                                Verdict::Mismatch {
                                    expected: format!("{} ! {}", want.0, want.1),
                                    got: format!("{got_ty} ! {got_effect}"),
                                }
                            }
                        }
                        Outcome::StaticError { message } => Verdict::Mismatch {
                            expected: format!("<error: {message}>"),
                            got: format!("{got_ty} ! {got_effect}"),
                        },
                    }
                }
                Err(e) => Verdict::Error { message: e.to_string() },
            },
        };
        report.record(case, verdict);
    }
    println!("{}", report.summary("fx91 type/effect"));
    print!("{}", report.detail(10));

    // Full conformance: every form's type and effect agrees with the
    // reference, after normalising the run-dependent identifier numbering.
    assert_eq!(
        report.matched.len(),
        182,
        "regression from full conformance\n{}",
        report.detail(10)
    );
}

/// Bugs in the 1991 source that are reproduced rather than repaired.
///
/// The reference implementation is what defines which programs FX-91 accepts,
/// so matching it is what makes the 182-case corpus mean anything; "fixing"
/// these would produce disagreements indistinguishable from our own mistakes.
/// These tests exist so the behaviour is deliberate and visible rather than
/// accidental. Each names the intended comparison. See `docs/divergences.md`.
#[test]
fn reference_bugs_are_reproduced_deliberately() {
    let mut arena = Arena::new();
    let mut interner = Interner::new();
    let mut checker = Checker::new(&mut arena, &mut interner).expect("the fx module loads");

    let parse = |c: &mut Checker, text: &str| -> fixpt_fx91::FxId {
        let mut sources = SourceMap::new();
        let file = sources.add("<test>", text);
        let form = Reader::new(text, file, SyntaxProfile::FX91, c.p.interner)
            .read()
            .expect("reads")
            .expect("one form");
        let alpha = c.p.init_alpha;
        c.p.parse_dexp(alpha, &form).expect("parses")
    };

    // `unify-poly?` compares `(poly-body dexp1)` with itself, so two `poly`
    // types unify whenever their arity and kinds agree — whatever their bodies
    // say. Intended: compare dexp1's body with dexp2's.
    let a = parse(&mut checker, "(poly ((t type)) (subr (maxeff) ((x t)) t))");
    let b = parse(&mut checker, "(poly ((u type)) (subr (maxeff) ((y u)) bool))");
    assert!(
        checker.unify(a, b).expect("no error"),
        "unify-poly?'s self-comparison makes these unify; see docs/divergences.md"
    );

    // `dlambda<=?` recurses with itself rather than with `description<=-1?`,
    // and a dlambda's body is a type, so the recursion fails at once.
    let c = parse(&mut checker, "(dlambda ((t type)) t)");
    let d = parse(&mut checker, "(dlambda ((t type)) t)");
    // Equal descriptions still compare equal by identity, so use two distinct
    // but equivalent ones to see the failure.
    assert!(
        !checker.description_leq(c, d).expect("no error"),
        "dlambda<=?'s self-recursion makes even equivalent dlambdas incomparable"
    );
}
