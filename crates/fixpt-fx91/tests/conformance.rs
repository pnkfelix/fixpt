//! FX-91 conformance, reported as a running count.
//!
//! Two levels: the *static* one compares the inferred type and effect against
//! the reference, and the *dynamic* one compares the evaluated value. The
//! second is the stronger check — it exercises the code generator, the runtime
//! and the Scheme engine as well as the checker — and it is the reason FX-91's
//! corpus is worth more than FX-87's, whose port has no evaluator at all.
//!
//! The corpus is read with the checker's own interner rather than a throwaway
//! one: a `Sym` is an index into a specific table, so a form read against one
//! table means nothing to another.

use fixpt_conform::{normalize, parse_goldens, Case, Outcome, Report, Verdict};
use fixpt_fx91::check::Checker;
use fixpt_fx91::{Fx91Session, Parser};
use fixpt_read::{Interner, Reader, SourceMap, Syntax, SyntaxProfile};

const GOLDENS: &str = include_str!("../../../tests/conformance/fx91/tests.expected");
const SOURCE: &str = include_str!("../../../tests/conformance/fx91/cases/tests.fx");

fn cases() -> Vec<Case> {
    parse_goldens(GOLDENS).expect("goldens parse")
}

/// Read the corpus into `interner`, which must be the one that will consume it.
fn read_forms(interner: &mut Interner) -> Vec<Syntax> {
    let mut sources = SourceMap::new();
    let file = sources.add("tests.fx", SOURCE);
    Reader::new(SOURCE, file, SyntaxProfile::FX91, interner)
        .read_all()
        .expect("the FX-91 test suite reads")
}

fn corpus_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/conformance/fx91/cases")
}

#[test]
fn every_form_parses() {
    let mut parser = Parser::new();
    let mut interner = std::mem::take(&mut parser.interner);
    let forms = read_forms(&mut interner);
    parser.interner = interner;

    let cases = cases();
    assert_eq!(forms.len(), cases.len(), "corpus and goldens must line up");

    let mut report = Report::default();
    for (form, case) in forms.iter().zip(&cases) {
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
    let checker = Checker::new().expect("the fx module loads");
    assert!(checker.p.arena.len() > 500, "the fx signature builds a substantial arena");
    for name in ["int", "bool", "listof", "sexp", "refof"] {
        assert!(checker.p.interner.get(name).is_some(), "{name} should be interned");
    }
}

#[test]
fn types_and_effects_match_the_reference() {
    let mut checker = Checker::new().expect("the fx module loads");
    checker.load_base = corpus_dir();
    let mut interner = std::mem::take(&mut checker.p.interner);
    let forms = read_forms(&mut interner);
    checker.p.interner = interner;

    let cases = cases();
    let mut report = Report::default();
    for (form, case) in forms.iter().zip(&cases) {
        checker.reset();
        let alpha = checker.p.init_alpha;
        let verdict = match checker.p.parse_exp(alpha, form) {
            Err(e) => Verdict::Error { message: format!("parse: {e}") },
            Ok(node) => match checker.type_effect_of_exp(node) {
                Ok((ty, effect)) => {
                    let got = (
                        normalize(&checker.render_dexp(ty)),
                        normalize(&checker.render_dexp(effect)),
                    );
                    match &case.outcome {
                        Outcome::Typed { ty, effect } => {
                            let want = (normalize(ty), normalize(effect));
                            if got == want {
                                Verdict::Match
                            } else {
                                Verdict::Mismatch {
                                    expected: format!("{} ! {}", want.0, want.1),
                                    got: format!("{} ! {}", got.0, got.1),
                                }
                            }
                        }
                        Outcome::StaticError { message } => Verdict::Mismatch {
                            expected: format!("<error: {message}>"),
                            got: format!("{} ! {}", got.0, got.1),
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
    assert_eq!(
        report.matched.len(),
        182,
        "regression from full static conformance\n{}",
        report.detail(10)
    );
}

#[test]
fn values_match_the_reference() {
    let mut session = Fx91Session::new().expect("the fx module and runtime load");
    session.set_load_base(corpus_dir());
    let mut interner = std::mem::take(&mut session.checker.p.interner);
    let forms = read_forms(&mut interner);
    session.checker.p.interner = interner;

    let cases = cases();
    let mut report = Report::default();
    for (form, case) in forms.iter().zip(&cases) {
        let verdict = match session.run(form) {
            Err(e) => Verdict::Error { message: e.to_string() },
            Ok(outcome) => match (&outcome.value, case.expected_value()) {
                (Ok(got), Some(want)) => {
                    let (got, want) = (normalize_value(got), normalize_value(want));
                    if got == want {
                        Verdict::Match
                    } else {
                        Verdict::Mismatch { expected: want, got }
                    }
                }
                (Err(e), _) => Verdict::Error { message: format!("{e}\n    code: {}", outcome.code) },
                (Ok(got), None) => {
                    Verdict::Mismatch { expected: "<no golden>".into(), got: got.clone() }
                }
            },
        };
        report.record(case, verdict);
    }
    println!("{}", report.summary("fx91 value"));
    print!("{}", report.detail(10));

    // Full dynamic conformance: every form evaluates to the same value the
    // reference produces.
    assert_eq!(
        report.matched.len(),
        182,
        "regression from full value conformance\n{}",
        report.detail(10)
    );
}

/// Canonicalise a printed value.
///
/// A procedure's printed name is an artifact of how the host names closures —
/// the reference shows Racket source locations for anonymous ones — and says
/// nothing about FX-91 semantics, so any procedure prints the same way.
fn normalize_value(v: &str) -> String {
    let mut out = String::with_capacity(v.len());
    let mut rest = v;
    while let Some(i) = rest.find("#<procedure") {
        out.push_str(&rest[..i]);
        out.push_str("#<procedure>");
        match rest[i..].find('>') {
            Some(j) => rest = &rest[i + j + 1..],
            None => {
                rest = "";
                break;
            }
        }
    }
    out.push_str(rest);
    normalize(&out)
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
    let mut checker = Checker::new().expect("the fx module loads");

    fn parse(c: &mut Checker, text: &str) -> fixpt_fx91::FxId {
        let mut sources = SourceMap::new();
        let file = sources.add("<test>", text);
        let mut interner = std::mem::take(&mut c.p.interner);
        let form = Reader::new(text, file, SyntaxProfile::FX91, &mut interner)
            .read()
            .expect("reads")
            .expect("one form");
        c.p.interner = interner;
        let alpha = c.p.init_alpha;
        c.p.parse_dexp(alpha, &form).expect("parses")
    }

    // `unify-poly?` compares `(poly-body dexp1)` with itself, so two `poly`
    // types unify whenever arity and kinds agree — whatever their bodies say.
    // Intended: compare dexp1's body with dexp2's.
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
    assert!(
        !checker.description_leq(c, d).expect("no error"),
        "dlambda<=?'s self-recursion makes even equivalent dlambdas incomparable"
    );
}
