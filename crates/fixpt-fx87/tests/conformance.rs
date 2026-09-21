//! FX-87 conformance, reported as a running count.
//!
//! The same methodology as FX-91: a floor that must not regress, and a printed
//! summary so progress is visible while the checker is being built. Levels are
//! added as they start passing — parse first, then type and effect.
//!
//! The corpus is read with the parser's own interner. A `Sym` is an index into
//! one specific table, so a form read against another means nothing here.

use fixpt_conform::{normalize, parse_goldens, Case, Outcome, Report, Verdict};
use fixpt_fx87::check::Checker;
use fixpt_fx87::Fx87Session;
use fixpt_fx87::unparse::unparse;
use fixpt_fx87::Parser;
use fixpt_read::{Interner, Reader, SourceMap, Syntax, SyntaxProfile};

const GOLDENS: &str = include_str!("../../../tests/conformance/fx87/kernel.expected");
const SOURCE: &str = include_str!("../../../tests/conformance/fx87/cases/kernel.fx");

fn cases() -> Vec<Case> {
    parse_goldens(GOLDENS).expect("goldens parse")
}

fn read_forms(interner: &mut Interner) -> Vec<Syntax> {
    let mut sources = SourceMap::new();
    let file = sources.add("kernel.fx", SOURCE);
    Reader::new(SOURCE, file, SyntaxProfile::FX87, interner)
        .read_all()
        .expect("the FX-87 corpus reads")
}

#[test]
fn the_corpus_and_the_goldens_line_up() {
    let mut interner = Interner::new();
    let forms = read_forms(&mut interner);
    let cases = cases();
    assert_eq!(forms.len(), cases.len(), "one golden per form");
    assert_eq!(cases.len(), 155, "the corpus is 155 forms");
}

/// Every form in the corpus reaches the abstract syntax.
///
/// The floor rises as the parser grows; it must never fall. A form that fails
/// here cannot be type-checked at all, so this is the level everything else
/// sits on.
#[test]
fn forms_parse() {
    let mut parser = Parser::new();
    let mut interner = std::mem::take(&mut parser.interner);
    let forms = read_forms(&mut interner);
    parser.interner = interner;

    let cases = cases();
    let mut report = Report::default();
    for (form, case) in forms.iter().zip(&cases) {
        let verdict = match parser.parse_exp(form, &Default::default()) {
            Ok(_) => Verdict::Match,
            Err(e) => Verdict::Error { message: e.to_string() },
        };
        report.record(case, verdict);
    }
    println!("{}", report.summary("fx87 parse"));
    print!("{}", report.detail(12));

    const FLOOR: usize = 155;
    assert!(
        report.matched.len() >= FLOOR,
        "fx87 parse regressed below {FLOOR}\n{}",
        report.detail(12)
    );
}

/// Type and effect against the reference.
///
/// The floor rises as the checker grows and must never fall. A case counts only
/// when *both* the type and the effect match — reporting the right type with
/// the wrong effect would miss the entire point of the language.
#[test]
fn types_and_effects_match_the_reference() {
    let mut checker = Checker::new().expect("the standard environment loads");
    let mut interner = std::mem::take(&mut checker.p.interner);
    let forms = read_forms(&mut interner);
    checker.p.interner = interner;

    let cases = cases();
    let mut report = Report::default();
    for (form, case) in forms.iter().zip(&cases) {
        let env = checker.env.clone();
        let verdict = match checker.p.parse_exp(form, &Default::default()) {
            Err(e) => Verdict::Error { message: format!("parse: {e}") },
            Ok(exp) => match checker.check(exp, &env) {
                Ok(d) => {
                    let got = (
                        normalize(&unparse(&checker.p.arena, &checker.p.interner, d.ty)),
                        normalize(&unparse(&checker.p.arena, &checker.p.interner, d.effect)),
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
                Err(e) => match &case.outcome {
                    // The reference reports every checking failure the same
                    // way, so matching the message is part of conformance.
                    Outcome::StaticError { message } if e.to_string() == *message => {
                        Verdict::Match
                    }
                    Outcome::StaticError { message } => Verdict::Mismatch {
                        expected: message.clone(),
                        got: e.to_string(),
                    },
                    Outcome::Typed { .. } => Verdict::Error { message: e.to_string() },
                },
            },
        };
        report.record(case, verdict);
    }
    println!("{}", report.summary("fx87 type/effect"));
    print!("{}", report.detail(14));

    const FLOOR: usize = 154;
    assert!(
        report.matched.len() >= FLOOR,
        "fx87 type/effect regressed below {FLOOR}\n{}",
        report.detail(14)
    );
}


/// Canonicalise a printed value.
///
/// The goldens come from Racket, this engine prints its own way, and a few
/// shapes differ without anything about FX-87 differing:
///
/// * a procedure's printed name carries the temporary file it was compiled
///   from, which is not even stable between runs of the generator;
/// * Racket writes a box `#&3` where this prints `#<box 3>`;
/// * Racket's `#<void>` is this engine's unspecified value;
/// * FX-87's unit is the symbol `#u`, which Racket `write`s with bars.
///
/// Everything else is compared literally.
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
    let out = out
        .replace("#<void>", "#<unspecified>")
        .replace("|#u|", "#u");
    // `#&x` and `#<box x>` are the same box.
    let out = if let Some(i) = out.find("#&") {
        format!("{}#<box {}>", &out[..i], &out[i + 2..])
    } else {
        out
    };
    normalize(&out)
}

/// Values, against the archive's evaluating path.
///
/// The stronger of the two levels, and the reason it was worth generating:
/// static conformance exercises the checker, while this exercises erasure, the
/// run-time representations those types were hiding, and the Scheme engine
/// underneath. The goldens come from `#lang fx87-hashlang` rather than from
/// `impl.rkt`, whose driver installs no evaluator at all — so a value here is
/// evidence about the language rather than a restatement of its type.
#[test]
fn values_match_the_reference() {
    let mut session = Fx87Session::new().expect("the standard environment and runtime load");
    let mut interner = std::mem::take(&mut session.checker.p.interner);
    let forms = read_forms(&mut interner);
    session.checker.p.interner = interner;

    let cases = cases();
    let mut report = Report::default();
    for (form, case) in forms.iter().zip(&cases) {
        let verdict = match session.run(form) {
            Err(e) => match case.expected_value() {
                // A case with no dynamic golden cannot fail here.
                None => Verdict::Unsupported { reason: "no value golden".into() },
                Some(_) => Verdict::Error { message: e.to_string() },
            },
            Ok(outcome) => match (&outcome.value, case.expected_value()) {
                (_, None) => Verdict::Unsupported { reason: "no value golden".into() },
                (Ok(got), Some(want)) => {
                    let (got, want) = (normalize_value(got), normalize_value(want));
                    if got == want {
                        Verdict::Match
                    } else {
                        Verdict::Mismatch { expected: want, got }
                    }
                }
                (Err(e), Some(_)) => {
                    Verdict::Error { message: format!("{e}\n    code: {}", outcome.code) }
                }
            },
        };
        report.record(case, verdict);
    }
    println!("{}", report.summary("fx87 value"));
    print!("{}", report.detail(14));

    const FLOOR: usize = 120;
    assert!(
        report.matched.len() >= FLOOR,
        "fx87 value regressed below {FLOOR}\n{}",
        report.detail(14)
    );
}
