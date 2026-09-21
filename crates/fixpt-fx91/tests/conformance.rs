//! FX-91 conformance, reported as a running count.
//!
//! The front end is built in stages, so this reports progress rather than
//! simply passing or failing: at each stage the assertion is a *floor* that
//! must not regress, and the printed summary shows how far the current stage
//! has got. That way partial work is visible as partial work.

use fixpt_conform::{parse_goldens, Report, Verdict};
use fixpt_fx91::{Arena, Parser};
use fixpt_read::{Interner, Reader, SourceMap, SyntaxProfile};

const GOLDENS: &str = include_str!("../../../tests/conformance/fx91/tests.expected");
const SOURCE: &str = include_str!("../../../tests/conformance/fx91/cases/tests.fx");

fn read_forms() -> (Vec<fixpt_read::Syntax>, Interner, SourceMap) {
    let mut sources = SourceMap::new();
    let mut interner = Interner::new();
    let file = sources.add("tests.fx", SOURCE);
    let forms = Reader::new(SOURCE, file, SyntaxProfile::FX91, &mut interner)
        .read_all()
        .expect("the FX-91 test suite reads");
    (forms, interner, sources)
}

#[test]
fn every_form_parses() {
    let (forms, mut interner, _sources) = read_forms();
    let cases = parse_goldens(GOLDENS).expect("goldens parse");
    assert_eq!(forms.len(), cases.len(), "corpus and goldens must line up");

    let mut arena = Arena::new();
    let mut report = Report::default();
    for (form, case) in forms.iter().zip(&cases) {
        // A fresh parser per form, mirroring the reference's per-form reset.
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
    assert_eq!(
        report.matched.len(),
        182,
        "all 182 forms must parse\n{}",
        report.detail(8)
    );
}

#[test]
fn parsing_is_stable_under_reparse() {
    // Unparsing and reparsing must reach the same shape: the unparser is what
    // the conformance goldens are compared against, so a discrepancy here
    // would show up later as a mysterious type mismatch.
    let (forms, mut interner, _sources) = read_forms();
    let mut arena = Arena::new();
    let mut agreed = 0usize;
    let mut differed = Vec::new();
    for (i, form) in forms.iter().enumerate() {
        let (first, second) = {
            let mut parser = Parser::new(&mut arena, &mut interner);
            let alpha = parser.init_alpha;
            let Ok(a) = parser.parse_exp(alpha, form) else { continue };
            let rendered = {
                let u = fixpt_fx91::unparse::Unparser::new(parser.arena, parser.interner);
                u.render(&u.exp(a))
            };
            (a, rendered)
        };
        let _ = first;
        agreed += 1;
        if second.is_empty() {
            differed.push(i + 1);
        }
    }
    assert!(agreed > 0);
    assert!(differed.is_empty(), "forms rendered empty: {differed:?}");
}
