//! FX-87 conformance, reported as a running count.
//!
//! The same methodology as FX-91: a floor that must not regress, and a printed
//! summary so progress is visible while the checker is being built. Levels are
//! added as they start passing — parse first, then type and effect.
//!
//! The corpus is read with the parser's own interner. A `Sym` is an index into
//! one specific table, so a form read against another means nothing here.

use fixpt_conform::{normalize, parse_goldens, Case, Outcome, Report, Verdict};
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

/// Keeps `Outcome` and `normalize` referenced while the type level is built.
#[allow(dead_code)]
fn _will_be_used(case: &Case) -> Option<String> {
    match &case.outcome {
        Outcome::Typed { ty, .. } => Some(normalize(ty)),
        Outcome::StaticError { .. } => None,
    }
}
