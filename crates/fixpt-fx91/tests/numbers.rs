//! Numbers beyond the reference corpus.

use fixpt_fx91::Fx91Session;
use fixpt_read::{Reader, SourceMap, SyntaxProfile};

fn run(session: &mut Fx91Session, text: &str) -> String {
    let mut sources = SourceMap::new();
    let file = sources.add("<t>", text);
    let mut interner = std::mem::take(&mut session.checker.p.interner);
    let forms = Reader::new(text, file, SyntaxProfile::FX91, &mut interner).read_all().expect("reads");
    session.checker.p.interner = interner;
    let outcome = session.run(&forms[0]).unwrap_or_else(|e| panic!("{e}\n  in: {text}"));
    match outcome.value {
        Ok(v) => v,
        Err(e) => panic!("{e}\n  in: {text}"),
    }
}

/// `floor` and its kin are typed `(float) int`, so they give an exact
/// integer, usable as an index: not Scheme's inexact 2.0.
#[test]
fn rounding_gives_an_exact_int() {
    for backend in [fixpt_engine::Backend::Ast, fixpt_engine::Backend::Bytecode] {
        let mut s = Fx91Session::with_backend(backend).expect("starts");
        assert_eq!(run(&mut s, "(floor 2.3)"), "2", "{backend:?}");
        assert_eq!(run(&mut s, "(ceiling 2.3)"), "3", "{backend:?}");
        assert_eq!(run(&mut s, "(truncate -2.7)"), "-2", "{backend:?}");
        assert_eq!(run(&mut s, "(round 2.5)"), "2", "{backend:?}");
    }
}
