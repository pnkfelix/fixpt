//! `fixpt test`'s runner (`fixpt_fx26::spec_tests`) over the specification
//! programs: a counterexample found for each that is false, and none for
//! the rest, so that a specification left open by the verifier because it
//! is false (`wrong-ensures.fx`) is told from one left open because it is
//! beyond the prover (`square.fx`). Those the checker refuses are not run.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

/// The programs a counterexample shows false.
const FALSE: [&str; 3] = ["harness-insert-wrong.fx", "wrong-ensures.fx", "wrong-requires.fx"];

#[test]
fn specifications_tested_by_running() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/specs");
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    let mut wrong = Vec::new();
    for p in names {
        let text = std::fs::read_to_string(&p).unwrap();
        if text.starts_with("; Refused") {
            continue;
        }
        let name = p.file_name().unwrap().to_string_lossy().into_owned();
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        let tested = fixpt_fx26::spec_tests::test_program(&mut s, &text, 100).unwrap_or_else(|e| panic!("{name}: {e}"));
        let found: Vec<String> = tested.iter().filter_map(|t| t.counterexample.as_ref().map(|c| format!("{}: {c}", t.name))).collect();
        eprintln!("{name}: {} tested, {}", tested.len(), if found.is_empty() { "no counterexample".to_string() } else { found.join("; ") });
        if found.is_empty() == FALSE.contains(&name.as_str()) {
            wrong.push(name);
        }
    }
    assert!(wrong.is_empty(), "counterexamples not as expected: {wrong:?}");
}
