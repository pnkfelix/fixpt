//! `fixpt test`'s runner (`fixpt_fx26::spec_tests`) over the specification
//! programs: a counterexample found for each that is false, and none for
//! the rest, so that a specification left open by the verifier because it
//! is false (`wrong-ensures.fx`) is told from one left open because it is
//! beyond the prover (`square.fx`). Those the checker refuses are not run.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

/// The programs a counterexample shows false.
const FALSE: [&str; 4] = ["harness-insert-wrong.fx", "logic-harness-wrong.fx", "wrong-ensures.fx", "wrong-requires.fx"];

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

/// With an SMT solver (`fixpt_fx26::smt`; skipped without one), each VC the
/// verifier leaves open sorted (S2 of the note, its §8): `x * x ≥ 0`
/// proved; a specification shown false only of a program that is
/// (`FALSE`), and of those where a counterexample to the VC is one to the
/// program; the harness, true, not inductive, the call the proof took to
/// give what it does not named.
#[test]
fn open_obligations_sorted_by_a_solver() {
    if fixpt_fx26::smt::solver().is_none() {
        eprintln!("no SMT solver: skipped");
        return;
    }
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/specs");
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    let mut said = std::collections::BTreeMap::new();
    for p in names {
        let text = std::fs::read_to_string(&p).unwrap();
        if text.starts_with("; Refused") {
            continue;
        }
        let name = p.file_name().unwrap().to_string_lossy().into_owned();
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        let (lines, _) = fixpt_fx26::verifying::report(&mut s.scheme, &text, Some(&name), Some(dir.into()), &[]).unwrap_or_else(|e| panic!("{name}: {e}"));
        said.insert(name, lines.join("\n"));
    }
    for (name, lines) in &said {
        assert!(!lines.contains(": false: ") || FALSE.contains(&name.as_str()), "{name} said false:\n{lines}");
    }
    let has = |name: &str, what: &str| said[name].contains(what);
    assert!(has("square.fx", "`square`: verified") && has("square.fx", "by the SMT solver"), "{}", said["square.fx"]);
    assert!(has("wrong-ensures.fx", "at wrong-ensures.fx:5:27, `x`: the ensures: false: with x = -1, the result is -1"), "{}", said["wrong-ensures.fx"]);
    assert!(has("wrong-requires.fx", "`(clamp x 0 5)`: the callee's requires: false: with x = 1, the requires of clamp does not hold"), "{}", said["wrong-requires.fx"]);
    let insert = "at harness-insert.fx:20:47, `(assert (sorted? (insert e xs)))`: `assert`'s requires: not proved, as the proof knows too little of a call. It holds for e = 0, xs = (the ints nil); but for all the proof knows, (sorted? (insert 0 (the ints nil))) could be #f, where it is #t.";
    assert!(has("harness-insert.fx", insert), "{}", said["harness-insert.fx"]);
    // Logic functions, defined for the solver (`smt_theory`): `insert`'s
    // inductive `ensures` proved; the one too weak to be, the recursive
    // call's value named; the wrong `insert` false, of lists the solver
    // found.
    assert!(has("logic-insert.fx", "`insert`: verified") && has("logic-insert.fx", "by the SMT solver"), "{}", said["logic-insert.fx"]);
    let weak = "not proved, as the proof knows too little of a call. It holds for e = ";
    assert!(has("logic-harness.fx", weak) && has("logic-harness.fx", "but for all the proof knows, (insert "), "{}", said["logic-harness.fx"]);
    assert!(has("logic-harness-wrong.fx", "the ensures: false: with e = ") && has("logic-harness-wrong.fx", "xs = (the ints (list "), "{}", said["logic-harness-wrong.fx"]);
}
