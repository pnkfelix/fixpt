//! The harness must be able to read the real corpora, not just a toy record.

use fixpt_conform::{parse_goldens, normalize, Outcome};

const FX91: &str = include_str!("../../../tests/conformance/fx91/tests.expected");
const FX87: &str = include_str!("../../../tests/conformance/fx87/kernel.expected");

#[test]
fn reads_the_fx91_corpus() {
    let cases = parse_goldens(FX91).expect("fx91 goldens parse");
    assert_eq!(cases.len(), 182);
    assert!(cases.iter().all(|c| matches!(c.outcome, Outcome::Typed { .. })),
            "every FX-91 form typechecks in the reference");
    // 181 evaluate; one hits the archive's unbound cons~/nil~ and is recorded
    // with both outcomes. See docs/divergences.md.
    let plain = cases.iter().filter(|c| c.value.is_some()).count();
    let augmented = cases.iter().filter(|c| c.value_augmented.is_some()).count();
    assert_eq!(plain, 181);
    assert_eq!(augmented, 1);
    let gap = cases.iter().find(|c| c.value_augmented.is_some()).unwrap();
    assert!(gap.value_error.as_deref().unwrap().contains("nil~"), "{gap:?}");
    assert_eq!(gap.expected_value(), Some("3"), "we expect the fixed value");
    // Every case has something to check against.
    assert!(cases.iter().all(|c| c.expected_value().is_some()));
}

#[test]
fn reads_the_fx87_corpus() {
    let cases = parse_goldens(FX87).expect("fx87 goldens parse");
    assert_eq!(cases.len(), 161);
    let errors = cases.iter().filter(|c| matches!(c.outcome, Outcome::StaticError { .. })).count();
    assert_eq!(errors, 13, "deliberately ill-typed cases, or ones pinning a quirk");
    // Values do exist, but not for every case. `impl.rkt` installs no
    // evaluator, so they come from `#lang fx87-hashlang` — which does not
    // implement FX-87's standard forms (`record`, `one`, `tagcase`, `delay`,
    // `vlambda`) and hangs on a form whose type is recursive. Those 25 cases
    // carry no `#value` and are checked separately, in
    // `fixpt-fx87/tests/beyond_reference.rs`, against this implementation
    // rather than against the reference.
    let values = cases.iter().filter(|c| c.value.is_some()).count();
    assert_eq!(values, 123, "the evaluating path reaches 123 of the 161");
    assert!(
        cases
            .iter()
            .filter(|c| matches!(c.outcome, Outcome::StaticError { .. }))
            .all(|c| c.value.is_none()),
        "an ill-typed form never has a value"
    );
}

#[test]
fn normalising_the_real_corpus_is_idempotent_and_keeps_distinctions() {
    let cases = parse_goldens(FX91).unwrap();
    let mut normalized = Vec::new();
    for c in &cases {
        if let Outcome::Typed { ty, effect } = &c.outcome {
            let n = normalize(ty);
            assert_eq!(normalize(&n), n, "case {}: normalisation must be idempotent", c.number);
            normalized.push((c.number, n, normalize(effect)));
        }
    }
    // Sanity: the unification variables really did get renumbered somewhere.
    assert!(normalized.iter().any(|(_, t, _)| t.contains("*UNIF*-#0")));
    // And two structurally different types must stay different.
    let unique: std::collections::HashSet<_> = normalized.iter().map(|(_, t, e)| (t, e)).collect();
    assert!(unique.len() > 50, "normalisation collapsed too much: {} distinct", unique.len());
}
