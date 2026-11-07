//! `validate` (`docs/research/loads-and-places.md`, "Decided: three keys"):
//! the cheap keys checked against the full one as the walk gives them
//! (`parser-ids.fx`'s `validated!`), and each full key's facts against
//! those it had before (`compile-facts.fx`'s `c-validate-facts!`). A
//! process of its own, so that it can be made to validate
//! (`ids::set_mode`) before anything asks the mode.

mod common;

use fixpt_fx26::ids::{Mode, set_mode};
use fixpt_heap::Value;
use fixpt_read::FileId;

fn validating() {
    assert!(set_mode(Mode::Validate), "the mode was asked before");
}

/// A cheap key given again with another full key is said: `path`'s, here,
/// recorded as the walk records it.
#[test]
fn a_cheap_key_given_twice_is_said() {
    validating();
    let mut s = common::session();
    let said = s.run_program(include_str!("validate/key-given-twice.fx")).expect("runs").expect("checks");
    assert!(said.contains("validate: the `path` key (5 0) was given another expression before"), "{said}");
}

/// A full key handed to the compiler again with other facts is the
/// compiler's error: here, one summary and then another, of one key.
#[test]
fn a_key_with_other_facts_is_refused() {
    validating();
    let mut s = common::front_end_session();
    let facts = |s: &mut fixpt_scheme::Session, summary: i64| {
        s.make(|m| {
            let h = m.heap();
            let product = fixpt_heap::layout::kind("product");
            let at = h.make_frozen(product, &[Value::fixnum(0), Value::fixnum(1), Value::fixnum(12345), Value::fixnum(678)]);
            let fields = h.make_frozen(product, &[Value::fixnum(summary)]);
            let name = h.intern("n-summary");
            let noted = h.make_frozen(fixpt_heap::layout::kind("sum"), &[name, fields]);
            let fact = h.make_frozen(product, &[at, noted]);
            h.cons(fact, Value::NULL)
        })
    };
    let made = s.scheme.scope(|sc| {
        let first = facts(sc, 1);
        let once = fixpt_fx26::syn::compile_to_word(sc, FileId(0), "(+ 1 2)\n", first).expect("parses");
        let other = facts(sc, 2);
        let again = fixpt_fx26::syn::compile_to_word(sc, FileId(0), "(+ 1 2)\n", other).expect("parses");
        (once.is_ok(), again.err())
    });
    assert!(made.0, "the first handoff is the key's first");
    let why = made.1.expect("refused");
    assert!(why.contains("validate: the full key (12345 678) has other facts"), "{why}");
}

/// Every test program, compiled one after another by one front end: no key
/// given twice, and each full key met again, in one program or another,
/// with the facts it had.
#[test]
fn every_program_compiles_under_validate() {
    validating();
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut said = Vec::new();
    let mut ran = 0;
    for sub in ["bidirectional", "control", "run", "pldi89", "bloblet", "datum", "modules", "higher-kinds", "processes"] {
        let mut names: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
        names.sort();
        for path in names {
            let program = std::fs::read_to_string(&path).unwrap();
            let out = common::with_own(|s| s.compile_with_own_compiler(&program)).map_err(|e| e.to_string());
            ran += 1;
            let text = match &out {
                Ok(v) => v.clone(),
                Err(e) => e.clone(),
            };
            if text.contains("validate:") {
                said.push(format!("{sub}/{}: {text}", path.file_name().unwrap().to_string_lossy()));
            }
        }
    }
    assert!(said.is_empty(), "{} of {ran}:\n{}", said.len(), said.join("\n"));
    assert!(ran >= 15, "only {ran} programs");
}

/// A definition checked again after a name it uses was redefined is read
/// again first, its keys new (`k-rerun`, `read-again`): what that check
/// finds is not taken for what the first check of it found. Before, the
/// two checks' facts met under one key, and `validate` refused the
/// redefinition's compile.
#[test]
fn a_definition_checked_again_is_read_again() {
    validating();
    let mut s = fixpt_fx26::session::Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).expect("starts");
    s.strategy = fixpt_fx26::session::Strategy::Cellular;
    let mut run = |text: &str| -> Vec<String> {
        let forms = s.checker.read_in(FileId(0), text).expect("reads");
        forms.iter().map(|f| s.run(f).map(|o| format!("{}{}", o.printed, o.value.map(|v| v.unwrap_or_default()).unwrap_or_default())).unwrap_or_else(|e| e.message)).collect()
    };
    run(include_str!("programs/redefine/compatible.fx"));
    let out = run(include_str!("validate/redefine-again.fx"));
    assert!(!out[0].contains("validate:"), "{out:?}");
    assert_eq!(out[2], "3", "{out:?}");
}
