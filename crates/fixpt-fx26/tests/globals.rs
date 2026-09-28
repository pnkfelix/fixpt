//! Globals as a region: naming a global reads its binding, `(read (globals
//! g))`, within `(read @globals)`; `define*` finds what a procedure reads.
//! Checked with `globals_effects` on, as the language will be once every
//! program says what it reads.

use fixpt_fx26::{Checker, Top};
use fixpt_read::FileId;

/// Each form of the program, checked in turn: a definition's name and
/// type, an expression's type and effect, or the error.
fn check(name: &str) -> Vec<String> {
    let text = std::fs::read_to_string(format!("{}/tests/programs/globals/{name}.fx", env!("CARGO_MANIFEST_DIR"))).unwrap();
    let mut c = Checker::new();
    c.globals_effects = true;
    let forms = c.read_in(FileId(0), &text).expect("reads");
    forms
        .iter()
        .map(|f| match c.top(f) {
            Ok(Top::Define { name, ty, .. }) => format!("{} : {}", c.interner.name(name), c.show_ty(ty)),
            Ok(Top::Exp(k)) => format!("{} ! {}", c.show_ty(k.ty), c.show_effect(&k.effect)),
            Ok(other) => format!("{other:?}"),
            Err(e) => format!("error: {}", e.message),
        })
        .collect()
}

#[test]
fn define_star_finds_what_a_procedure_reads() {
    let out = check("inferred");
    assert_eq!(out[1], "below : (subr (read (globals limit)) (int) bool)", "{out:?}");
    assert_eq!(out[2], "clamp : (subr (read (globals below limit)) (int) int)", "{out:?}");
    assert_eq!(out[3], "count : (subr (maxeff spin (read (globals below count limit))) (int) int)", "{out:?}");
    assert_eq!(out[4], "int ! (read (globals below clamp limit))", "{out:?}");
}

#[test]
fn define_says_what_it_reads_or_is_refused() {
    let out = check("written");
    assert_eq!(out[1], "below : (subr (read (globals limit)) (int) bool)", "{out:?}");
    assert_eq!(out[2], "clamp : (subr (read @globals) (int) int)", "{out:?}");
    assert!(out[3].starts_with("error:") && out[3].contains("globals"), "{out:?}");
}

#[test]
fn effect_polymorphism_carries_what_an_argument_reads() {
    let out = check("polymorphic");
    assert_eq!(out[3], "bool ! (read (globals below limit twice))", "{out:?}");
    assert_eq!(out[4], "bool ! (read (globals twice))", "{out:?}");
}

#[test]
fn globals_are_a_region_only_in_effects() {
    let out = check("only-effects");
    assert!(out[0].contains("only in effects"), "{out:?}");
    assert!(out[1].contains("only read and written"), "{out:?}");
}
