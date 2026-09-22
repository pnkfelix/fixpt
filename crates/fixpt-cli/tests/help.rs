//! The in-REPL help facility.
//!
//! What each dialect can answer differs, and the difference is the interesting
//! part: Scheme knows arities, FX knows *types*, and only a language with types
//! can answer "I have one of these — what accepts it?".

use std::io::Write as _;
use std::process::{Command, Stdio};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

fn repl(dialect: Option<&str>, input: &str) -> String {
    let mut cmd = Command::new(FIXPT);
    if let Some(d) = dialect {
        cmd.args(["--dialect", d]);
    }
    let mut child = cmd
        .arg("repl")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("fixpt starts");
    child.stdin.take().expect("piped").write_all(input.as_bytes()).expect("writes");
    let out = child.wait_with_output().expect("finishes");
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn every_dialect_lists_its_commands() {
    for d in [None, Some("fx87"), Some("fx91")] {
        let out = repl(d, ",help\n");
        assert!(out.contains(",apropos"), "{d:?} has no overview:\n{out}");
        assert!(out.contains(",fits"), "{d:?}:\n{out}");
    }
}

#[test]
fn scheme_reports_arities() {
    let out = repl(None, ",help vector-ref\n,help map\n");
    assert!(out.contains("a primitive, 2 argument(s)"), "{out}");
    assert!(out.contains("2 or more arguments"), "{out}");
}

#[test]
fn apropos_finds_names_in_every_dialect() {
    assert!(repl(None, ",apropos string->\n").contains("string->number"));
    assert!(repl(Some("fx87"), ",apropos vector\n").contains("vector-ref"));
    assert!(repl(Some("fx91"), ",apropos stream\n").contains("open-input-stream"));
}

/// The question a REPL usually cannot answer.
#[test]
fn fx87_finds_what_accepts_a_type() {
    let out = repl(Some("fx87"), ",fits (pairof int bool @=)\n");
    // The pair operations, found by matching a polymorphic formal against the
    // query — nobody had to instantiate `car` first.
    for name in ["car", "cdr", "set-car!", "set-cdr!"] {
        assert!(out.contains(&format!("{name} :")), "{name} missing:\n{out}");
    }
    // And not things that take something else.
    assert!(!out.contains("string-length :"), "{out}");
}

#[test]
fn fx87_finds_what_produces_a_type() {
    let out = repl(Some("fx87"), ",returns bool\n");
    for name in ["not?", "and?", "symbol=?"] {
        assert!(out.contains(&format!("{name} :")), "{name} missing:\n{out}");
    }
}

/// A binding whose result is a bare type variable matches *every* query, so it
/// is counted rather than listed — otherwise `caaaar` buries the answer.
#[test]
fn universally_applicable_bindings_are_summarised_not_listed() {
    let out = repl(Some("fx87"), ",returns bool\n");
    assert!(out.contains("more that fit anything"), "no summary line:\n{out}");
    // `car` really can produce a bool, but listing it here is noise.
    assert!(
        !out.contains("\n  car :"),
        "a universally-matching binding should not be listed inline:\n{out}"
    );
}

/// A dialect that cannot answer says so, rather than returning nothing —
/// "no results" and "I cannot ask that" are different.
#[test]
fn a_dialect_without_types_declines_rather_than_finding_nothing() {
    let out = repl(None, ",fits int\n");
    assert!(out.contains("cannot answer"), "{out}");
    assert!(out.contains("fx87"), "it should say where the answer lives:\n{out}");
}

#[test]
fn an_unknown_name_is_reported_as_such() {
    for d in [None, Some("fx87"), Some("fx91")] {
        let out = repl(d, ",help definitely-not-bound\n");
        assert!(out.contains("nothing named"), "{d:?}:\n{out}");
    }
}

/// A line that merely starts with a comma is still a program if it is not a
/// command — `,x` is unquote-splicing's cousin and must not be swallowed.
#[test]
fn only_real_commands_are_intercepted() {
    let out = repl(None, "(define x 5)\n`(1 ,x)\n");
    assert!(out.contains("(1 5)"), "unquote was swallowed:\n{out}");
}

/// `,help` written *inside* a form asks about that position rather than about
/// the whole expression.
#[test]
fn a_hole_reports_what_belongs_in_it() {
    // The first argument pins the element type, so the *second* is an index.
    let out = repl(Some("fx87"), "(vector-ref (make-vector 3 0) ,help)\n");
    assert!(out.contains("the hole wants: int"), "{out}");
    // And it goes on to say what produces one.
    assert!(out.contains("string-length :"), "{out}");
}

#[test]
fn an_unconstrained_hole_says_so_rather_than_guessing() {
    // `car` constrains its argument only to be some pair, and the answer
    // reports exactly that rather than inventing a type.
    let out = repl(Some("fx87"), "(car ,help)\n");
    assert!(out.contains("(pairof t1 t2 r)"), "{out}");
}

/// A hole in operator position asks the other question: what can be applied to
/// the arguments that are written?
#[test]
fn a_hole_in_operator_position_searches_by_argument() {
    let out = repl(Some("fx87"), "(,help (cons 1 2))\n");
    assert!(out.contains("applied to a (pairof int int @=)"), "{out}");
    for name in ["car", "cdr", "set-car!"] {
        assert!(out.contains(&format!("{name} :")), "{name} missing:\n{out}");
    }
}

/// A form with no hole is still a program.
#[test]
fn a_form_without_a_hole_is_evaluated_normally() {
    let out = repl(Some("fx87"), "(+ 1 2)\n");
    assert!(out.contains("3 : int ! pure"), "{out}");
    assert!(!out.contains("the hole"), "{out}");
}

/// The overview must describe what the dialect can actually do.
///
/// It used to list `,fits` everywhere, including in the two dialects that
/// decline it — a menu advertising a dish the kitchen does not serve.
#[test]
fn the_overview_advertises_only_what_works() {
    let fx87 = repl(Some("fx87"), ",help\n");
    assert!(fx87.contains(",fits TYPE"), "FX-87 can search by type:\n{fx87}");
    assert!(fx87.contains("inside a form"), "and answer holes:\n{fx87}");

    for d in [None, Some("fx91")] {
        let out = repl(d, ",help\n");
        assert!(!out.contains(",fits TYPE "), "{d:?} cannot do this:\n{out}");
        assert!(
            out.contains("which `--dialect fx87` has"),
            "{d:?} should say where it lives:\n{out}"
        );
    }
}

/// FX-91 answers a hole too, and answers it about *its own* language.
///
/// The two dialects disagree about `car`: FX-87's takes a pair, FX-91's takes a
/// list. Help that reported a shared approximation would be wrong for both.
#[test]
fn fx91_answers_a_hole_about_its_own_types() {
    let out = repl(Some("fx91"), "(vector-ref (make-vector 3 0) ,help)\n");
    assert!(out.contains("the hole wants: int"), "{out}");
    assert!(!out.contains("unbound value variable unquote"), "raw error leaked:\n{out}");

    let fx91 = repl(Some("fx91"), "(car ,help)\n");
    assert!(fx91.contains("(listof t)"), "FX-91's car takes a list:\n{fx91}");
    let fx87 = repl(Some("fx87"), "(car ,help)\n");
    assert!(fx87.contains("(pairof t1 t2 r)"), "FX-87's takes a pair:\n{fx87}");
}

/// What FX-91 *cannot* do is the second half — listing what produces the type —
/// and it declines exactly that rather than the whole question.
#[test]
fn fx91_declines_only_the_half_it_cannot_do() {
    let out = repl(Some("fx91"), "(cons 1 ,help)\n");
    assert!(out.contains("the hole wants:"), "the first half works:\n{out}");
    assert!(out.contains("cannot yet list what produces one"), "{out}");
}

/// …and `,help` in a *string* is not a hole.
#[test]
fn a_comma_help_inside_a_string_is_just_text() {
    let out = repl(Some("fx91"), "\",help\"\n");
    assert!(!out.contains("searched by name"), "text was mistaken for a hole:\n{out}");
}
