//! The in-REPL help facility.
//!
//! What each dialect can answer differs, and the difference is the interesting
//! part: Scheme knows arities, FX knows *types*, and only a language with types
//! can answer "I have one of these — what accepts it?".

use std::io::Write as _;
use std::process::{Command, Stdio};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

fn repl(dialect: Option<&str>, input: &str) -> String {
    repl_with(dialect, None, input)
}

/// The same, on a named engine. The two engines learn what is around a hole by
/// different means, so both are asked.
fn repl_engine(dialect: Option<&str>, engine: &str, input: &str) -> String {
    repl_with(dialect, Some(engine), input)
}

fn repl_with(dialect: Option<&str>, engine: Option<&str>, input: &str) -> String {
    let mut cmd = Command::new(FIXPT);
    if let Some(d) = dialect {
        cmd.args(["--dialect", d]);
    }
    if let Some(e) = engine {
        cmd.args(["--engine", e]);
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

// ------------------------------------------------ `,help` as a running program

/// The dynamic half of a hole, on both engines.
///
/// Scheme has no types, so evaluating up to the hole is the *only* way it can
/// say anything about a position — and what it says is made of values.
#[test]
fn scheme_answers_a_hole_with_values() {
    for engine in ["ast", "bytecode"] {
        let out = repl_engine(None, engine, "(vector-ref (make-vector 3 0) ,help)\n");
        assert!(out.contains("argument 2 of 2"), "{engine}:\n{out}");
        assert!(out.contains("vector-ref"), "{engine}:\n{out}");
        // The point: a *value*, not a type.
        assert!(out.contains("#(0 0 0)"), "{engine}:\n{out}");
    }
}

/// A hole the program never reaches is answered by saying so, not by inventing
/// a context that never existed.
#[test]
fn scheme_reports_a_hole_that_is_never_reached() {
    let out = repl(None, "(if #f ,help 7)\n");
    assert!(out.contains("never reached"), "{out}");
    assert!(out.contains('7'), "{out}");
}

/// Both engines answer, and they agree on the part they can both see.
///
/// They reach it differently: the AST machine reads its frame stack, while the
/// compiled one has no frame saying "argument 2 of 3" and segments its operand
/// stack using the position the reader recorded in the `%hole` call. Nested
/// calls are where a wrong segmentation shows up, so that is what is asked.
#[test]
fn both_engines_segment_nested_calls_the_same_way() {
    let src = "(define (f a b) (+ a b))\n(f 1 (f 2 ,help))\n";
    for engine in ["ast", "bytecode"] {
        let out = repl_engine(None, engine, src);
        assert!(out.contains("argument 2 of 2"), "{engine}:\n{out}");
        // The inner call's argument, not the outer one's: reporting `1` here
        // would mean the operand stack had been read as a single flat call.
        assert!(out.contains("argument 1 evaluated to 2"), "{engine}:\n{out}");
    }
}

/// A form that only *looks* like an application is not described as one.
///
/// `(b ,help)` in a `let` binding list reads exactly like a call, so the
/// reader's position is a guess. The run disproves it — nothing was pushed for
/// such a call — and the report follows the run.
#[test]
fn a_binding_clause_is_not_reported_as_a_call() {
    let out = repl(None, "(let ((a 1) (b ,help)) a)\n");
    assert!(
        out.contains("not an application") || out.contains("initialiser 2 of 2"),
        "{out}"
    );
}

/// FX keeps the static answer and gains the dynamic one.
#[test]
fn fx_answers_a_hole_both_ways() {
    for d in ["fx87", "fx91"] {
        let out = repl(Some(d), "(vector-ref (make-vector 3 0) ,help)\n");
        assert!(out.contains("the hole wants"), "{d} lost the static half:\n{out}");
        assert!(out.contains("int"), "{d}:\n{out}");
        assert!(out.contains("#(0 0 0)"), "{d} lost the dynamic half:\n{out}");
    }
}

/// The effect system licenses the speculation, and refuses it when it should.
///
/// Showing what an argument evaluates to means running it, which the user did
/// not ask for. That is only defensible when nothing can tell — so an argument
/// that may *write* is described rather than run. This is the assertion that
/// makes the gate a guarantee rather than a comment.
#[test]
fn fx_will_not_run_an_argument_that_writes() {
    let src = "(+ (begin (vector-set! (make-vector 1 0) 0 7) 5) ,help)\n";
    let out = repl(Some("fx91"), src);
    assert!(out.contains("not evaluated"), "the write gate did not fire:\n{out}");
    assert!(out.contains("write"), "{out}");
    // The pure operator beside it still is evaluated, so the refusal is about
    // the effect and not about having given up on the form.
    assert!(out.contains("the operator +"), "{out}");
}

// -------------------------------------------------------- holding a hole

/// In Scheme a hole is held, not just reported: `,resume` continues the form
/// from the hole with a value, and can do so again with another.
#[test]
fn scheme_resumes_a_hole_with_a_value_more_than_once() {
    for engine in ["ast", "bytecode"] {
        let out = repl_engine(
            None,
            engine,
            "(list 'got (vector-ref (vector 10 20 30) ,help))\n,resume 0\n,resume 2\n",
        );
        assert!(out.contains("(got 10)"), "{engine}:\n{out}");
        assert!(out.contains("(got 30)"), "{engine}:\n{out}");
    }
}

/// A value supplied to `,resume` may itself contain a hole; answering that one
/// finishes both.
#[test]
fn a_resumed_value_can_itself_ask() {
    let out = repl(
        None,
        "(list 'got (vector-ref (vector 10 20 30) ,help))\n,resume (+ 1 ,help)\n,resume 1\n",
    );
    assert!(out.contains("argument 1 evaluated to 1"), "{out}");
    assert!(out.contains("(got 30)"), "{out}");
}

#[test]
fn where_repeats_the_held_hole_and_says_when_there_is_none() {
    let out = repl(None, ",where\n(+ 1 ,help)\n,where\n");
    assert!(out.contains("no hole is held"), "{out}");
    assert_eq!(out.matches("argument 1 evaluated to 1").count(), 2, "{out}");
}

#[test]
fn only_scheme_advertises_resume() {
    assert!(repl(None, ",help\n").contains(",resume"));
    for d in ["fx87", "fx91"] {
        assert!(!repl(Some(d), ",help\n").contains(",resume"), "{d}");
    }
}

// ----------------------------------------------- `,help` before the form ends

/// `,help` written while the form is still open: the eager reader sees the
/// hole as the newest element of an open list, the REPL answers it as though
/// the form were closed there, and gives the form back — without the hole — to
/// carry on typing.
#[test]
fn a_hole_can_be_asked_about_before_the_form_is_finished() {
    let out = repl(None, "(define v (vector 10 20 30))\n(list 'got (vector-ref v ,help\n2))\n");
    assert!(out.contains("argument 1 evaluated to #(10 20 30)"), "{out}");
    assert!(out.contains("carry on typing"), "{out}");
    assert!(out.contains("(got 30)"), "{out}");
    // The form being typed is not the one that was closed off, so resuming
    // it is not offered.
    assert!(!out.contains("`,resume EXPR`"), "{out}");
}

/// In FX-26, `,apropos` looks in every namespace, labelling what it finds,
/// and `,apropos KIND TEXT` in one; `,help` shows each meaning of a name.
#[test]
fn fx26_apropos_searches_every_namespace() {
    let defs = include_str!("programs/apropos-namespaces.fx");
    let out = repl(Some("fx26"), &format!("{defs},apropos k\n"));
    for want in [
        "kstate = (maxeff (read @t) (write @t))  (an effect)",
        "kcell = (ref int @t)  (a type)",
        "(kbox (t type)) = (pairof t t finite)  (a type family)",
        "(kid (t type +)) = (pairof t int finite)  (a generative type)",
        "kval : int",
    ] {
        assert!(out.contains(want), "no `{want}` in:\n{out}");
    }
    // What `,apropos` finds is the indented lines; the rest echoes the
    // definitions.
    let out = repl(Some("fx26"), &format!("{defs},apropos effect k\n"));
    let found: Vec<&str> = out.lines().filter_map(|l| l.split("fx26> ").last()).filter(|l| l.starts_with("  ")).collect();
    assert_eq!(found, ["  kstate = (maxeff (read @t) (write @t))  (an effect)"], "{out}");
    let out = repl(Some("fx26"), &format!("{defs},help kid\n"));
    assert!(out.contains("(kid (t type +)) = (pairof t int finite)  (a generative type)"), "{out}");
}
