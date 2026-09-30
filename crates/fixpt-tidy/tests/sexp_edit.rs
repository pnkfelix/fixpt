//! `sexp-edit`'s edits (`fixpt_tidy::sexp_edit`), on a small FX-26 file.

use fixpt_read::SyntaxProfile;
use fixpt_tidy::sexp_edit as se;

const SAMPLE: &str = include_str!("sexp/sample.fx");
const P: SyntaxProfile = SyntaxProfile::FX26;

#[test]
fn finds_definitions_and_define_rec_members() {
    let names: Vec<String> = se::definitions(SAMPLE, P).unwrap().into_iter().map(|d| d.name).collect();
    assert_eq!(names, ["a", "b", "c", "d", "s"]);
    let a = se::find(SAMPLE, P, "a").unwrap();
    assert!(SAMPLE[a.lead..a.end].starts_with(";; A comment about `a`."));
    assert!(se::find(SAMPLE, P, "zz").is_err());
}

#[test]
fn replaces_and_inserts_by_name_and_refuses_what_does_not_read() {
    let out = se::replace(SAMPLE, P, "d", "(d (subr pure (int) int) (lambda (n) n))").unwrap();
    assert!(out.contains("  (d (subr pure (int) int) (lambda (n) n)))"));
    // One closing parenthesis too many: refused, nothing changed.
    assert!(se::replace(SAMPLE, P, "b", "(define b int 1))").is_err());
    // A new text with a comment replaces the comment too.
    let out = se::replace(SAMPLE, P, "a", ";; A new comment.\n(define a int 2)").unwrap();
    assert!(out.contains(";; A new comment.\n(define a int 2)") && !out.contains("A comment about `a`"), "{out}");
    let out = se::insert_before(SAMPLE, P, "b", ";; new\n(define z int 1)").unwrap();
    assert!(out.contains(";; new\n(define z int 1)\n(define b"));
    let out = se::insert_after(SAMPLE, P, "c", "(e (subr pure () int) (lambda () 1))").unwrap();
    assert!(out.contains("(c n))))") || out.contains("\n  (e (subr pure () int)"));
}

#[test]
fn moves_a_definition_with_its_comments() {
    let out = se::move_before(SAMPLE, P, "b", "a").unwrap();
    let b = out.find("(define b").unwrap();
    let a = out.find(";; A comment about `a`.").unwrap();
    assert!(b < a, "{out}");
    let out = se::move_before(SAMPLE, P, "a", "s").unwrap();
    assert!(out.find(";; A comment about `a`.").unwrap() > out.find("(define-rec").unwrap(), "{out}");
}

#[test]
fn edits_in_several_places_balanced_together() {
    // An open paren in one place and its close in another: each alone is
    // refused, both at once are not.
    let (open, close) = (("(if (= n 0)", "(begin (if (= n 0)"), ("(d (- n 1))", "(d (- n 1)))"));
    assert!(se::edit(SAMPLE, P, "c", open.0, open.1).is_err());
    assert!(se::edit_many(SAMPLE, P, "c", &[open]).is_err());
    let out = se::edit_many(SAMPLE, P, "c", &[open, close]).unwrap();
    assert!(out.contains("(begin (if (= n 0) 0 (d (- n 1))))"), "{out}");
}

#[test]
fn deletes_a_definition_with_its_comments() {
    let out = se::delete(SAMPLE, P, "a").unwrap();
    assert!(!out.contains("A comment about `a`") && !out.contains("(define a"), "{out}");
    assert!(out.contains("(define b"));
    assert!(se::delete(SAMPLE, P, "zz").is_err());
}

#[test]
fn renames_symbols_but_not_strings() {
    let (out, n) = se::rename(SAMPLE, P, "b", "bee", None).unwrap();
    assert_eq!(n, 2);
    assert!(out.contains("(bee x)") && out.contains("(define bee") && out.contains("\"b is not a symbol here\""));
    // Within `c` only: its parameter and its two uses, not `d`'s.
    let (_, n) = se::rename(SAMPLE, P, "n", "k", Some("c")).unwrap();
    assert_eq!(n, 3);
}

#[test]
fn reports_values_used_before_their_definitions() {
    let early = se::order(&[(SAMPLE.to_string(), P)]).unwrap();
    let names: Vec<&str> = early.iter().map(|e| e.name.as_str()).collect();
    // `a` uses `b`, defined after it; `c` and `d` are one group.
    assert_eq!(names, ["b"]);
    // A parameter of the same name is no use of the definition.
    let shadow = "(define f (subr pure (int) int) (lambda (g) g))\n(define g int 1)\n";
    assert!(se::order(&[(shadow.to_string(), P)]).unwrap().is_empty());
    // A `define*` is a definition too (it was missed, TODO.md §15).
    let star = "(define f (subr pure () int) (lambda () (h 1)))\n(define* h (subr pure (int) int) (lambda (n) n))\n";
    let early = se::order(&[(star.to_string(), P)]).unwrap();
    assert_eq!(early.iter().map(|e| e.name.as_str()).collect::<Vec<_>>(), ["h"]);
}

#[test]
fn edits_text_inside_a_definition_keeping_its_balance() {
    let out = se::edit(SAMPLE, P, "b", "(+ x 1)", "(+ (* x 2) 1)").unwrap();
    assert!(out.contains("(lambda (x) (+ (* x 2) 1)))"), "{out}");
    // A fragment need not be a form: the tail of `c`'s body, closed as it was.
    let out = se::edit(SAMPLE, P, "c", "(- n 1)))))", "(- n 2)))))").unwrap();
    assert!(out.contains("(d (- n 2)))))"), "{out}");
    // One list closed fewer: refused, and says so.
    let e = se::edit(SAMPLE, P, "c", "(- n 1)))))", "(- n 1))))").unwrap_err();
    assert!(e.contains("leaves 1 more list(s) open"), "{e}");
    // Only within the definition named, and only once.
    assert!(se::edit(SAMPLE, P, "a", "(+ x 1)", "x").is_err());
    assert!(se::edit(SAMPLE, P, "c", "n", "m").unwrap_err().contains("times"));
}
