//! Macros at the REPL (`docs/research/typed-macros.md`): every entry is
//! read into the session's one text, past those before
//! (`Fx26Session::read_entry`), so a place says which entry it is in, a
//! template's the one that defined its macro.

use std::io::Write as _;
use std::process::{Command, Stdio};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// What the REPL prints, out and error, given `input`.
fn repl(input: &str) -> String {
    let mut child = Command::new(FIXPT).arg("repl").stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().expect("starts");
    child.stdin.take().expect("piped").write_all(input.as_bytes()).expect("writes");
    let out = child.wait_with_output().expect("finishes");
    format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
}

/// A use in a later entry than its macro's definition runs (it once took
/// the entry's text by the template's place, past its end), and an error in
/// what its template made is said in the entry that defined it.
#[test]
fn a_macro_is_used_in_a_later_entry() {
    let def = "(define-syntax foo (macro (_ (x @ bvar e @ expr) body @ expr) expr (bind x in body)) (syntax-rules ((_ (x e) body) (let ((x e)) body))))\n";
    let out = repl(&format!("{def}(foo (hey \"dude\") hey)\n(define-syntax bad (macro (_ expr) expr) (syntax-rules ((_ e) (+ e #t))))\n(bad 3)\n"));
    assert!(out.contains("\"dude\" : string"), "{out}");
    assert!(out.contains("<fx26:3>:1:68: argument 2 is a bool") && !out.contains("panicked"), "{out}");
    assert!(out.contains("  in the expansion of `bad` at <fx26:4>:1:1"), "{out}");
}

/// A macro that makes definitions, used in later entries: each use's
/// definitions shown, its template's own made fresh for each use.
#[test]
fn a_macro_makes_definitions_in_later_entries() {
    let def = "(define-syntax define-counter (macro (_ bvar) defn) (syntax-rules ((_ name) (begin (define count (new 0)) (define name (lambda () (begin (set count (+ (get count) 1)) (get count))))))))\n";
    let out = repl(&format!("{def}(define-counter tick)\n(define-counter tock)\n(tick)\n(+ (tick) (tock))\n"));
    assert!(out.contains("tick : (subr") && out.contains("tock : (subr"), "{out}");
    // Each use's own, named by its form's key (`Macros::form_begin`).
    let counts: Vec<&str> = out.lines().filter_map(|l| l.split(" : (ref int").next().filter(|_| l.contains(" : (ref int"))?.rsplit(' ').next()).collect();
    assert!(counts.len() >= 2 && counts.iter().all(|c| c.starts_with("%count:") && c.ends_with(".1")) && counts[0] != counts[1], "{out}");
    assert!(out.contains("3 : int") && !out.contains("panicked"), "{out}");
}

/// A module file's own expansion that made a macro (`own.fx`'s
/// `(define-clamper clamp)`) leaves nothing to the entry that loads it: an
/// earlier entry's global `clamp` stays the session's, the load not refused
/// "`clamp` is defined already" (the macros an expansion made, none at each
/// form's start: `Macros::form_begin`, FX-26's `form-begun!`).
#[test]
fn a_files_own_made_macro_is_not_the_loaders() {
    let own = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/import-with-syntax/own.fx");
    let out = repl(&format!("(define clamp 7)\n(define lib (load-module \"{own}\"))\n(with lib clamped)\nclamp\n"));
    assert!(!out.contains("defined already") && out.contains("10 : int") && out.contains("7 : int ! (read (globals clamp))"), "{out}");
}

/// A procedural macro's alias, `%~K.N:x`, is of its form and the
/// expansions in it alone (`Macros::expansion_begun`): a use's global is
/// spelled the same whatever the forms before it expanded, and alike in
/// both checkers (it was `%~N:x`, `N` the session's count).
#[test]
fn a_procedural_macros_alias_is_of_its_form() {
    let check = |text: &str| {
        let out = Command::new(FIXPT).args(["check", "--reps=text", text]).output().expect("runs");
        format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
    };
    let counter = "(define-syntax counter (er-macro-transformer (lambda (form rename compare) `(,(rename 'begin) (,(rename 'define) ,(rename 'n) 1)))))\n";
    let other = "(define-syntax one (er-macro-transformer (lambda (form rename compare) 1)))\n(define two (+ (one) (one)))\n";
    let alone = check(&format!("{counter}(counter)\n"));
    let after = check(&format!("{counter}{other}(counter)\n"));
    let aliases = |out: &str| out.lines().filter(|l| l.starts_with("%~")).map(str::to_string).collect::<Vec<_>>();
    assert!(aliases(&alone).len() == 1 && aliases(&alone) == aliases(&after), "{alone}\n{after}");
    assert!(aliases(&alone)[0].ends_with(".1:n (base int)") && !after.contains("differs"), "{alone}\n{after}");
}

/// A form's key hashes every atom by its value (`syn_hash`, `syn-hash`),
/// numbers too, so `(check 1)` and `(check 2)` have keys apart: putting one
/// before the other names neither's fresh names otherwise (Kayak's
/// INCR_IMPED.md §5; a number was its kind alone, the two forms one key
/// counted twice, `K` and `K-1`). Alike in both checkers.
#[test]
fn a_forms_key_is_of_its_numbers_too() {
    let check = |text: &str| {
        let out = Command::new(FIXPT).args(["check", "--reps=text", text]).output().expect("runs");
        format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
    };
    let def = "(define-syntax check (macro (_ expr) defn) (syntax-rules ((_ v) (define seen v))))\n";
    let ab = check(&format!("{def}(check 1)\n(check 2)\n(check 1.5)\n(check #\\a)\n"));
    let ba = check(&format!("{def}(check #\\a)\n(check 1.5)\n(check 2)\n(check 1)\n"));
    let seen = |out: &str| out.lines().filter(|l| l.starts_with("%seen:")).map(|l| l.split(' ').next().unwrap_or("").to_string()).collect::<Vec<_>>();
    let (mut a, b) = (seen(&ab), seen(&ba));
    assert!(a.len() == 4 && a.iter().all(|n| n.ends_with(".1") && !n.contains('-')), "{ab}");
    a.reverse();
    assert!(a == b && !ab.contains("differs") && !ba.contains("differs"), "{ab}\n{ba}");
}
