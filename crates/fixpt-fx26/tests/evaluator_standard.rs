//! The evaluator written in FX-26 has the standard environment the
//! checkers accept: every standard name but the compilers' own (of machine
//! code and words, which it has none of), each as the machines have it
//! (Heist's R4, `TODO.md` §211: `reverse` was "an unbound variable" there,
//! and some seventy names besides).

mod common;

/// What is not the evaluator's: the compilers' own, which it refuses as
/// theirs; and the i-cells' forms' names as values, whose forms it runs.
fn not_the_evaluators(name: &str) -> bool {
    ["tword-", "wcell-", "wglobal", "rep-", "runtime-primitive", "set-register-twin"].iter().any(|p| name.starts_with(p))
        || ["make-word", "make-global", "close-over-word!", "disassemble", "icell-get", "icell-put!"].contains(&name)
}

#[test]
fn every_standard_name_is_the_evaluators() {
    let names: Vec<&str> = fixpt_fx26::standard::ENTRIES.iter().map(|(n, _)| *n).filter(|n| !n.starts_with('%') && !not_the_evaluators(n)).collect();
    let unbound: Vec<String> = common::with_own_eval(|s| {
        names
            .iter()
            .filter_map(|n| match s.eval_with_own_evaluator(n) {
                Ok(out) if out.contains("unbound variable") || out.contains("the compilers'") => Some(format!("{n}: {out}")),
                Err(e) if e.message.contains("unbound variable") => Some(format!("{n}: {}", e.message)),
                _ => None,
            })
            .collect()
    });
    assert!(names.len() > 300, "only {} names", names.len());
    assert!(unbound.is_empty(), "{}", unbound.join("\n"));
}

/// Each found missing, as the machines give it (the default machine's
/// answers, written here).
#[test]
fn the_evaluator_gives_what_the_machines_give() {
    let cases = [
        ("(reverse (list 1 2 3))", "(3 2 1)"),
        ("(char-alphabetic? #\\1)", "#f"),
        ("(char-whitespace? #\\space)", "#t"),
        ("(char-downcase #\\Q)", "#\\q"),
        ("(char-in? #\\b \"abc\")", "#t"),
        ("(string-downcase \"AbC\")", "\"abc\""),
        ("(string-ci=? \"abc\" \"ABC\")", "#t"),
        ("(string-compare \"b\" \"a\")", "1"),
        ("(string-search \"hello\" \"l\" 3)", "3"),
        ("(symbol-compare 'a 'b)", "-1"),
        ("(nat? -1)", "#f"),
        ("(parse-nat \"ff\" 16)", "255"),
        ("(parse-number \"1.5\" 10)", "(1.5)"),
        ("(array->list (make-array 3 7))", "(7 7 7)"),
        ("(array-length (list->array (list 1 2 3)))", "3"),
        ("(length-is? (list 1 2) 3)", "#f"),
        ("(acyclic? (list 1 2))", "#t"),
        ("(quote #(1 (2 3) #(4)))", "#(1 (2 3) #(4))"),
        ("(vector? 1)", "#f"),
        ("(bytevector? (make-bytevector 2 0))", "#t"),
        ("(datum-byte? (quote 256))", "#f"),
        ("(datum-proper-list? (quote (1 . 2)))", "#f"),
        ("(typecase (the datum (quote #(1))) (vector v 1) (else 2))", "1"),
        (include_str!("programs/run/eqtable.fx"), "12"),
    ];
    let wrong: Vec<String> = common::with_own_eval(|s| {
        cases
            .iter()
            .filter_map(|(text, want)| {
                let got = s.eval_with_own_evaluator(text).map_err(|e| e.message);
                (got.as_deref() != Ok(want)).then(|| format!("{text}: wants {want}, gives {got:?}"))
            })
            .collect()
    });
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
