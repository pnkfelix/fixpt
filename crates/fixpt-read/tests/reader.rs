//! Reader tests, including reading the real FX corpora.
//!
//! The dialect cases are not hypothetical: each one pins down a behaviour taken
//! from the archive (or from the Racket ports' own reader files), with the
//! reason recorded, so a later "simplification" of the profile mechanism has to
//! argue with the evidence.

use fixpt_read::{Datum, Interner, Num, SourceMap, SyntaxProfile, Syntax, read_string, write_syntax};

fn read(profile: SyntaxProfile, text: &str) -> (Vec<Syntax>, Interner) {
    let mut sources = SourceMap::new();
    let mut interner = Interner::new();
    let forms = read_string(&mut sources, &mut interner, "<test>", text, profile)
        .unwrap_or_else(|e| panic!("read failed: {e}"));
    (forms, interner)
}

fn show(profile: SyntaxProfile, text: &str) -> String {
    let (forms, interner) = read(profile, text);
    forms.iter().map(|f| write_syntax(f, &interner)).collect::<Vec<_>>().join(" ")
}

fn err(profile: SyntaxProfile, text: &str) -> String {
    let mut sources = SourceMap::new();
    let mut interner = Interner::new();
    match read_string(&mut sources, &mut interner, "<test>", text, profile) {
        Ok(v) => panic!("expected an error, got {v:?}"),
        Err(e) => e.message,
    }
}

// ------------------------------------------------------------------- Scheme

#[test]
fn scheme_basics_round_trip() {
    let p = SyntaxProfile::SCHEME;
    for text in [
        "()",
        "(1 2 3)",
        "(a . b)",
        "(a b . c)",
        "#(1 2 3)",
        "#t",
        "#f",
        "\"hi\"",
        "#\\a",
        "#\\space",
        "#\\newline",
        "(quote x)",
        "(quasiquote (a (unquote b) (unquote-splicing c)))",
        "#u8(1 2 255)",
        "-42",
        "1/2",
        "3.5",
        "+inf.0",
    ] {
        let once = show(p, text);
        let twice = show(p, &once);
        assert_eq!(once, twice, "{text:?} does not survive write/read/write");
    }
}

#[test]
fn scheme_is_case_sensitive() {
    let (forms, interner) = read(SyntaxProfile::SCHEME, "Foo foo");
    let a = forms[0].as_symbol().unwrap();
    let b = forms[1].as_symbol().unwrap();
    assert_ne!(a, b);
    assert_eq!(interner.name(a), "Foo");
}

#[test]
fn quote_abbreviations_expand() {
    assert_eq!(show(SyntaxProfile::SCHEME, "'x"), "(quote x)");
    assert_eq!(show(SyntaxProfile::SCHEME, "`x"), "(quasiquote x)");
    assert_eq!(show(SyntaxProfile::SCHEME, ",x"), "(unquote x)");
    assert_eq!(show(SyntaxProfile::SCHEME, ",@x"), "(unquote-splicing x)");
    assert_eq!(show(SyntaxProfile::SCHEME, "`(a ,b ,@c)"), "(quasiquote (a (unquote b) (unquote-splicing c)))");
}

#[test]
fn comments_in_all_three_forms() {
    let p = SyntaxProfile::SCHEME;
    assert_eq!(show(p, "1 ; trailing\n2"), "1 2");
    assert_eq!(show(p, "1 #| a #| nested |# b |# 2"), "1 2");
    assert_eq!(show(p, "(1 #;2 3)"), "(1 3)");
}

#[test]
fn numbers_parse_across_radix_and_exactness() {
    let p = SyntaxProfile::SCHEME;
    let (forms, _) = read(p, "#x1f #b1011 #o17 #d99 #e10 #i2 1/2 -7 .5 1e3");
    let nums: Vec<&Num> = forms
        .iter()
        .map(|f| match &f.datum {
            Datum::Number(n) => n,
            other => panic!("not a number: {other:?}"),
        })
        .collect();
    assert_eq!(*nums[0], Num::Int(31));
    assert_eq!(*nums[1], Num::Int(11));
    assert_eq!(*nums[2], Num::Int(15));
    assert_eq!(*nums[3], Num::Int(99));
    assert_eq!(*nums[4], Num::Int(10));
    assert_eq!(*nums[5], Num::Real(2.0));
    assert_eq!(*nums[6], Num::Ratio(Box::new(Num::Int(1)), Box::new(Num::Int(2))));
    assert_eq!(*nums[7], Num::Int(-7));
    assert_eq!(*nums[8], Num::Real(0.5));
    assert_eq!(*nums[9], Num::Real(1000.0));
}

#[test]
fn integers_too_wide_for_a_word_are_kept_exact() {
    // Silently narrowing here would be a correctness bug the numeric tower
    // could never recover from.
    let (forms, _) = read(SyntaxProfile::SCHEME, "123456789012345678901234567890");
    match &forms[0].datum {
        Datum::Number(Num::Big { negative, digits, radix }) => {
            assert!(!negative);
            assert_eq!(digits, "123456789012345678901234567890");
            assert_eq!(*radix, 10);
        }
        other => panic!("expected a bignum, got {other:?}"),
    }
}

#[test]
fn symbols_that_look_like_numbers_stay_symbols() {
    let p = SyntaxProfile::SCHEME;
    for text in ["+", "-", "...", "1+", "a.b", "->", "1-", "<=?"] {
        let (forms, interner) = read(p, text);
        let s = forms[0].as_symbol().unwrap_or_else(|| panic!("{text:?} should be a symbol"));
        assert_eq!(interner.name(s), text);
    }
}

#[test]
fn pipe_symbols_escape_everything() {
    let (forms, interner) = read(SyntaxProfile::SCHEME, "|hello world| |#t| |123|");
    assert_eq!(interner.name(forms[0].as_symbol().unwrap()), "hello world");
    assert_eq!(interner.name(forms[1].as_symbol().unwrap()), "#t");
    assert_eq!(interner.name(forms[2].as_symbol().unwrap()), "123");
    // …and writing them back out re-escapes, matching Racket.
    assert_eq!(show(SyntaxProfile::SCHEME, "|#t|"), "|#t|");
    assert_eq!(show(SyntaxProfile::SCHEME, "|123|"), "|123|");
}

#[test]
fn string_escapes() {
    let (forms, _) = read(SyntaxProfile::SCHEME, r#" "a\nb\tc\\d\"e\x41;f" "#);
    assert_eq!(forms[0].as_str().unwrap(), "a\nb\tc\\d\"eAf");
    // A backslash-newline elides the line break and following indentation.
    let (forms, _) = read(SyntaxProfile::SCHEME, "\"one\\\n   two\"");
    assert_eq!(forms[0].as_str().unwrap(), "onetwo");
}

#[test]
fn errors_are_reported_with_a_span() {
    let p = SyntaxProfile::SCHEME;
    assert!(err(p, "(1 2").contains("unterminated list"));
    assert!(err(p, ")").contains("unbalanced"));
    assert!(err(p, "\"abc").contains("unterminated string"));
    assert!(err(p, "(a . )").contains("expected a datum after `.`"));
    assert!(err(p, "(a . b c)").contains("expected `)` after the tail"));
    assert!(err(p, "(. a)").contains("must follow at least one element"));
    assert!(err(p, "#\\nosuchname").contains("unknown character name"));
    assert!(err(p, "(1 2]").contains("expected `)`"));
}

// -------------------------------------------------------------------- FX-87

#[test]
fn fx87_reads_booleans_and_unit_as_symbols() {
    // syntax.lisp's literal-bool? is `(memv (caddr node) `(,|#f| ,|#t|))` and
    // literal-unit? is `(eqv? (caddr node) |#u|)`: these were never Scheme
    // booleans, and the checker's literal table depends on that.
    let (forms, interner) = read(SyntaxProfile::FX87, "#t #f #u");
    for (form, name) in forms.iter().zip(["#t", "#f", "#u"]) {
        let s = form.as_symbol().unwrap_or_else(|| panic!("{name} should be a symbol"));
        assert_eq!(interner.name(s), name);
    }
}

#[test]
fn fx87_folds_case() {
    let (forms, interner) = read(SyntaxProfile::FX87, "LAMBDA Lambda lambda");
    let a = forms[0].as_symbol().unwrap();
    assert_eq!(forms[1].as_symbol().unwrap(), a);
    assert_eq!(forms[2].as_symbol().unwrap(), a);
    assert_eq!(interner.name(a), "lambda");
}

#[test]
fn fx87_brackets_are_symbol_characters() {
    // `intern-[p]defines?` and `free-[d]vars` are single Common Lisp symbols;
    // treating brackets as parentheses would split them into three tokens.
    let (forms, interner) = read(SyntaxProfile::FX87, "intern-[p]defines? free-[d]vars");
    assert_eq!(interner.name(forms[0].as_symbol().unwrap()), "intern-[p]defines?");
    assert_eq!(interner.name(forms[1].as_symbol().unwrap()), "free-[d]vars");
}

#[test]
fn fx87_region_symbols() {
    let (forms, interner) = read(SyntaxProfile::FX87, "@= @! @red @hash-value-accumulator-region");
    assert_eq!(interner.name(forms[0].as_symbol().unwrap()), "@=");
    assert_eq!(interner.name(forms[1].as_symbol().unwrap()), "@!");
    assert_eq!(interner.name(forms[3].as_symbol().unwrap()), "@hash-value-accumulator-region");
}

// -------------------------------------------------------------------- FX-91

#[test]
fn fx91_reads_real_booleans_but_uppercase_unit() {
    // impl.rkt's LITERAL? recognises #t/#f via BOOLEAN?, but FX-UNIT-VALUE is
    // built with string->symbol at load time, before case folding can apply --
    // so it is uppercase `#U` even though the source says `#u`.
    let (forms, interner) = read(SyntaxProfile::FX91, "#t #f #u");
    assert_eq!(forms[0].datum, Datum::Bool(true));
    assert_eq!(forms[1].datum, Datum::Bool(false));
    assert_eq!(interner.name(forms[2].as_symbol().unwrap()), "#U");
}

#[test]
fn fx91_bracket_projection_sugar() {
    // Report §2.4.9. The original reader macro is lost and the Racket port
    // cannot reach this at all -- Racket reads `[e d]` and `(e d)` as the same
    // datum -- so this is the one place where we genuinely exceed the
    // reference, deliberately and per the published grammar.
    let p = SyntaxProfile::FX91;
    assert_eq!(show(p, "[ cons (t type) ]"), "(proj cons (t type))");
    assert_eq!(show(p, "[f int bool]"), "(proj f int bool)");
    // As it appears in tests.fx's own DEFINE heads.
    assert_eq!(
        show(p, "(define ([ car (t type) ] p) p)"),
        "(define ((proj car (t type)) p) p)"
    );
    assert!(err(p, "[a . b]").contains("not allowed in `[…]`"));
}

#[test]
fn fx91_dot_notation_is_a_symbol_not_a_dotted_pair() {
    // `m.x` is module selection sugar (report §2.4.7) and must survive the
    // reader intact; only a *lone* dot is the pair marker.
    let (forms, interner) = read(SyntaxProfile::FX91, "m.x a.b.c (a . b)");
    assert_eq!(interner.name(forms[0].as_symbol().unwrap()), "m.x");
    assert_eq!(interner.name(forms[1].as_symbol().unwrap()), "a.b.c");
    assert!(matches!(forms[2].datum, Datum::List { tail: Some(_), .. }));
}

#[test]
fn fx91_backslash_escaped_digit_symbols() {
    // standard.scm's sexp-module uses `\1` … `\9` as sumof/productof tags.
    let (forms, interner) = read(SyntaxProfile::FX91, r"(\1 (productof (\1 unit)))");
    let items = forms[0].as_proper_list().unwrap();
    assert_eq!(interner.name(items[0].as_symbol().unwrap()), "1");
}

// --------------------------------------------------- the real archive corpora

const FX91_TESTS: &str = include_str!("../../../tests/conformance/fx91/cases/tests.fx");
const FX87_CASES: &str = include_str!("../../../tests/conformance/fx87/cases/kernel.fx");

#[test]
fn reads_the_whole_fx91_test_suite() {
    let (forms, interner) = read(SyntaxProfile::FX91, FX91_TESTS);
    assert_eq!(forms.len(), 182, "tests.fx has 182 top-level forms");

    // Spot-check that the projection sugar actually fired somewhere in it,
    // rather than the file happening to parse for unrelated reasons.
    let proj = interner.get("proj").expect("`proj` was interned, so `[…]` was used");
    fn mentions(s: &Syntax, target: fixpt_read::Sym) -> bool {
        match &s.datum {
            Datum::Symbol(x) => *x == target,
            Datum::List { items, tail } => {
                items.iter().any(|i| mentions(i, target))
                    || tail.as_ref().is_some_and(|t| mentions(t, target))
            }
            Datum::Vector(items) => items.iter().any(|i| mentions(i, target)),
            _ => false,
        }
    }
    assert!(forms.iter().any(|f| mentions(f, proj)), "no `[…]` projection sugar found");
}

#[test]
fn reads_the_whole_fx87_corpus() {
    let (forms, _) = read(SyntaxProfile::FX87, FX87_CASES);
    assert_eq!(forms.len(), 155, "the FX-87 corpus has 155 forms");
}

#[test]
fn every_fx91_form_survives_write_then_read() {
    // A stronger check than "it parses": the printer and reader must agree, or
    // error messages and golden comparisons will quietly disagree with the
    // source.
    let (forms, interner) = read(SyntaxProfile::FX91, FX91_TESTS);
    let printed: Vec<String> = forms.iter().map(|f| write_syntax(f, &interner)).collect();
    let (again, interner2) = read(SyntaxProfile::FX91, &printed.join("\n"));
    assert_eq!(again.len(), forms.len());
    for (i, (a, b)) in printed.iter().zip(again.iter()).enumerate() {
        assert_eq!(*a, write_syntax(b, &interner2), "form {} differs on re-read", i + 1);
    }
}
