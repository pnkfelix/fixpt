//! The symbols FX-91 parsing needs to recognise or construct, interned once.

use fixpt_read::{Interner, Sym};

macro_rules! syms {
    ($($field:ident => $name:literal),* $(,)?) => {
        #[derive(Clone, Debug)]
        pub struct Syms { $(pub $field: Sym,)* }
        impl Syms {
            pub fn new(i: &mut Interner) -> Syms {
                Syms { $($field: i.intern($name),)* }
            }
        }
    };
}

syms! {
    // ---- kernel keywords (token.scm's *fx-keywords*) ----
    abs => "abs",
    and => "and",
    begin => "begin",
    cond => "cond",
    define_abstraction => "define-abstraction",
    define_datatype => "define-datatype",
    define_description => "define-description",
    define => "define",
    define_typed => "define-typed",
    desc => "desc",
    dfunc => "dfunc",
    arrow_arrow => "->>",
    dlambda => "dlambda",
    effect => "effect",
    else_ => "else",
    extend => "extend",
    extract => "extract",
    fx => "fx",
    if_ => "if",
    lambda => "lambda",
    let_ => "let",
    letrec => "letrec",
    let_star => "let*",
    load => "load",
    match_ => "match",
    maxeff => "maxeff",
    module => "module",
    moduleof => "moduleof",
    open => "open",
    or => "or",
    plambda => "plambda",
    poly => "poly",
    product => "product",
    productof => "productof",
    proj => "proj",
    select => "select",
    subr => "subr",
    arrow => "->",
    sum => "sum",
    sumof => "sumof",
    symbol => "symbol",
    tagcase => "tagcase",
    the => "the",
    type_ => "type",
    val => "val",
    with => "with",

    // ---- not in *fx-keywords* but dispatched on ----
    close => "close",
    does => "does",
    do_ => "do",
    quote => "quote",
    quasiquote => "quasiquote",
    unquote => "unquote",
    unquote_splicing => "unquote-splicing",
    pure => "pure",
    underscore => "_",

    // ---- literal identifiers, from standard.scm's add-literal calls ----
    a_bool => "a-bool",
    an_unit => "an-unit",
    an_int => "an-int",
    a_float => "a-float",
    a_char => "a-char",
    a_string => "a-string",
    a_sym => "a-sym",
    a_listof => "a-listof",
    a_sexp => "a-sexp",
    nil => "nil",
    unit_value => "#U",

    // ---- names desugaring constructs ----
    up_prefix => "up-",
    down_prefix => "down-",
    unspecified => "unspecified",
    identity => "identity",
    cons_tilde => "cons~",
    null_tilde => "nil~",
    list_to_sexp => "list->sexp~",
    quoted_to_sexp => "quoted->sexp~",
    quasiquoted_to_sexp => "quasiquoted->sexpr~",
    unquoted_to_sexp => "unquoted->sexp",
    unquoted_splicing_to_sexp => "unquoted-splicing->sexp~",
    set_bang => "set!",
    set_bang_renamed => "set!-1",
}

/// `token.scm`'s `*fx-keywords*`, the identifiers a program may not rebind.
///
/// Reproduced exactly, including its omissions: `close`, `does`, `do`, `quote`
/// and `match` are dispatched on by the parser but are *not* on this list, so
/// FX-91 lets you shadow them. That is the reference's behaviour and programs
/// in the test suite rely on some of it.
pub const KEYWORD_FIELDS: &[&str] = &[
    "abs", "and", "begin", "cond",
    "define-abstraction", "define-datatype", "define-description", "define",
    "define-typed", "desc", "dfunc", "->>", "dlambda",
    "effect", "else", "extend", "extract",
    "fx", "if", "lambda", "let",
    "letrec", "let*", "load", "match",
    "maxeff", "module", "moduleof", "open",
    "or", "plambda", "poly", "product",
    "productof", "proj", "select", "subr", "->",
    "sum", "sumof", "symbol", "tagcase",
    "the", "type", "val", "with",
];
