//! The names the language reserves, interned once.
//!
//! Comparing `Sym`s rather than strings keeps the parser's dispatch to integer
//! equality, and gathering them here means the set of reserved words is one
//! list rather than string literals scattered through a match.

use fixpt_read::{Interner, Sym};

macro_rules! syms {
    ($($field:ident => $text:literal,)*) => {
        #[derive(Clone, Debug)]
        pub struct Syms { $(pub $field: Sym,)* }

        impl Syms {
            pub fn new(interner: &mut Interner) -> Syms {
                Syms { $($field: interner.intern($text),)* }
            }
        }
    };
}

syms! {
    // description constructors with their own syntax
    subr => "subr",
    vsubr => "vsubr",
    poly => "poly",
    recordof => "recordof",
    oneof => "oneof",
    dletrec => "dletrec",
    dlet => "dlet",
    dlambda => "dlambda",
    // effects
    pure => "pure",
    read => "read",
    write => "write",
    alloc => "alloc",
    maxeff => "maxeff",
    // regions
    runion => "runion",
    region_eq => "@=",
    region_bang => "@!",
    // kinds
    kind_type => "type",
    kind_effect => "effect",
    kind_region => "region",
    dfunc => "dfunc",
    // expression keywords
    the => "the",
    if_ => "if",
    begin => "begin",
    lambda => "lambda",
    letrec => "letrec",
    plambda => "plambda",
    plet => "plet",
    pletrec => "pletrec",
    proj => "proj",
    set_bang => "set!",
    quote => "quote",
    // sugar
    let_ => "let",
    let_star => "let*",
    and => "and",
    or => "or",
    cond => "cond",
    else_ => "else",
    do_ => "do",
    // standard forms
    record => "record",
    select => "select",
    record_set => "record-set!",
    one => "one",
    tagcase => "tagcase",
    one_set => "one-set!",
    delay => "delay",
    vlambda => "vlambda",
    promise => "promise",
    // literals that the FX-87 reader delivers as symbols
    true_ => "#t",
    false_ => "#f",
    unit => "#u",
    // standard types used by literals
    int => "int",
    bool => "bool",
    char => "char",
    float => "float",
    unit_type => "unit",
    symbol => "symbol",
    string => "string",
    ref_ => "ref",
    pairof => "pairof",
}
