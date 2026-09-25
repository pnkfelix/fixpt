//! Lexical syntax profiles — what makes the same reader serve three languages.
//!
//! The FX dialects are not Scheme with extra forms; they differ at the
//! character level, and the archive is explicit about it:
//!
//! * FX-87's own reader (`fx-extensions.lisp`, reproduced in
//!   `fx87-hashlang/lang/reader.rkt`) reads `#t`, `#f` and `#u` as **symbols**,
//!   because `syntax.lisp`'s `literal-bool?` tests `(memv (caddr node) '(|#f|
//!   |#t|))` — they were never Scheme booleans. It also needs `[` and `]` as
//!   ordinary symbol characters, since `intern-[p]defines?` and
//!   `free-[d]vars` are single Common Lisp symbols.
//!
//! * FX-91 reads `#t`/`#f` as real booleans but `#u` as the **uppercase**
//!   symbol `#U`, because `standard.scm:90` builds it with `string->symbol` at
//!   load time, before any case-folding reader parameter could apply.
//!
//! * FX-91 also has `[e dx1 … dxn]` as sugar for `(proj e dx1 … dxn)` (report
//!   §2.4.9). The reader macro that implemented it is not in the recovered
//!   archive — `sugar.scm:7` only *refers* to it — and the Racket port cannot
//!   reach the feature at all, because Racket's reader gives `[e d]` and
//!   `(e d)` the identical datum. Here the reader is ours, so it works.
//!
//! * Both dialects fold symbol case; Scheme does not.
//!
//! * FX-26, this project's own dialect, has a profile of its own rather than
//!   borrowing one: Scheme's, except that `#u` is also the unit value and
//!   `[`/`]` are reserved — FX-91 used them for projection sugar, and FX-26
//!   has not yet decided what they are for.

/// How `[` and `]` are treated.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Brackets {
    /// Interchangeable with `(` and `)`, and required to match.
    Parens,
    /// Ordinary symbol constituents — FX-87 needs `free-[d]vars` to be one
    /// symbol.
    SymbolChars,
    /// `[e d…]` reads as `(proj e d…)` — FX-91's projection sugar.
    ProjSugar,
    /// Delimiters that mean nothing yet: using one is an error. FX-26's, so
    /// that giving them a meaning later breaks no program.
    Reserved,
}

/// How `#u` reads.
///
/// Both FX dialects read it as a *symbol*, not as a distinguished datum:
/// FX-87's `literal-unit?` tests `(eq? (caddr node) |#u|)` and FX-91's
/// `fx-unit-value` is `(string->symbol "#U")`. Modelling it faithfully costs
/// nothing and keeps the front ends' literal tables matching the originals'.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum UnitSyntax {
    /// Not unit syntax. `#u8(` opens a bytevector instead.
    Bytevector,
    /// `#u` reads as the symbol named by [`SyntaxProfile::unit_name`].
    Symbol,
    /// Both: `#u` on its own is the unit symbol, and `#u8(` opens a
    /// bytevector. They do not collide, since R7RS spells bytevectors with
    /// the `8`.
    SymbolOrBytevector,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct SyntaxProfile {
    pub name: &'static str,
    /// Fold unescaped symbol characters to lower case. `|Foo|` is still `Foo`.
    pub case_fold: bool,
    pub brackets: Brackets,
    /// `#t`/`#f` read as the symbols `#t`/`#f` rather than as booleans.
    pub booleans_are_symbols: bool,
    pub unit: UnitSyntax,
    /// The symbol `#u` produces when `unit` is [`UnitSyntax::Unit`]. FX-91
    /// needs this uppercase; FX-87 needs it lowercase.
    pub unit_name: &'static str,
    /// `#;` datum comments.
    pub datum_comments: bool,
    /// `#| … |#` nestable block comments.
    pub block_comments: bool,
    /// `#n=` / `#n#` datum labels.
    pub datum_labels: bool,
    /// `'`, `` ` ``, `,`, `,@`.
    pub quote_sugar: bool,
}

impl SyntaxProfile {
    /// R7RS-flavoured Scheme.
    pub const SCHEME: SyntaxProfile = SyntaxProfile {
        name: "scheme",
        case_fold: false,
        brackets: Brackets::Parens,
        booleans_are_symbols: false,
        unit: UnitSyntax::Bytevector,
        unit_name: "",
        datum_comments: true,
        block_comments: true,
        datum_labels: true,
        quote_sugar: true,
    };

    pub const FX87: SyntaxProfile = SyntaxProfile {
        name: "fx87",
        case_fold: true,
        brackets: Brackets::SymbolChars,
        booleans_are_symbols: true,
        unit: UnitSyntax::Symbol,
        unit_name: "#u",
        datum_comments: false,
        block_comments: false,
        datum_labels: false,
        quote_sugar: true,
    };

    pub const FX91: SyntaxProfile = SyntaxProfile {
        name: "fx91",
        case_fold: true,
        brackets: Brackets::ProjSugar,
        booleans_are_symbols: false,
        unit: UnitSyntax::Symbol,
        // Uppercase, and deliberately so: see the module docs.
        unit_name: "#U",
        datum_comments: false,
        block_comments: false,
        datum_labels: false,
        quote_sugar: true,
    };

    /// FX-26: Scheme's lexical syntax, with `#u` as unit beside `#u8(`, and
    /// `[`/`]` reserved.
    pub const FX26: SyntaxProfile = SyntaxProfile {
        name: "fx26",
        case_fold: false,
        brackets: Brackets::Reserved,
        booleans_are_symbols: false,
        unit: UnitSyntax::SymbolOrBytevector,
        unit_name: "#u",
        datum_comments: true,
        block_comments: true,
        // Nothing in FX-26 is a cyclic datum to label.
        datum_labels: false,
        quote_sugar: true,
    };

    pub fn by_name(name: &str) -> Option<SyntaxProfile> {
        match name {
            "scheme" | "r7rs" => Some(SyntaxProfile::SCHEME),
            "fx87" => Some(SyntaxProfile::FX87),
            "fx91" => Some(SyntaxProfile::FX91),
            "fx26" => Some(SyntaxProfile::FX26),
            _ => None,
        }
    }
}
