//! `fixpt-read` — one reader, three lexical syntaxes.
//!
//! Scheme, FX-87 and FX-91 differ at the character level, not merely in their
//! special forms: case folding, whether `#t` is a boolean or a symbol, whether
//! `#u` exists at all and under what name, and whether `[…]` is a parenthesis,
//! a pair of symbol characters, or projection sugar. [`SyntaxProfile`] captures
//! exactly those differences, so the tokeniser, the list reader, the number
//! parser and the string parser are shared rather than triplicated.
//!
//! The reader yields Rust-side [`Syntax`] trees carrying [`Span`]s. They are
//! deliberately not heap values: errors get real source locations, and no
//! front-end code can hold a `Value` across a collection.

pub mod datum;
pub mod intern;
pub mod profile;
pub mod reader;
pub mod span;
pub mod writer;

pub use datum::{Datum, Num, Syntax};
pub use intern::{Interner, Sym};
pub use profile::{Brackets, SyntaxProfile, UnitSyntax};
pub use reader::{ReadError, ReadResult, Reader, form_status, FormStatus};
pub use span::{FileId, SourceMap, Span};
pub use reader::{match_delimiter, tokens, Token, TokenKind};
pub use writer::{display_syntax, escape_symbol, write_syntax};

/// Read every datum in `text` under `profile`. The common entry point.
pub fn read_string(
    sources: &mut SourceMap,
    interner: &mut Interner,
    name: &str,
    text: &str,
    profile: SyntaxProfile,
) -> ReadResult<Vec<Syntax>> {
    let file = sources.add(name, text);
    Reader::new(text, file, profile, interner).read_all()
}
