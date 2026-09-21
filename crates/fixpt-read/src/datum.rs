//! The spanned s-expression the front ends consume.

use crate::intern::{Interner, Sym};
use crate::span::Span;

/// A numeric literal, kept in the form it was written so the numeric layer can
/// decide representation. Splitting "what was written" from "how it is stored"
/// is what lets the reader stay free of bignum arithmetic.
#[derive(Clone, PartialEq, Debug)]
pub enum Num {
    /// An exact integer that fits a machine word.
    Int(i64),
    /// An exact integer that does not. Digits are in `radix`, unsigned.
    Big { negative: bool, digits: String, radix: u32 },
    /// An exact ratio, already in lowest terms only if the source was.
    Ratio(Box<Num>, Box<Num>),
    /// An inexact real.
    Real(f64),
}

impl Num {
    pub fn is_exact(&self) -> bool {
        !matches!(self, Num::Real(_))
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Datum {
    Bool(bool),
    Number(Num),
    Char(char),
    Str(String),
    Symbol(Sym),
    /// `()`
    Nil,
    /// A possibly-improper list. `tail` is `Some` only for `(a . b)`.
    ///
    /// Storing lists flat rather than as nested pairs is a deliberate
    /// divergence from Scheme's own representation: the FX front ends index
    /// heavily (`cadr`, `caddr`, `cadddr` appear throughout `token.scm` and
    /// `syntax-check.lisp`), and a `Vec` makes that a bounds check rather than
    /// a pointer chase. Conversion to real heap pairs happens in one place.
    List { items: Vec<Syntax>, tail: Option<Box<Syntax>> },
    Vector(Vec<Syntax>),
    Bytevector(Vec<u8>),
}

/// A datum plus where it came from.
#[derive(Clone, PartialEq, Debug)]
pub struct Syntax {
    pub span: Span,
    pub datum: Datum,
}

impl Syntax {
    pub fn new(span: Span, datum: Datum) -> Syntax {
        Syntax { span, datum }
    }

    /// Build `(head rest…)` attributed to `span` — how desugarers synthesise
    /// forms while keeping errors pointing at the user's own text.
    pub fn list(span: Span, items: Vec<Syntax>) -> Syntax {
        Syntax::new(span, Datum::List { items, tail: None })
    }

    pub fn symbol(span: Span, s: Sym) -> Syntax {
        Syntax::new(span, Datum::Symbol(s))
    }

    pub fn as_symbol(&self) -> Option<Sym> {
        match self.datum {
            Datum::Symbol(s) => Some(s),
            _ => None,
        }
    }

    /// The elements of a proper list, or `None` for anything else — including
    /// an improper list, which callers almost always want to reject.
    pub fn as_proper_list(&self) -> Option<&[Syntax]> {
        match &self.datum {
            Datum::List { items, tail: None } => Some(items),
            Datum::Nil => Some(&[]),
            _ => None,
        }
    }

    /// True when this is `(kw …)` for the given keyword.
    pub fn is_form(&self, kw: Sym) -> bool {
        self.as_proper_list()
            .and_then(|items| items.first())
            .and_then(|h| h.as_symbol())
            .is_some_and(|s| s == kw)
    }

    pub fn as_i64(&self) -> Option<i64> {
        match &self.datum {
            Datum::Number(Num::Int(n)) => Some(*n),
            _ => None,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match &self.datum {
            Datum::Str(s) => Some(s),
            _ => None,
        }
    }

    /// Render for an error message. Not `write`-faithful — see
    /// [`crate::writer`] for that — just short and recognisable.
    pub fn summary(&self, interner: &Interner) -> String {
        crate::writer::write_syntax(self, interner)
    }
}
