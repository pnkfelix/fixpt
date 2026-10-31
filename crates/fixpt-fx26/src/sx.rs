//! The Scheme the lowering makes (`lower.rs`): s-expressions, given to the
//! Scheme session as syntax (`Code::syntax`), with its own symbols, and
//! written out only to be shown (`,code`). Symbols are kept by name, so the
//! checker's interner and the session's need not agree.

use fixpt_read::{Datum, Interner, Span, Syntax};
use std::fmt;

/// A Scheme expression or form.
#[derive(Clone, Debug, PartialEq)]
pub enum Sx {
    Sym(String),
    Int(i128),
    Float(f64),
    Str(String),
    Char(char),
    Bool(bool),
    List(Vec<Sx>),
    /// `(a … . d)`.
    Dotted(Vec<Sx>, Box<Sx>),
}

impl Sx {
    pub fn sym(s: impl Into<String>) -> Sx {
        Sx::Sym(s.into())
    }

    /// `(head args …)`.
    pub fn call(head: &str, args: impl IntoIterator<Item = Sx>) -> Sx {
        let mut items = vec![Sx::sym(head)];
        items.extend(args);
        Sx::List(items)
    }

    /// `'x`.
    pub fn quote(x: Sx) -> Sx {
        Sx::call("quote", [x])
    }

    pub fn int(n: impl Into<i128>) -> Sx {
        Sx::Int(n.into())
    }

    /// As syntax, every piece at `span`, its symbols interned in `interner`.
    pub fn syntax(&self, interner: &mut Interner, span: Span) -> Syntax {
        let datum = match self {
            Sx::Sym(s) => Datum::Symbol(interner.intern(s)),
            Sx::Int(n) => Datum::Number(number(&n.to_string())),
            Sx::Float(x) => Datum::Number(number(&fixpt_runtime::num::format_flonum(*x))),
            Sx::Str(s) => Datum::Str(s.clone()),
            Sx::Char(c) => Datum::Char(*c),
            Sx::Bool(b) => Datum::Bool(*b),
            Sx::List(items) if items.is_empty() => Datum::Nil,
            Sx::List(items) => Datum::List { items: items.iter().map(|x| x.syntax(interner, span)).collect(), tail: None },
            Sx::Dotted(items, tail) => Datum::List {
                items: items.iter().map(|x| x.syntax(interner, span)).collect(),
                tail: Some(Box::new(tail.syntax(interner, span))),
            },
        };
        Syntax::new(span, datum)
    }
}

/// A number the lowering wrote, as the reader reads it.
fn number(text: &str) -> fixpt_read::Num {
    fixpt_read::reader::parse_number(text, 10, None).unwrap_or_else(|| panic!("`{text}` reads as a number"))
}

impl fmt::Display for Sx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sx::Sym(s) => f.write_str(&fixpt_read::escape_symbol(s)),
            Sx::Int(n) => write!(f, "{n}"),
            Sx::Float(x) => f.write_str(&fixpt_runtime::num::format_flonum(*x)),
            Sx::Str(s) => {
                f.write_str("\"")?;
                for ch in s.chars() {
                    match ch {
                        '"' => f.write_str("\\\"")?,
                        '\\' => f.write_str("\\\\")?,
                        '\n' => f.write_str("\\n")?,
                        c => write!(f, "{c}")?,
                    }
                }
                f.write_str("\"")
            }
            Sx::Char(c) if c.is_ascii_alphanumeric() => write!(f, "#\\{c}"),
            Sx::Char(c) => write!(f, "#\\x{:x}", *c as u32),
            Sx::Bool(b) => f.write_str(if *b { "#t" } else { "#f" }),
            // `'x`, as the lowering wrote it.
            Sx::List(items) if items.len() == 2 && items[0] == Sx::sym("quote") => write!(f, "'{}", items[1]),
            Sx::List(items) => {
                f.write_str("(")?;
                for (i, x) in items.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    write!(f, "{x}")?;
                }
                f.write_str(")")
            }
            Sx::Dotted(items, tail) => {
                f.write_str("(")?;
                for x in items {
                    write!(f, "{x} ")?;
                }
                write!(f, ". {tail})")
            }
        }
    }
}

/// What one top-level form lowers to: Scheme forms, in order, none for a
/// form that makes nothing run (a `define-type`).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Code(pub Vec<Sx>);

impl Code {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// `other` after this.
    pub fn extend(&mut self, other: Code) {
        self.0.extend(other.0);
    }

    /// As syntax for a Scheme session's runtime `rt`: its symbols interned
    /// there, every piece placed in a source named `name`, of no text. Not
    /// written out to be read: an error in code the lowering made is the
    /// lowering's, and says what it is without a place in it.
    pub fn syntax(&self, rt: &mut fixpt_runtime::Runtime, name: &str) -> Vec<Syntax> {
        let file = rt.sources.add(name, "");
        let span = Span::new(file, 0, 0);
        self.0.iter().map(|x| x.syntax(&mut rt.interner, span)).collect()
    }
}

impl From<Sx> for Code {
    fn from(x: Sx) -> Code {
        Code(vec![x])
    }
}

/// Each form on a line of its own, as the lowering's text was.
impl fmt::Display for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, x) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str("\n")?;
            }
            write!(f, "{x}")?;
        }
        Ok(())
    }
}
