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
    /// `#(x …)`, in a quote's constant.
    Vector(Vec<Sx>),
    /// `#:name`, in a quote's constant.
    Keyword(String),
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
            Sx::Vector(items) => Datum::Vector(items.iter().map(|x| x.syntax(interner, span)).collect()),
            Sx::Keyword(s) => Datum::Keyword(interner.intern(s)),
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
            Sx::Vector(items) => {
                f.write_str("#(")?;
                for (i, x) in items.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    write!(f, "{x}")?;
                }
                f.write_str(")")
            }
            Sx::Keyword(s) => write!(f, "#:{}", fixpt_read::escape_symbol(s)),
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

    /// As bytes, for a cache (`session.rs`'s `load_lowered`): each piece
    /// exactly, a float by its bits; read back by [`Code::decode`].
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        put_len(&mut out, self.0.len());
        for x in &self.0 {
            x.encode(&mut out);
        }
        out
    }

    /// What [`Code::encode`] made of some code: that code; none if `bytes`
    /// are not all of one.
    pub fn decode(bytes: &[u8]) -> Option<Code> {
        let mut at = 0;
        let n = get_len(bytes, &mut at)?;
        let mut xs = Vec::with_capacity(n.min(bytes.len()));
        for _ in 0..n {
            xs.push(Sx::decode(bytes, &mut at)?);
        }
        (at == bytes.len()).then_some(Code(xs))
    }
}

impl Sx {
    fn encode(&self, out: &mut Vec<u8>) {
        let text = |out: &mut Vec<u8>, tag: u8, s: &str| {
            out.push(tag);
            put_len(out, s.len());
            out.extend(s.as_bytes());
        };
        let items = |out: &mut Vec<u8>, xs: &[Sx]| {
            put_len(out, xs.len());
            for x in xs {
                x.encode(out);
            }
        };
        match self {
            Sx::Sym(s) => text(out, 0, s),
            Sx::Int(n) => {
                out.push(1);
                out.extend(n.to_le_bytes());
            }
            Sx::Float(x) => {
                out.push(2);
                out.extend(x.to_bits().to_le_bytes());
            }
            Sx::Str(s) => text(out, 3, s),
            Sx::Char(c) => {
                out.push(4);
                out.extend((*c as u32).to_le_bytes());
            }
            Sx::Bool(b) => out.push(if *b { 6 } else { 5 }),
            Sx::List(xs) => {
                out.push(7);
                items(out, xs);
            }
            Sx::Dotted(xs, tail) => {
                out.push(8);
                items(out, xs);
                tail.encode(out);
            }
            Sx::Vector(xs) => {
                out.push(9);
                items(out, xs);
            }
            Sx::Keyword(s) => text(out, 10, s),
        }
    }

    fn decode(bytes: &[u8], at: &mut usize) -> Option<Sx> {
        let tag = *bytes.get(*at)?;
        *at += 1;
        let take = |at: &mut usize, n: usize| -> Option<&[u8]> {
            let b = bytes.get(*at..at.checked_add(n)?)?;
            *at += n;
            Some(b)
        };
        let text = |at: &mut usize| -> Option<String> {
            let n = get_len(bytes, at)?;
            String::from_utf8(take(at, n)?.to_vec()).ok()
        };
        let items = |at: &mut usize| -> Option<Vec<Sx>> {
            let n = get_len(bytes, at)?;
            let mut xs = Vec::with_capacity(n.min(bytes.len()));
            for _ in 0..n {
                xs.push(Sx::decode(bytes, at)?);
            }
            Some(xs)
        };
        Some(match tag {
            0 => Sx::Sym(text(at)?),
            1 => Sx::Int(i128::from_le_bytes(take(at, 16)?.try_into().ok()?)),
            2 => Sx::Float(f64::from_bits(u64::from_le_bytes(take(at, 8)?.try_into().ok()?))),
            3 => Sx::Str(text(at)?),
            4 => Sx::Char(char::from_u32(u32::from_le_bytes(take(at, 4)?.try_into().ok()?))?),
            5 => Sx::Bool(false),
            6 => Sx::Bool(true),
            7 => Sx::List(items(at)?),
            8 => {
                let xs = items(at)?;
                Sx::Dotted(xs, Box::new(Sx::decode(bytes, at)?))
            }
            9 => Sx::Vector(items(at)?),
            10 => Sx::Keyword(text(at)?),
            _ => return None,
        })
    }
}

fn put_len(out: &mut Vec<u8>, n: usize) {
    out.extend((n as u64).to_le_bytes());
}

fn get_len(bytes: &[u8], at: &mut usize) -> Option<usize> {
    let b = bytes.get(*at..*at + 8)?;
    *at += 8;
    usize::try_from(u64::from_le_bytes(b.try_into().ok()?)).ok()
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
