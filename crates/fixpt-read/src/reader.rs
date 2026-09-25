//! The reader: source text to spanned [`Syntax`], under a [`SyntaxProfile`].

use crate::datum::{Datum, Num, Syntax};
use crate::intern::Interner;
use crate::profile::{Brackets, SyntaxProfile, UnitSyntax};
use crate::span::{FileId, Span};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub struct ReadError {
    pub span: Span,
    pub message: String,
    /// The input simply stopped in the middle of a datum, rather than being
    /// wrong.
    ///
    /// The distinction is what lets an interactive reader tell "keep typing"
    /// from "that is a mistake" — and it has to come from the reader, because
    /// only the reader knows that the `)` inside `#| ) |#` or `|a(b|` is not a
    /// delimiter. A separate paren-counter in the REPL would have to duplicate
    /// every one of those rules, and would get them wrong.
    pub incomplete: bool,
}

impl ReadError {
    fn at(span: Span, message: impl Into<String>) -> ReadError {
        ReadError { span, message: message.into(), incomplete: false }
    }

    /// An error that more input could still fix.
    fn truncated(span: Span, message: impl Into<String>) -> ReadError {
        ReadError { span, message: message.into(), incomplete: true }
    }
}

/// Whether a piece of text is a whole form yet.
#[derive(Debug)]
pub enum FormStatus {
    /// Reads as zero or more complete data.
    Complete,
    /// Ran out in the middle of something; more input could complete it.
    Incomplete,
    /// Wrong in a way more input cannot fix.
    Invalid(ReadError),
}

/// Ask the real reader whether `text` is a complete form.
///
/// Used by the REPL to decide whether `Enter` submits or opens a new line. It
/// re-reads from the start each time, which is why no parser state has to be
/// kept between keystrokes: for a REPL-sized form that costs microseconds.
/// Symbols are interned into a scratch table so that probing half-typed input
/// leaves nothing behind.
pub fn form_status(text: &str, profile: SyntaxProfile) -> FormStatus {
    let mut interner = crate::Interner::new();
    match Reader::new(text, FileId(0), profile, &mut interner).read_all() {
        Ok(_) => FormStatus::Complete,
        Err(e) if e.incomplete => FormStatus::Incomplete,
        Err(e) => FormStatus::Invalid(e),
    }
}

impl std::fmt::Display for ReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for ReadError {}

pub type ReadResult<T> = Result<T, ReadError>;

pub struct Reader<'a> {
    src: &'a str,
    pos: usize,
    file: FileId,
    profile: SyntaxProfile,
    interner: &'a mut Interner,
    labels: HashMap<u64, Syntax>,
}

impl<'a> Reader<'a> {
    pub fn new(
        src: &'a str,
        file: FileId,
        profile: SyntaxProfile,
        interner: &'a mut Interner,
    ) -> Reader<'a> {
        Reader { src, pos: 0, file, profile, interner, labels: HashMap::new() }
    }

    /// Read every datum in the source.
    pub fn read_all(&mut self) -> ReadResult<Vec<Syntax>> {
        let mut out = Vec::new();
        while let Some(d) = self.read()? {
            out.push(d);
        }
        Ok(out)
    }

    /// How far the reader has consumed, in bytes.
    ///
    /// A port needs this: reading one datum from a buffered file has to know
    /// where the next one starts.
    pub fn position(&self) -> usize {
        self.pos
    }

    /// Start reading at `offset` rather than at the beginning.
    pub fn seek(&mut self, offset: usize) {
        self.pos = offset;
    }

    /// Read one datum, or `None` at end of input.
    pub fn read(&mut self) -> ReadResult<Option<Syntax>> {
        self.skip_atmosphere()?;
        if self.peek().is_none() {
            return Ok(None);
        }
        self.read_datum().map(Some)
    }

    // ------------------------------------------------------------- characters
    #[inline]
    fn peek(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }
    #[inline]
    fn peek2(&self) -> Option<char> {
        let mut it = self.src[self.pos..].chars();
        it.next();
        it.next()
    }
    #[inline]
    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        Some(c)
    }
    #[inline]
    fn span_from(&self, start: usize) -> Span {
        Span::new(self.file, start as u32, self.pos as u32)
    }
    #[inline]
    fn here(&self) -> Span {
        Span::new(self.file, self.pos as u32, self.pos as u32)
    }

    fn is_delimiter(&self, c: char) -> bool {
        match c {
            c if c.is_whitespace() => true,
            '(' | ')' | '"' | ';' | '\'' | '`' | ',' => true,
            '[' | ']' => self.profile.brackets != Brackets::SymbolChars,
            _ => false,
        }
    }

    // ------------------------------------------------------------- atmosphere
    fn skip_atmosphere(&mut self) -> ReadResult<()> {
        loop {
            match self.peek() {
                Some(c) if c.is_whitespace() => {
                    self.bump();
                }
                Some(';') => {
                    while let Some(c) = self.bump() {
                        if c == '\n' {
                            break;
                        }
                    }
                }
                Some('#') if self.profile.block_comments && self.peek2() == Some('|') => {
                    self.skip_block_comment()?;
                }
                Some('#') if self.profile.datum_comments && self.peek2() == Some(';') => {
                    self.pos += 2;
                    self.skip_atmosphere()?;
                    // Read and discard. Its side effects on datum labels are
                    // kept, matching R7RS's "the datum is read but ignored".
                    self.read_datum()?;
                }
                _ => return Ok(()),
            }
        }
    }

    fn skip_block_comment(&mut self) -> ReadResult<()> {
        let start = self.pos;
        self.pos += 2; // #|
        let mut depth = 1;
        while depth > 0 {
            match self.bump() {
                None => return Err(ReadError::truncated(self.span_from(start), "unterminated `#|` comment")),
                Some('|') if self.peek() == Some('#') => {
                    self.bump();
                    depth -= 1;
                }
                Some('#') if self.peek() == Some('|') => {
                    self.bump();
                    depth += 1;
                }
                _ => {}
            }
        }
        Ok(())
    }

    // ------------------------------------------------------------------ datum
    fn read_datum(&mut self) -> ReadResult<Syntax> {
        self.skip_atmosphere()?;
        let start = self.pos;
        let c = match self.peek() {
            None => return Err(ReadError::truncated(self.here(), "unexpected end of input")),
            Some(c) => c,
        };
        match c {
            '(' => {
                self.bump();
                self.read_list(start, ')', None)
            }
            '[' => match self.profile.brackets {
                Brackets::Parens => {
                    self.bump();
                    self.read_list(start, ']', None)
                }
                // `[e d…]` is `(proj e d…)`: reconstructed from report §2.4.9.
                Brackets::ProjSugar => {
                    self.bump();
                    let proj = self.interner.intern("proj");
                    self.read_list(start, ']', Some(proj))
                }
                Brackets::SymbolChars => self.read_atom(),
                Brackets::Reserved => {
                    self.bump();
                    Err(ReadError::at(self.span_from(start), "`[` is reserved: it has no meaning yet"))
                }
            },
            ']' if self.profile.brackets == Brackets::Reserved => {
                self.bump();
                Err(ReadError::at(self.span_from(start), "`]` is reserved: it has no meaning yet"))
            }
            ')' | ']' => {
                self.bump();
                Err(ReadError::at(self.span_from(start), format!("unbalanced `{c}`")))
            }
            '"' => self.read_string(),
            '#' => self.read_hash(),
            '\'' if self.profile.quote_sugar => self.read_abbrev(start, "quote"),
            '`' if self.profile.quote_sugar => self.read_abbrev(start, "quasiquote"),
            ',' if self.profile.quote_sugar => {
                if self.peek2() == Some('@') {
                    self.bump();
                    self.read_abbrev(start, "unquote-splicing")
                } else {
                    self.read_abbrev(start, "unquote")
                }
            }
            _ => self.read_atom(),
        }
    }

    fn read_abbrev(&mut self, start: usize, name: &str) -> ReadResult<Syntax> {
        self.bump();
        let sym = self.interner.intern(name);
        let inner = self.read_datum()?;
        let span = self.span_from(start);
        Ok(Syntax::list(span, vec![Syntax::symbol(Span::new(self.file, start as u32, start as u32 + 1), sym), inner]))
    }

    /// Read a list body up to `close`. `prefix`, when given, is prepended as
    /// the operator — that is what turns `[e d…]` into `(proj e d…)`.
    fn read_list(
        &mut self,
        start: usize,
        close: char,
        prefix: Option<crate::intern::Sym>,
    ) -> ReadResult<Syntax> {
        let mut items: Vec<Syntax> = Vec::new();
        if let Some(p) = prefix {
            items.push(Syntax::symbol(Span::new(self.file, start as u32, start as u32 + 1), p));
        }
        let mut tail: Option<Box<Syntax>> = None;
        loop {
            self.skip_atmosphere()?;
            match self.peek() {
                None => {
                    return Err(ReadError::truncated(
                        self.span_from(start),
                        format!("unterminated list, expected `{close}`"),
                    ));
                }
                Some(c) if c == close => {
                    self.bump();
                    break;
                }
                Some(']') if self.profile.brackets == Brackets::Reserved => {
                    let at = self.here();
                    self.bump();
                    return Err(ReadError::at(at, "`]` is reserved: it has no meaning yet"));
                }
                Some(c @ (')' | ']')) => {
                    let at = self.here();
                    self.bump();
                    return Err(ReadError::at(at, format!("expected `{close}` but found `{c}`")));
                }
                Some('.') if self.at_lone_dot() => {
                    if prefix.is_some() {
                        let at = self.here();
                        return Err(ReadError::at(at, "`.` is not allowed in `[…]` projection sugar"));
                    }
                    if items.is_empty() {
                        let at = self.here();
                        return Err(ReadError::at(at, "`.` must follow at least one element"));
                    }
                    let dot = self.here();
                    self.bump();
                    self.skip_atmosphere()?;
                    // Running out here is unfinished, not wrong: `(a .` can
                    // still become `(a . b)`.
                    if self.peek().is_none() {
                        return Err(ReadError::truncated(dot, "expected a datum after `.`"));
                    }
                    if self.peek() == Some(close) {
                        return Err(ReadError::at(dot, "expected a datum after `.`"));
                    }
                    tail = Some(Box::new(self.read_datum()?));
                    self.skip_atmosphere()?;
                    match self.peek() {
                        Some(c) if c == close => {
                            self.bump();
                            break;
                        }
                        None => {
                            return Err(ReadError::truncated(
                                self.here(),
                                format!("expected `{close}` after the tail of a dotted list"),
                            ));
                        }
                        _ => {
                            return Err(ReadError::at(
                                self.here(),
                                format!("expected `{close}` after the tail of a dotted list"),
                            ));
                        }
                    }
                }
                _ => items.push(self.read_datum()?),
            }
        }
        let span = self.span_from(start);
        if items.is_empty() && tail.is_none() {
            return Ok(Syntax::new(span, Datum::Nil));
        }
        Ok(Syntax::new(span, Datum::List { items, tail }))
    }

    /// A `.` that is the dotted-pair marker, rather than the start of `.5` or
    /// `...` or a symbol like `a.b`.
    fn at_lone_dot(&self) -> bool {
        debug_assert_eq!(self.peek(), Some('.'));
        let mut it = self.src[self.pos..].chars();
        it.next();
        match it.next() {
            None => true,
            Some(c) => self.is_delimiter(c),
        }
    }

    // ---------------------------------------------------------------- strings
    fn read_string(&mut self) -> ReadResult<Syntax> {
        let start = self.pos;
        self.bump(); // opening quote
        let mut s = String::new();
        loop {
            match self.bump() {
                None => {
                    return Err(ReadError::truncated(self.span_from(start), "unterminated string"));
                }
                Some('"') => break,
                Some('\\') => match self.bump() {
                    None => {
                        return Err(ReadError::truncated(self.span_from(start), "unterminated string escape"));
                    }
                    Some('n') => s.push('\n'),
                    Some('t') => s.push('\t'),
                    Some('r') => s.push('\r'),
                    Some('a') => s.push('\u{7}'),
                    Some('b') => s.push('\u{8}'),
                    Some('0') => s.push('\0'),
                    Some('\\') => s.push('\\'),
                    Some('"') => s.push('"'),
                    Some('x') | Some('X') => {
                        let mut hex = String::new();
                        while let Some(c) = self.peek() {
                            if c == ';' {
                                self.bump();
                                break;
                            }
                            if !c.is_ascii_hexdigit() {
                                return Err(ReadError::at(self.here(), "expected `;` after `\\x` escape"));
                            }
                            hex.push(c);
                            self.bump();
                        }
                        let n = u32::from_str_radix(&hex, 16)
                            .map_err(|_| ReadError::at(self.span_from(start), "bad `\\x` escape"))?;
                        s.push(char::from_u32(n).ok_or_else(|| {
                            ReadError::at(self.span_from(start), format!("{n:#x} is not a character"))
                        })?);
                    }
                    // `\<intraline ws><newline><intraline ws>` elides the break.
                    Some(c) if c == '\n' || c == ' ' || c == '\t' => {
                        let mut saw_newline = c == '\n';
                        while let Some(c) = self.peek() {
                            if c == '\n' && !saw_newline {
                                saw_newline = true;
                                self.bump();
                            } else if c == ' ' || c == '\t' {
                                self.bump();
                            } else {
                                break;
                            }
                        }
                        if !saw_newline {
                            s.push(c);
                        }
                    }
                    Some(c) => s.push(c),
                },
                Some(c) => s.push(c),
            }
        }
        Ok(Syntax::new(self.span_from(start), Datum::Str(s)))
    }

    // ------------------------------------------------------------- `#` syntax
    fn read_hash(&mut self) -> ReadResult<Syntax> {
        let start = self.pos;
        self.bump(); // '#'
        let c = self
            .peek()
            .ok_or_else(|| ReadError::truncated(self.span_from(start), "`#` at end of input"))?;
        match c {
            '(' => {
                self.bump();
                let inner = self.read_list(start, ')', None)?;
                let items = match inner.datum {
                    Datum::Nil => Vec::new(),
                    Datum::List { items, tail: None } => items,
                    Datum::List { .. } => {
                        return Err(ReadError::at(inner.span, "a vector cannot be a dotted list"));
                    }
                    _ => unreachable!("read_list yields Nil or List"),
                };
                Ok(Syntax::new(self.span_from(start), Datum::Vector(items)))
            }
            '\\' => self.read_char(start),
            't' | 'f' | 'T' | 'F' => self.read_boolean(start),
            'u' | 'U' => self.read_u(start),
            'b' | 'B' | 'o' | 'O' | 'd' | 'D' | 'x' | 'X' | 'e' | 'E' | 'i' | 'I' => {
                self.pos = start;
                self.read_atom()
            }
            '0'..='9' if self.profile.datum_labels => self.read_label(start),
            _ => {
                self.bump();
                Err(ReadError::at(self.span_from(start), format!("unknown `#` syntax: `#{c}`")))
            }
        }
    }

    fn read_boolean(&mut self, start: usize) -> ReadResult<Syntax> {
        let word = self.take_while(|c, r| !r.is_delimiter(c));
        let lower = word.to_ascii_lowercase();
        let value = match lower.as_str() {
            "t" | "true" => true,
            "f" | "false" => false,
            _ => {
                return Err(ReadError::at(
                    self.span_from(start),
                    format!("unknown `#` syntax: `#{word}`"),
                ));
            }
        };
        let span = self.span_from(start);
        if self.profile.booleans_are_symbols {
            // FX-87: `literal-bool?` tests membership in `(|#f| |#t|)`.
            let s = self.interner.intern(if value { "#t" } else { "#f" });
            Ok(Syntax::symbol(span, s))
        } else {
            Ok(Syntax::new(span, Datum::Bool(value)))
        }
    }

    fn read_u(&mut self, start: usize) -> ReadResult<Syntax> {
        let lone_u = {
            let mut ahead = self.src[self.pos..].chars();
            ahead.next();
            ahead.next().is_none_or(|c| self.is_delimiter(c))
        };
        match self.profile.unit {
            UnitSyntax::Symbol => self.read_unit(start),
            UnitSyntax::SymbolOrBytevector if lone_u => self.read_unit(start),
            UnitSyntax::Bytevector | UnitSyntax::SymbolOrBytevector => self.read_bytevector(start),
        }
    }

    fn read_unit(&mut self, start: usize) -> ReadResult<Syntax> {
        self.bump(); // 'u'
        let span = self.span_from(start);
        // The exact spelling matters: FX-91 needs `#U`, FX-87 `#u`.
        let s = self.interner.intern(self.profile.unit_name);
        Ok(Syntax::symbol(span, s))
    }

    fn read_bytevector(&mut self, start: usize) -> ReadResult<Syntax> {
        let word = self.take_while(|c, _| c == 'u' || c == 'U' || c.is_ascii_digit());
        if !word.eq_ignore_ascii_case("u8") {
            return Err(ReadError::at(
                self.span_from(start),
                format!("unknown `#` syntax: `#{word}`"),
            ));
        }
        if self.peek() != Some('(') {
            return Err(ReadError::at(self.here(), "expected `(` after `#u8`"));
        }
        self.bump();
        let inner = self.read_list(start, ')', None)?;
        let items: Vec<Syntax> = match inner.datum {
            Datum::Nil => Vec::new(),
            Datum::List { items, tail: None } => items,
            _ => return Err(ReadError::at(inner.span, "a bytevector cannot be dotted")),
        };
        let mut bytes = Vec::with_capacity(items.len());
        for item in items {
            match item.as_i64() {
                Some(n) if (0..=255).contains(&n) => bytes.push(n as u8),
                _ => {
                    return Err(ReadError::at(
                        item.span,
                        "bytevector elements must be exact integers in 0..=255",
                    ));
                }
            }
        }
        Ok(Syntax::new(self.span_from(start), Datum::Bytevector(bytes)))
    }

    fn read_label(&mut self, start: usize) -> ReadResult<Syntax> {
        let digits = self.take_while(|c, _| c.is_ascii_digit());
        let n: u64 = digits
            .parse()
            .map_err(|_| ReadError::at(self.span_from(start), "datum label is too large"))?;
        match self.bump() {
            Some('=') => {
                let d = self.read_datum()?;
                self.labels.insert(n, d.clone());
                Ok(d)
            }
            Some('#') => self
                .labels
                .get(&n)
                .cloned()
                .ok_or_else(|| ReadError::at(self.span_from(start), format!("undefined datum label `#{n}#`"))),
            _ => Err(ReadError::at(self.span_from(start), "expected `=` or `#` after a datum label")),
        }
    }

    fn read_char(&mut self, start: usize) -> ReadResult<Syntax> {
        self.bump(); // '\'
        let first = self
            .bump()
            .ok_or_else(|| ReadError::truncated(self.span_from(start), "`#\\` at end of input"))?;
        // A single character followed by a delimiter is that character, even
        // when it also starts a longer name (`#\s` is `s`, `#\space` is ` `).
        let rest = self.take_while(|c, r| !r.is_delimiter(c));
        let span = self.span_from(start);
        if rest.is_empty() {
            return Ok(Syntax::new(span, Datum::Char(first)));
        }
        let name: String = std::iter::once(first).chain(rest.chars()).collect();
        let lower = name.to_ascii_lowercase();
        let c = match lower.as_str() {
            "space" => ' ',
            "newline" | "linefeed" | "nl" => '\n',
            "tab" => '\t',
            "return" => '\r',
            "null" | "nul" => '\0',
            "alarm" => '\u{7}',
            "backspace" => '\u{8}',
            "delete" | "rubout" => '\u{7f}',
            "escape" | "altmode" | "esc" => '\u{1b}',
            _ if lower.starts_with('x') && lower.len() > 1 => {
                let n = u32::from_str_radix(&lower[1..], 16)
                    .map_err(|_| ReadError::at(span, format!("bad character name `#\\{name}`")))?;
                char::from_u32(n)
                    .ok_or_else(|| ReadError::at(span, format!("{n:#x} is not a character")))?
            }
            _ => return Err(ReadError::at(span, format!("unknown character name `#\\{name}`"))),
        };
        Ok(Syntax::new(span, Datum::Char(c)))
    }

    // ------------------------------------------------------------------ atoms
    fn take_while(&mut self, pred: impl Fn(char, &Self) -> bool) -> String {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if !pred(c, self) {
                break;
            }
            s.push(c);
            self.bump();
        }
        s
    }

    /// Read a symbol or a number. Which one it is can only be decided after the
    /// whole token is in hand: `+` is a symbol, `+1` is a number, `1+` is a
    /// symbol again.
    fn read_atom(&mut self) -> ReadResult<Syntax> {
        let start = self.pos;
        let mut text = String::new();
        // `escaped` records whether any part was written `|…|` or `\c`, which
        // suppresses case folding and forces a symbol interpretation.
        let mut escaped = false;
        loop {
            match self.peek() {
                None => break,
                Some('|') => {
                    escaped = true;
                    self.bump();
                    loop {
                        match self.bump() {
                            None => {
                                return Err(ReadError::truncated(
                                    self.span_from(start),
                                    "unterminated `|…|` symbol",
                                ));
                            }
                            Some('|') => break,
                            Some('\\') => {
                                if let Some(c) = self.bump() {
                                    text.push(c)
                                }
                            }
                            Some(c) => text.push(c),
                        }
                    }
                }
                Some('\\') => {
                    escaped = true;
                    self.bump();
                    if let Some(c) = self.bump() {
                        text.push(c);
                    }
                }
                Some(c) if self.is_delimiter(c) => break,
                Some(c) => {
                    text.push(c);
                    self.bump();
                }
            }
        }
        let span = self.span_from(start);
        if text.is_empty() && !escaped {
            let c = self.peek().unwrap_or('?');
            self.bump();
            return Err(ReadError::at(span, format!("unexpected `{c}`")));
        }
        if !escaped
            && let Some(n) = parse_number(&text, 10, None)
        {
            return Ok(Syntax::new(span, Datum::Number(n)));
        }
        let name = if self.profile.case_fold && !escaped { text.to_lowercase() } else { text };
        let s = self.interner.intern(&name);
        Ok(Syntax::symbol(span, s))
    }
}

// ------------------------------------------------------------------- numbers

/// Parse an R7RS number, or return `None` so the caller falls back to a symbol.
///
/// Prefixes (`#x`, `#e`, …) may appear in either order and are consumed here
/// rather than in the `#` dispatcher, because `#x-1f` is one token.
pub fn parse_number(text: &str, default_radix: u32, exact: Option<bool>) -> Option<Num> {
    let mut radix = default_radix;
    let mut exactness = exact;
    let mut rest = text;
    while let Some(stripped) = rest.strip_prefix('#') {
        let c = stripped.chars().next()?;
        match c.to_ascii_lowercase() {
            'b' => radix = 2,
            'o' => radix = 8,
            'd' => radix = 10,
            'x' => radix = 16,
            'e' => exactness = Some(true),
            'i' => exactness = Some(false),
            _ => return None,
        }
        rest = &stripped[c.len_utf8()..];
    }
    if rest.is_empty() {
        return None;
    }
    let n = parse_real(rest, radix)?;
    Some(match exactness {
        Some(false) => Num::Real(to_f64(&n)?),
        // Exactness coercion of an inexact literal needs the numeric tower;
        // the front end applies it, and `#e1.5` is rejected here for now.
        Some(true) if !n.is_exact() => return None,
        _ => n,
    })
}

fn parse_real(text: &str, radix: u32) -> Option<Num> {
    match text {
        "+inf.0" => return Some(Num::Real(f64::INFINITY)),
        "-inf.0" => return Some(Num::Real(f64::NEG_INFINITY)),
        "+nan.0" | "-nan.0" => return Some(Num::Real(f64::NAN)),
        _ => {}
    }
    if let Some((n, d)) = text.split_once('/') {
        let num = parse_integer(n, radix)?;
        let den = parse_integer(d, radix)?;
        return Some(Num::Ratio(Box::new(num), Box::new(den)));
    }
    if radix == 10 && text.contains(['.', 'e', 'E']) && !text.starts_with("...") {
        // Reject things like `1e` or `.` that `f64::from_str` would also
        // reject, and `1.2.3`, which it would not.
        if let Ok(x) = text.parse::<f64>() {
            return Some(Num::Real(x));
        }
        return None;
    }
    parse_integer(text, radix)
}

fn parse_integer(text: &str, radix: u32) -> Option<Num> {
    let (negative, digits) = match text.strip_prefix('-') {
        Some(d) => (true, d),
        None => (false, text.strip_prefix('+').unwrap_or(text)),
    };
    if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
        return None;
    }
    match i64::from_str_radix(text, radix) {
        Ok(n) => Some(Num::Int(n)),
        // Too wide for a machine word: hand the digits on rather than
        // truncating. The numeric layer builds the bignum.
        Err(_) => Some(Num::Big { negative, digits: digits.to_string(), radix }),
    }
}

fn to_f64(n: &Num) -> Option<f64> {
    Some(match n {
        Num::Int(i) => *i as f64,
        Num::Real(x) => *x,
        Num::Ratio(a, b) => to_f64(a)? / to_f64(b)?,
        Num::Big { negative, digits, radix } => {
            let mut acc = 0f64;
            for c in digits.chars() {
                acc = acc * (*radix as f64) + c.to_digit(*radix)? as f64;
            }
            if *negative { -acc } else { acc }
        }
    })
}

// --------------------------------------------------------------- tokenising

/// What a stretch of source is, for the purpose of showing it to someone.
///
/// Coarser than the reader's own distinctions, because it exists to be given a
/// colour rather than a meaning.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum TokenKind {
    Open,
    Close,
    /// `'`, `` ` ``, `,`, `,@`
    Quote,
    Str,
    Char,
    Number,
    Boolean,
    Symbol,
    /// `;…`, `#|…|#`, `#;`
    Comment,
    /// `#(`, `#u8(` and other dispatches that are not any of the above.
    Hash,
    Whitespace,
}

/// One token: a half-open byte range and what it is.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Token {
    pub start: usize,
    pub end: usize,
    pub kind: TokenKind,
}

/// Scan `text` into tokens.
///
/// This lives in the reader, with the reader's own notion of what a delimiter
/// is, because getting that wrong is how the REPL used to truncate
/// `(define (f x) #| ) |# x)`. A highlighter that counted for itself would
/// repeat the mistake in a quieter form — colouring the wrong parenthesis
/// rather than submitting the wrong form.
///
/// Unlike [`Reader::read`], this never fails: unterminated anything simply runs
/// to the end of the input, which is the normal state of a line being typed.
pub fn tokens(text: &str, profile: SyntaxProfile) -> Vec<Token> {
    let bytes: Vec<(usize, char)> = text.char_indices().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    let at = |i: usize| bytes.get(i).map(|(_, c)| *c);
    let offset = |i: usize| bytes.get(i).map_or(text.len(), |(o, _)| *o);

    let bracket_is_paren = profile.brackets != Brackets::SymbolChars;
    let is_delim = |c: char| match c {
        c if c.is_whitespace() => true,
        '(' | ')' | '"' | ';' | '\'' | '`' | ',' => true,
        '[' | ']' => bracket_is_paren,
        _ => false,
    };

    while i < bytes.len() {
        let start = i;
        let c = at(i).expect("in range");
        let kind = match c {
            c if c.is_whitespace() => {
                while at(i).is_some_and(|c| c.is_whitespace()) {
                    i += 1;
                }
                TokenKind::Whitespace
            }
            ';' => {
                while at(i).is_some_and(|c| c != '\n') {
                    i += 1;
                }
                TokenKind::Comment
            }
            '#' if profile.block_comments && at(i + 1) == Some('|') => {
                // Nested, as the reader nests them.
                i += 2;
                let mut depth = 1usize;
                while depth > 0 && i < bytes.len() {
                    if at(i) == Some('#') && at(i + 1) == Some('|') {
                        depth += 1;
                        i += 2;
                    } else if at(i) == Some('|') && at(i + 1) == Some('#') {
                        depth -= 1;
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                TokenKind::Comment
            }
            '#' if profile.datum_comments && at(i + 1) == Some(';') => {
                i += 2;
                TokenKind::Comment
            }
            '"' => {
                i += 1;
                while let Some(c) = at(i) {
                    i += 1;
                    match c {
                        '\\' => i += 1,
                        '"' => break,
                        _ => {}
                    }
                }
                TokenKind::Str
            }
            '#' if at(i + 1) == Some('\\') => {
                i += 2;
                // At least one character, then constituents.
                if at(i).is_some() {
                    i += 1;
                }
                while at(i).is_some_and(|c| !is_delim(c)) {
                    i += 1;
                }
                TokenKind::Char
            }
            '(' => {
                i += 1;
                TokenKind::Open
            }
            ')' => {
                i += 1;
                TokenKind::Close
            }
            '[' if bracket_is_paren => {
                i += 1;
                TokenKind::Open
            }
            ']' if bracket_is_paren => {
                i += 1;
                TokenKind::Close
            }
            '\'' | '`' => {
                i += 1;
                TokenKind::Quote
            }
            ',' => {
                i += 1;
                if at(i) == Some('@') {
                    i += 1;
                }
                TokenKind::Quote
            }
            '|' => {
                // `|a symbol|`, inside which a parenthesis is not a delimiter.
                i += 1;
                while let Some(c) = at(i) {
                    i += 1;
                    if c == '|' {
                        break;
                    }
                }
                TokenKind::Symbol
            }
            '#' => {
                i += 1;
                while at(i).is_some_and(|c| !is_delim(c)) {
                    i += 1;
                }
                let text = &text[offset(start)..offset(i)];
                if profile.booleans_are_symbols {
                    TokenKind::Symbol
                } else if matches!(text, "#t" | "#f" | "#true" | "#false") {
                    TokenKind::Boolean
                } else {
                    TokenKind::Hash
                }
            }
            _ => {
                while at(i).is_some_and(|c| !is_delim(c)) {
                    i += 1;
                }
                let word = &text[offset(start)..offset(i)];
                if parse_number(word, 10, None).is_some() {
                    TokenKind::Number
                } else {
                    TokenKind::Symbol
                }
            }
        };
        if i == start {
            // Never stall, whatever the input.
            i += 1;
        }
        out.push(Token { start: offset(start), end: offset(i), kind });
    }
    out
}

/// The token that closes or opens the one at `cursor`, if the text balances
/// there.
///
/// Only real delimiters count — a `)` inside a string, a comment or a
/// `|symbol|` is not one, which is precisely the knowledge a highlighter
/// cannot be trusted to reproduce for itself.
pub fn match_delimiter(toks: &[Token], cursor: usize) -> Option<(Token, Token)> {
    let here = toks.iter().position(|t| {
        matches!(t.kind, TokenKind::Open | TokenKind::Close) && t.start == cursor
    })?;
    let t = toks[here];
    match t.kind {
        TokenKind::Open => {
            let mut depth = 0i32;
            for u in &toks[here..] {
                match u.kind {
                    TokenKind::Open => depth += 1,
                    TokenKind::Close => {
                        depth -= 1;
                        if depth == 0 {
                            return Some((t, *u));
                        }
                    }
                    _ => {}
                }
            }
            None
        }
        TokenKind::Close => {
            let mut depth = 0i32;
            for u in toks[..=here].iter().rev() {
                match u.kind {
                    TokenKind::Close => depth += 1,
                    TokenKind::Open => {
                        depth -= 1;
                        if depth == 0 {
                            return Some((*u, t));
                        }
                    }
                    _ => {}
                }
            }
            None
        }
        _ => None,
    }
}
