//! A lint: `(cons A (cons B … nil))`, a list written out pair by pair, where
//! `(list A B …)` says the same (the user's, 2026-09-29). Two pairs or more;
//! the last `cdr` is `nil`, perhaps ascribed, `(the T nil)`.
//!
//! `list` makes a `(listof T acyclic)`, so a chain whose pairs must be in
//! a region (`@k`, say, which goes when its computation ends, or one written
//! later) stays a chain. Such a chain is said so where it is written: its
//! own line, or the line before, carries `; cons-chain:` and the reason.

use crate::sexp_edit::line_col;
use fixpt_read::{Datum, FileId, Interner, Reader, Syntax, SyntaxProfile};

/// A chain of pairs ending in `nil`.
#[derive(Clone, Debug, PartialEq)]
pub struct Finding {
    pub line: usize,
    pub col: usize,
    /// How many elements: how many pairs.
    pub elements: usize,
}

/// What marks a chain kept on purpose.
pub const KEEP: &str = "; cons-chain:";

fn items(s: &Syntax) -> &[Syntax] {
    match &s.datum {
        Datum::List { items, .. } => items,
        _ => &[],
    }
}

struct Lint<'a> {
    i: &'a Interner,
    out: Vec<(usize, usize)>,
}

impl Lint<'_> {
    fn head_is(&self, e: &Syntax, name: &str) -> bool {
        items(e).first().and_then(|h| h.as_symbol()).is_some_and(|s| self.i.name(s) == name)
    }

    fn is_nil(&self, e: &Syntax) -> bool {
        match e.as_symbol() {
            Some(s) => self.i.name(s) == "nil",
            None => self.head_is(e, "the") && items(e).len() == 3 && self.is_nil(&items(e)[2]),
        }
    }

    /// How many pairs `e` is, if a chain of `cons` ending in `nil`.
    fn chain(&self, e: &Syntax) -> Option<usize> {
        if self.is_nil(e) {
            return Some(0);
        }
        let its = items(e);
        if !(self.head_is(e, "cons") && its.len() == 3) {
            return None;
        }
        self.chain(&its[2]).map(|n| n + 1)
    }

    fn scan(&mut self, e: &Syntax) {
        if let Some(n) = self.chain(e).filter(|n| *n >= 2) {
            self.out.push((e.span.start as usize, n));
            // Its elements may hold chains of their own.
            let mut rest = e;
            while self.head_is(rest, "cons") {
                self.scan(&items(rest)[1]);
                rest = &items(rest)[2];
            }
            return;
        }
        for x in items(e) {
            self.scan(x);
        }
    }
}

/// The chains in `text`, but for those marked kept.
pub fn cons_chains(text: &str, profile: SyntaxProfile) -> Result<Vec<Finding>, String> {
    let mut i = Interner::new();
    let forms = Reader::new(text, FileId(0), profile, &mut i).read_all().map_err(|e| {
        let (l, c) = line_col(text, e.span.start as usize);
        format!("{l}:{c}: {}", e.message)
    })?;
    let mut lint = Lint { i: &i, out: Vec::new() };
    for f in &forms {
        lint.scan(f);
    }
    let lines: Vec<&str> = text.lines().collect();
    let kept = |line: usize| {
        let at = |l: usize| l >= 1 && lines.get(l - 1).is_some_and(|s| s.contains(KEEP));
        at(line) || at(line - 1)
    };
    Ok(lint
        .out
        .into_iter()
        .map(|(at, elements)| {
            let (line, col) = line_col(text, at);
            Finding { line, col, elements }
        })
        .filter(|f| !kept(f.line))
        .collect())
}
