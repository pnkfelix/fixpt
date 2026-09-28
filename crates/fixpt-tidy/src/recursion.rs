//! A lint: a procedure that calls itself, not in tail position, stepping an
//! index (`(+ i 1)`, `(- i 1)`): a loop written as recursion, whose depth,
//! and so its stack, grows with its data. The assembler written in FX-26
//! listed its code so, once per instruction, and overflowed the data stack
//! at about 80,000 (`n-code-list`, 2026-09-28). A loop keeps what it has
//! made in an accumulator instead, and calls itself in tail position.

use crate::sexp_edit::line_col;
use fixpt_read::{Datum, FileId, Interner, Reader, Sym, Syntax, SyntaxProfile};

/// A self-call not in tail position that steps an index.
#[derive(Clone, Debug, PartialEq)]
pub struct Finding {
    /// The procedure calling itself.
    pub name: String,
    pub line: usize,
    pub col: usize,
}

fn items(s: &Syntax) -> &[Syntax] {
    match &s.datum {
        Datum::List { items, .. } => items,
        _ => &[],
    }
}

struct Lint<'a> {
    text: &'a str,
    i: &'a Interner,
    out: Vec<Finding>,
}

impl Lint<'_> {
    fn name(&self, s: &Syntax) -> Option<&str> {
        s.as_symbol().map(|x: Sym| self.i.name(x))
    }

    /// `e`, looking for bindings of procedures to names: `define`,
    /// `define-rec`'s members, `letrec`'s bindings.
    fn scan(&mut self, e: &Syntax) {
        let its = items(e);
        let head = its.first().and_then(|h| self.name(h)).unwrap_or("");
        match head {
            "define" | "define*" if its.len() >= 3 => {
                if let Some(n) = its.get(1).and_then(|n| self.name(n)).map(str::to_string) {
                    self.procedure(&n, its.last().expect("an init"));
                }
            }
            "define-rec" | "letrec" => {
                let bindings: &[Syntax] = if head == "letrec" { its.get(1).map_or(&[], items) } else { &its[1..] };
                for b in bindings {
                    let parts = items(b);
                    if let (Some(n), Some(init)) = (parts.first().and_then(|n| self.name(n)).map(str::to_string), parts.last()) {
                        self.procedure(&n, init);
                    }
                }
            }
            _ => {}
        }
        for x in its {
            self.scan(x);
        }
    }

    /// `init` bound to `name`: a lambda's body, looked through for self-calls.
    fn procedure(&mut self, name: &str, init: &Syntax) {
        let mut e = init;
        loop {
            let its = items(e);
            match its.first().and_then(|h| self.name(h)) {
                Some("plambda" | "the") if its.len() >= 3 => e = &its[2],
                Some("lambda") if its.len() >= 3 => {
                    let params: Vec<String> = items(&its[1])
                        .iter()
                        .filter_map(|p| self.name(p).or_else(|| items(p).first().and_then(|n| self.name(n))).map(str::to_string))
                        .collect();
                    for (k, b) in its[2..].iter().enumerate() {
                        self.visit(name, &params, b, k + 3 == its.len());
                    }
                    return;
                }
                _ => return,
            }
        }
    }

    /// Whether `a` steps one of `params` by a constant.
    fn steps(&self, params: &[String], a: &Syntax) -> bool {
        let its = items(a);
        matches!(its.first().and_then(|h| self.name(h)), Some("+" | "-"))
            && its.len() == 3
            && its[1..].iter().any(|x| self.name(x).is_some_and(|n| params.iter().any(|p| p == n)))
            && its[1..].iter().any(|x| matches!(x.datum, Datum::Number(_)))
    }

    fn visit(&mut self, name: &str, params: &[String], e: &Syntax, tail: bool) {
        let its = items(e);
        if its.is_empty() {
            return;
        }
        let head = self.name(&its[0]).unwrap_or("");
        let last = its.len() - 1;
        match head {
            // A new procedure: its calls are its own.
            "lambda" | "plambda" | "rlambda" | "quote" => {}
            "if" => {
                for (k, x) in its[1..].iter().enumerate() {
                    self.visit(name, params, x, tail && k > 0);
                }
            }
            "begin" | "and" | "or" => {
                for (k, x) in its.iter().enumerate().skip(1) {
                    self.visit(name, params, x, tail && k == last);
                }
            }
            "let" | "let*" | "letrec" => {
                for b in its.get(1).map_or(&[][..], items) {
                    if let Some(init) = items(b).last() {
                        self.visit(name, params, init, false);
                    }
                }
                for (k, x) in its.iter().enumerate().skip(2) {
                    self.visit(name, params, x, tail && k == last);
                }
            }
            "letregion" | "letrena" | "letreap" | "letfreeze" => {
                for (k, x) in its.iter().enumerate().skip(2) {
                    self.visit(name, params, x, tail && k == last);
                }
            }
            "the" => {
                if let Some(x) = its.get(2) {
                    self.visit(name, params, x, tail);
                }
            }
            "cond" => {
                for clause in &its[1..] {
                    let c = items(clause);
                    for (k, x) in c.iter().enumerate() {
                        self.visit(name, params, x, tail && k > 0 && k + 1 == c.len());
                    }
                }
            }
            "tagcase" => {
                if let Some(s) = its.get(1) {
                    self.visit(name, params, s, false);
                }
                for arm in &its[2..] {
                    if let Some(body) = items(arm).last() {
                        self.visit(name, params, body, tail);
                    }
                }
            }
            _ => {
                // Only an index changes: every argument a parameter as it
                // is, or one stepped, or a constant. A call that also passes
                // a part of its data (a tree walked, keeping a depth) is not
                // a loop.
                let is_param = |a: &Syntax| self.name(a).is_some_and(|n| params.iter().any(|p| p == n));
                let only_index = its[1..].iter().all(|a| is_param(a) || self.steps(params, a) || matches!(a.datum, Datum::Number(_)));
                if head == name && !tail && only_index && its[1..].iter().any(|a| self.steps(params, a)) {
                    let (line, col) = line_col(self.text, e.span.start as usize);
                    self.out.push(Finding { name: name.to_string(), line, col });
                }
                for x in its {
                    self.visit(name, params, x, false);
                }
            }
        }
    }
}

/// Every self-call in `text` not in tail position that steps an index.
pub fn index_recursion(text: &str, profile: SyntaxProfile) -> Result<Vec<Finding>, String> {
    let mut i = Interner::new();
    let forms = Reader::new(text, FileId(0), profile, &mut i).read_all().map_err(|e| {
        let (l, c) = line_col(text, e.span.start as usize);
        format!("{l}:{c}: {}", e.message)
    })?;
    let mut lint = Lint { text, i: &i, out: Vec::new() };
    for f in &forms {
        lint.scan(f);
    }
    Ok(lint.out)
}
