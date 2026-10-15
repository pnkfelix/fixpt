//! `(define-convention name clause …)` (`TODO.md` §97, `docs/research/
//! declared-conventions.md`): a declaration is accepted when its clauses,
//! each printed canonically and sorted by role, are those of a convention
//! this implementation supports, which today is fixpt's `native`
//! (`fixpt_runtime::NATIVE_CONVENTION`). The checker written in FX-26 does
//! the same (`check-program.fx`, `k-check-convention`), word for word.

use crate::error::{FxError, R};
use fixpt_read::{Datum, Num, Span, Sym, Syntax};

const ATOMS: &str = "a convention's clause holds names, integers and lists";

/// `s` printed as both checkers print a clause: atoms apart by one space,
/// integers in decimal.
fn text(s: &Syntax, name: &dyn Fn(Sym) -> String) -> R<String> {
    match &s.datum {
        // Not `#t`, `#f` or `#u`, which the reader written in FX-26 reads
        // as names.
        Datum::Symbol(x) if !name(*x).starts_with('#') => Ok(name(*x)),
        Datum::Number(Num::Int(n)) => Ok(n.to_string()),
        Datum::Nil => Ok("()".into()),
        Datum::List { items, tail: None } => {
            let parts: R<Vec<String>> = items.iter().map(|x| text(x, name)).collect();
            Ok(format!("({})", parts?.join(" ")))
        }
        _ => Err(FxError::at(s.span, ATOMS)),
    }
}

/// A supported clause's role: its first word.
fn role_of(clause: &str) -> &str {
    let rest = &clause[1..];
    &rest[..rest.find([' ', ')']).unwrap_or(rest.len())]
}

/// Whether `clauses`, the form at `span`'s, declare the native convention;
/// else why not, at the first clause, by role, that differs.
pub fn check(span: Span, clauses: &[Syntax], name: &dyn Fn(Sym) -> String) -> R<()> {
    let mut ours: Vec<(String, String, Span)> = Vec::new();
    for c in clauses {
        let role = match c.as_proper_list() {
            Some([h, ..]) if h.as_symbol().is_some_and(|x| !name(x).starts_with('#')) => name(h.as_symbol().expect("a symbol")),
            _ => return Err(FxError::at(c.span, "a convention's clause is `(role …)`")),
        };
        ours.push((role, text(c, name)?, c.span));
    }
    ours.sort_by(|a, b| a.0.cmp(&b.0));
    for w in ours.windows(2) {
        if w[0].0 == w[1].0 {
            return Err(FxError::at(w[1].2, format!("`define-convention`: two `{}` clauses", w[1].0)));
        }
    }
    let mut theirs: Vec<(&str, &str)> = fixpt_runtime::NATIVE_CONVENTION.lines().map(|l| (role_of(l), l)).collect();
    theirs.sort_by(|a, b| a.0.cmp(b.0));
    let (mut i, mut j) = (0, 0);
    while i < ours.len() || j < theirs.len() {
        match (ours.get(i), theirs.get(j)) {
            (Some(o), Some(t)) if o.0 == t.0 => {
                if o.1 != t.1 {
                    return Err(FxError::at(o.2, format!("`define-convention`: the `{}` clause is not this implementation's: {}", o.0, t.1)));
                }
                i += 1;
                j += 1;
            }
            (Some(o), t) if t.is_none_or(|t| o.0.as_str() < t.0) => {
                return Err(FxError::at(o.2, format!("`define-convention`: this implementation's convention has no `{}` clause", o.0)));
            }
            (_, Some(t)) => {
                return Err(FxError::at(span, format!("`define-convention`: no `{}` clause, which this implementation's convention has", t.0)));
            }
            (_, None) => unreachable!("one list has more"),
        }
    }
    Ok(())
}
