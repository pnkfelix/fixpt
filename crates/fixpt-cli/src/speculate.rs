//! Checking a form while it is still being typed.
//!
//! The FX dialects can say a great deal about a form before it runs — its type
//! and effect — and the checkers are pure Rust, so asking costs nothing anyone
//! could notice. This module turns half-typed text into something a checker
//! can be asked about, and decides which of its complaints to believe.
//!
//! **Closing off.** An unfinished form is closed with the delimiters it is
//! missing, and a token still being typed at the end — `vec` on the way to
//! `vector-ref`, an unterminated string — is left out, so that the checker
//! never sees a half-typed name. What is left is a complete form made of
//! exactly what has been finished.
//!
//! **Believing errors.** Closing off manufactures errors of its own: `(if`
//! becomes `(if)`, which has no test. So an error is reported only when its
//! span lies wholly inside what was typed *and* contains none of the lists
//! that were closed off here — that is, when it is about a subform the user
//! has already finished. `(+ 1 (car 5)` reports `(car 5)` at once; the outer
//! `+`, still open, is not judged.
//!
//! **The hole at the cursor.** The innermost open list, with a `,help` hole
//! where the next argument goes, is what the static `,help` already answers —
//! so the answer can be shown continuously, as a hint, instead of on request.

use fixpt_read::{SyntaxProfile, TokenKind};

/// Half-typed text, made checkable.
#[derive(Debug, PartialEq, Eq)]
pub struct Partial {
    /// What was typed, less any token still in progress, with every open list
    /// closed.
    pub closed: String,
    /// How many bytes of the text were kept.
    pub kept: usize,
    /// Byte offsets of the open delimiters that were closed off here.
    pub open_at: Vec<usize>,
    /// The innermost open list, with a `,help` hole where the next argument
    /// goes: `(f a b ,help)`. `None` when no list is open, or when the hole
    /// would be the operator.
    pub hole_form: Option<String>,
}

impl Partial {
    /// Whether nothing was closed off or left out: the text was finished.
    pub fn finished(&self, text: &str) -> bool {
        self.open_at.is_empty() && self.kept == text.len()
    }

    /// Whether an error at bytes `start..end` of `closed` is about something
    /// the user has finished typing.
    pub fn believe(&self, start: usize, end: usize) -> bool {
        start < end && end <= self.kept && !self.open_at.iter().any(|&p| start <= p && p < end)
    }
}

/// Make `text` checkable, or `None` if it is not worth trying: nothing typed,
/// an unmatched closer (the reader will report that), or a `load`, which in
/// FX-91 reads a file *while checking* and so must not be done speculatively.
pub fn partial(text: &str, profile: SyntaxProfile) -> Option<Partial> {
    let toks = fixpt_read::tokens(text, profile);
    if toks.iter().any(|t| {
        t.kind == TokenKind::Symbol && text[t.start..t.end].eq_ignore_ascii_case("load")
    }) {
        return None;
    }
    // A token still being typed: anything that runs to the very end of the
    // text without a delimiter after it, or a string or block comment that
    // has not been closed, or a quote waiting for its datum.
    let mut kept = text.len();
    if let Some(last) = toks.iter().rev().find(|t| t.kind != TokenKind::Whitespace)
        && last.end == text.len()
    {
        let body = &text[last.start..last.end];
        let in_progress = match last.kind {
            TokenKind::Symbol | TokenKind::Number | TokenKind::Boolean | TokenKind::Char | TokenKind::Hash => true,
            TokenKind::Quote => true,
            TokenKind::Str => body.len() < 2 || !body.ends_with('"') || body.ends_with("\\\""),
            TokenKind::Comment => body.starts_with("#|") && !body.ends_with("|#"),
            _ => false,
        };
        if in_progress {
            kept = last.start;
        }
    }
    let mut stack: Vec<(usize, char)> = Vec::new();
    for t in toks.iter().filter(|t| t.end <= kept) {
        match t.kind {
            TokenKind::Open => {
                let close = if text[t.start..].starts_with('[') { ']' } else { ')' };
                stack.push((t.start, close));
            }
            TokenKind::Close => {
                stack.pop()?;
            }
            _ => {}
        }
    }
    let typed = &text[..kept];
    if typed.trim().is_empty() {
        return None;
    }
    let closers: String = stack.iter().rev().map(|&(_, c)| c).collect();
    let closed = format!("{typed}{closers}");
    let hole_form = stack.last().and_then(|&(at, close)| {
        let inner = &text[at..kept];
        // Just the open delimiter: the hole would be the operator.
        if inner[1..].trim().is_empty() {
            return None;
        }
        // Inside a quoted list the forms are data, not calls.
        let quoted = toks
            .iter()
            .rev()
            .find(|t| t.end <= at && t.kind != TokenKind::Whitespace)
            .is_some_and(|t| t.kind == TokenKind::Quote);
        (!quoted).then(|| format!("{} ,help{close}", inner.trim_end()))
    });
    Some(Partial {
        closed,
        kept,
        open_at: stack.iter().map(|&(p, _)| p).collect(),
        hole_form,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    const P: SyntaxProfile = SyntaxProfile::FX87;

    #[test]
    fn open_lists_are_closed_and_a_token_in_progress_is_left_out() {
        // `vec` is still being typed; the `(` before it is finished, and open.
        let p = partial("(+ 1 (car 5) (vec", P).expect("checkable");
        assert_eq!(p.closed, "(+ 1 (car 5) ())");
        assert_eq!(p.kept, "(+ 1 (car 5) (".len());
        assert_eq!(p.open_at, vec![0, 13]);
        assert_eq!(p.hole_form, None, "the hole would be the operator");
        // A token in progress is where the hole goes: typing `1` is typing
        // the second argument.
        let p = partial("(+ 1 (car 5) 1", P).expect("checkable");
        assert_eq!(p.closed, "(+ 1 (car 5) )");
        assert_eq!(p.hole_form.as_deref(), Some("(+ 1 (car 5) ,help)"));
    }

    #[test]
    fn only_finished_subforms_are_judged() {
        let text = "(+ 1 (car 5) ";
        let p = partial(text, P).expect("checkable");
        // `(car 5)` is finished.
        assert!(p.believe(5, 12));
        // The whole `(+ …` is not: it contains the open delimiter at 0.
        assert!(!p.believe(0, p.closed.len()));
        // Nothing in the closers the checker was given.
        assert!(!p.believe(12, p.closed.len()));
    }

    #[test]
    fn a_finished_form_is_left_alone() {
        let p = partial("(car 5)", P).expect("checkable");
        assert!(p.finished("(car 5)"));
        assert_eq!(p.closed, "(car 5)");
        assert_eq!(p.hole_form, None);
    }

    #[test]
    fn strings_and_quotes_in_progress() {
        assert_eq!(partial("(f \"abc", P).expect("checkable").closed, "(f )");
        assert_eq!(partial("(f '", P).expect("checkable").closed, "(f )");
        assert_eq!(partial("(f \"a\" x", P).expect("checkable").closed, "(f \"a\" )");
    }

    #[test]
    fn some_texts_are_not_worth_checking() {
        assert_eq!(partial("", P), None);
        assert_eq!(partial("   ", P), None);
        assert_eq!(partial("a)", P), None);
        assert_eq!(partial("(load \"x.fx\")", P), None, "`load` reads files while checking");
        // No hint for a hole in operator position, or in quoted data.
        assert_eq!(partial("(", P).and_then(|p| p.hole_form), None);
        assert_eq!(partial("'(a b ", P).and_then(|p| p.hole_form), None);
    }
}
