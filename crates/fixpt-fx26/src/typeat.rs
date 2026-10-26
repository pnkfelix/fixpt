//! `type-at` (Heist's, `FIXPT-CHANGES.md` F3): what the checker says of a
//! program text at a place, for an editor written in FX-26 to show. The text
//! is checked by the checker written in Rust, keeping each expression's type
//! (`Checker::record_types`, as the verifier does), and the innermost
//! expression of the text itself (not of a file it loads) whose span holds
//! the place is given, with its type, as `%fx26-type-at` says it: `START END
//! TYPE`, or `error START END MESSAGE` for the first refusal, up to the
//! form the place is in (what follows it is not checked). Places are in
//! characters, as FX-26's strings count them; spans are bytes.

use crate::check::Checker;
use crate::top::Top;
use fixpt_read::FileId;

/// The byte offset of character `c` of `text` (its end, past the last).
fn byte_of(text: &str, c: i64) -> usize {
    if c <= 0 {
        return 0;
    }
    text.char_indices().nth(c as usize).map(|(b, _)| b).unwrap_or(text.len())
}

/// The character offset of byte `b` of `text`.
fn char_of(text: &str, b: usize) -> usize {
    text[..b.min(text.len())].chars().count()
}

pub fn type_at(text: &str, pos: i64) -> String {
    let mut c = Checker::new();
    c.record_types = true;
    let at = byte_of(text, pos);
    // Checked up to the form the place is in: a definition sees only those
    // before it, so what comes after cannot change the type there, and a
    // mistake further down should not hide it.
    let checked = (|| {
        let forms = c.read_in(FileId(0), text)?;
        let done = c.declare_ahead(&forms)?;
        for (f, done) in forms.iter().zip(done) {
            if !done {
                let _: Top = c.top(f)?;
            }
            if f.span.file == FileId(0) && f.span.end as usize >= at {
                break;
            }
        }
        Ok::<(), crate::FxError>(())
    })();
    if let Err(e) = checked {
        let (a, b) = if e.span.file == FileId(0) { (e.span.start as usize, e.span.end as usize) } else { (0, 0) };
        let message = e.message.lines().next().unwrap_or("").to_string();
        return format!("error {} {} {}", char_of(text, a), char_of(text, b), message);
    }
    let mut best: Option<(usize, usize, crate::ast::TyId)> = None;
    for (&e, &t) in c.facts.types.iter() {
        let span = c.arena.span_of(e);
        let (start, end) = (span.start as usize, span.end as usize);
        if span.file != FileId(0) || start > at || at > end {
            continue;
        }
        if best.is_none_or(|(a, b, _)| end - start < b - a) {
            best = Some((start, end, t));
        }
    }
    match best {
        Some((a, b, t)) => format!("{} {} {}", char_of(text, a), char_of(text, b), c.show_ty(t)),
        None => format!("error {pos} {pos} no expression here"),
    }
}
