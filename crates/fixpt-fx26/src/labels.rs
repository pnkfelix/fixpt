//! A sum's label written bare, `ok` where `#:ok` is meant: in a `sumof`'s
//! variants, `(sumof (ok T) …)`, and a `sum`'s construction, `(sum ok v)`.
//! Both spellings are one label (`docs/fx26.md`, "Keywords"), and types
//! print it as a keyword; a future version will take only the keyword
//! (the user's, 2026-11-26: so that a bare name there can come to mean a
//! constructor of its own, `docs/research/tagged-generatives.md` §5). Until
//! then the bare spelling is warned of, once a file, where the program's
//! file or a module file is read from source (the CLI's `run`, `eval` and
//! `check`; `Checker::parse_load_file`), never the standard environment's
//! or a built-in module's. Found by the text as written, not as expanded,
//! so that what a macro makes (`define-datatype`'s sum) is not the file's,
//! and quoted data is passed over.

use fixpt_read::{Datum, FileId, Interner, Reader, Syntax, SyntaxProfile};

/// The first bare label in `text`, an FX-26 file: where it starts (in
/// characters), its name, and how many more the file has; none if none, or
/// if the text does not read (its reading says why, elsewhere).
pub fn bare_labels(text: &str) -> Option<(usize, String, usize)> {
    let mut interner = Interner::default();
    let forms = Reader::new(text, FileId(0), SyntaxProfile::FX26, &mut interner).read_all().ok()?;
    let mut found = Vec::new();
    for f in &forms {
        walk(f, &interner, &mut found);
    }
    let (at, name) = found.first()?.clone();
    Some((at, name, found.len() - 1))
}

/// What is said of the first bare label `name` of a file that has `more`
/// besides.
pub fn bare_label_warning(name: &str, more: usize) -> String {
    let besides = match more {
        0 => String::new(),
        1 => ", and 1 more in this file".to_string(),
        n => format!(", and {n} more in this file"),
    };
    format!(
        "warning: a sum's label written `{name}`, not `#:{name}`{besides}: a future version will take a sum's label only as a keyword, as types print it, in `sumof`'s variants and `sum`'s constructions: write `#:{name}`"
    )
}

fn walk(s: &Syntax, interner: &Interner, found: &mut Vec<(usize, String)>) {
    let Datum::List { items, tail } = &s.datum else { return };
    let head = items.first().and_then(|h| match &h.datum {
        Datum::Symbol(n) => Some(interner.name(*n)),
        _ => None,
    });
    match head {
        Some("quote" | "quasiquote") => return,
        Some("sumof") => {
            for v in &items[1..] {
                if let Datum::List { items: parts, .. } = &v.datum
                    && let Some(Datum::Symbol(l)) = parts.first().map(|l| &l.datum)
                {
                    found.push((parts[0].span.start as usize, interner.name(*l).to_string()));
                }
            }
        }
        Some("sum") if items.len() >= 2 => {
            if let Datum::Symbol(l) = &items[1].datum {
                found.push((items[1].span.start as usize, interner.name(*l).to_string()));
            }
        }
        _ => {}
    }
    for x in items {
        walk(x, interner, found);
    }
    if let Some(t) = tail {
        walk(t, interner, found);
    }
}
