//! Loading the standard environment.
//!
//! `standard.fx` is generated from the reference — see
//! `reference/fx87-stdenv.rkt` — and holds the three tables the 1987
//! implementation starts with:
//!
//! * `k-env`, the kind of each description constructor;
//! * `d-store`, what each one *denotes*, which is where `listof` turns out to
//!   be a `dlambda` over a recursive pair type;
//! * `t-env`, the type and region of each value binding, all 183 of them.
//!
//! It is read with this crate's own parser rather than being built in Rust, so
//! the types are the reference's syntax rather than a transcription of it.

use crate::ast::{Desc, DescId, Kind};
use crate::env::{TkEnv, ValueBinding};
use crate::error::{FxError, R};
use crate::eval::DStore;
use crate::parse::{DScope, Parser};
use fixpt_read::{Datum, Reader, SourceMap, Syntax, SyntaxProfile};

pub const SOURCE: &str = include_str!("standard.fx");

pub struct Standard {
    pub env: TkEnv,
    pub store: DStore,
}

/// Read `standard.fx` into an environment, using `parser`'s interner.
pub fn load(parser: &mut Parser) -> R<Standard> {
    let mut sources = SourceMap::new();
    let file = sources.add("standard.fx", SOURCE);
    let forms = {
        let mut interner = std::mem::take(&mut parser.interner);
        let result = Reader::new(SOURCE, file, SyntaxProfile::FX87, &mut interner).read_all();
        parser.interner = interner;
        result.map_err(|e| FxError::internal(e.span, format!("standard.fx: {}", e.message)))?
    };

    let mut env = TkEnv::new();
    let mut store = DStore::new();
    // Each section is read in turn, and the order matters: `d-store` entries
    // may mention constructors that `k-env` introduced, and `t-env` types
    // mention both.
    let mut kinds: Vec<(fixpt_read::Sym, Kind)> = Vec::new();
    for form in &forms {
        let Datum::List { items, .. } = &form.datum else {
            return Err(FxError::internal(form.span, "standard.fx: expected a section"));
        };
        let Some(Datum::Symbol(head)) = items.first().map(|s| &s.datum) else {
            return Err(FxError::internal(form.span, "standard.fx: unnamed section"));
        };
        let name = parser.interner.name(*head).to_string();
        match name.as_str() {
            "k-env" => {
                for entry in &items[1..] {
                    let (n, k) = kind_entry(parser, entry)?;
                    kinds.push((n, k));
                }
            }
            "d-store" => {
                for entry in &items[1..] {
                    let (n, d) = store_entry(parser, entry)?;
                    store.insert(n, d);
                }
            }
            "t-env" => {
                for entry in &items[1..] {
                    let (n, b) = value_entry(parser, entry)?;
                    env.bind_value(n, b);
                }
            }
            other => {
                return Err(FxError::internal(
                    form.span,
                    format!("standard.fx: unknown section {other}"),
                ));
            }
        }
    }
    for (n, k) in kinds {
        env.bind_desc(n, k);
    }
    Ok(Standard { env, store })
}

fn parts(form: &Syntax, n: usize) -> R<&[Syntax]> {
    match &form.datum {
        Datum::List { items, tail } if tail.is_none() && items.len() == n => Ok(items),
        _ => Err(FxError::internal(form.span, format!("standard.fx: expected {n} elements"))),
    }
}

fn symbol(parser: &mut Parser, form: &Syntax) -> R<fixpt_read::Sym> {
    match &form.datum {
        Datum::Symbol(s) => Ok(*s),
        // The table really does contain a binding whose name is `()` — the
        // empty list literal, of type `null`. It is not reachable by writing a
        // variable, but it has to load.
        Datum::Nil => Ok(parser.interner.intern("()")),
        _ => Err(FxError::internal(form.span, "standard.fx: expected a name")),
    }
}

fn kind_entry(parser: &mut Parser, form: &Syntax) -> R<(fixpt_read::Sym, Kind)> {
    let p = parts(form, 2)?.to_vec();
    let name = symbol(parser, &p[0])?;
    Ok((name, parser.parse_kind(&p[1])?))
}

fn store_entry(parser: &mut Parser, form: &Syntax) -> R<(fixpt_read::Sym, DescId)> {
    let p = parts(form, 2)?.to_vec();
    let name = symbol(parser, &p[0])?;
    Ok((name, parser.parse_desc(&p[1], &DScope::default())?))
}

fn value_entry(parser: &mut Parser, form: &Syntax) -> R<(fixpt_read::Sym, ValueBinding)> {
    let p = parts(form, 3)?.to_vec();
    let name = symbol(parser, &p[0])?;
    let ty = parser.parse_desc(&p[1], &DScope::default())?;
    let region = parser.parse_desc(&p[2], &DScope::default())?;
    let _ = Desc::Pure;
    Ok((name, ValueBinding { ty, region }))
}
