//! Reading FX-26 with the reader written in FX-26 (`eager-reader.fx`), and
//! turning what it read into the Rust checker's syntax.
//!
//! The reader builds `syn` values, a `define-datatype`: each piece of what
//! it read with where it starts and ends. At run time they are frozen
//! bloblets, a sum's tag and its product, so they can be walked here without
//! running anything. Positions are in characters there and in bytes in
//! [`Span`], and are converted with the text.

use crate::error::{FxError, R};
use crate::session::READER_PREFIX;
use fixpt_heap::Value;
use fixpt_read::{Datum, FileId, Interner, Num, Span, Syntax};
use fixpt_scheme::{Handle, Local, Session};
use fixpt_scheme::eager::EagerReader;

/// Read `text` with the FX-26 reader, already loaded into `scheme` (see
/// [`crate::session::load_eager_reader`]), interning names in `interner`.
pub fn read_with_fx26_reader(scheme: &mut Session, interner: &mut Interner, file: FileId, text: &str) -> R<Vec<Syntax>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let mut reader =
        EagerReader::attach_starting(scheme, READER_PREFIX, "eager-start-fx26").map_err(|e| fail(e.to_string()))?;
    scheme.scope(|s| {
        // As though Enter were pressed: a newline ends a trailing atom.
        let st = reader.state_after(s, text, true).map_err(|e| fail(e.to_string()))?;
        let call = |s: &mut Session, name: &str| {
            s.call_global(&format!("{READER_PREFIX}{name}"), &[st]).map_err(|e| fail(e.to_string()))
        };
        let offsets = byte_offsets(text);
        let at = |c: i64| offsets.get(c as usize).copied().unwrap_or(text.len()) as u32;
        let status = call(s, "eager-status")?;
        match s.view(|v| v.get(status).symbol_name()).as_deref() {
            Some("complete") => {}
            Some("error") => {
                let pos = call(s, "eager-state-position")?;
                let msg = call(s, "eager-state-message")?;
                return Err(s.view(|v| {
                    let pos = v.get(pos).fixnum().unwrap_or(0);
                    FxError::at(Span::new(file, at(pos), at(pos)), v.get(msg).string().unwrap_or_default())
                }));
            }
            _ => {
                return Err(FxError::at(Span::new(file, text.len() as u32, text.len() as u32), "the text ends in the middle of a form"));
            }
        }
        let syns = call(s, "eager-state-syntax")?;
        s.view(|v| {
            let items = v.get(syns).list().expect("a list");
            items.into_iter().map(|x| to_syntax(interner, file, &at, x)).collect()
        })
    })
}

/// Parse `text` with the reader and the parser written in FX-26: each
/// top-level form's tree, as [`crate::sexp::show_value`] prints it.
pub fn parse_with_fx26_parser(scheme: &mut Session, file: FileId, text: &str) -> R<Vec<String>> {
    scheme.scope(|s| {
        let tops = parse_to_trees(s, file, text)?;
        Ok(s.view(|v| v.get(tops).list().expect("a list").into_iter().map(crate::sexp::show_value).collect()))
    })
}

/// Read, parse, and run `text` with the evaluator written in FX-26: its
/// value as Scheme would write it, or `!! ` and its error.
pub fn eval_with_fx26_evaluator(scheme: &mut Session, file: FileId, text: &str) -> R<String> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    scheme.scope(|s| {
        let tops = parse_to_trees(s, file, text)?;
        let out = s.call_global(&format!("{READER_PREFIX}run-program"), &[tops]).map_err(|e| fail(e.to_string()))?;
        Ok(s.view(|v| v.get(out).string().unwrap_or_default()))
    })
}

/// Read, parse and compile `text` with the reader, the parser and the
/// compiler written in FX-26, and run the word it makes on the threaded
/// machine: the value, as Scheme writes it; or `!! ` and why it failed.
pub fn compile_with_fx26_compiler(scheme: &mut Session, standard: Handle, file: FileId, text: &str) -> R<String> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    scheme.scope(|s| {
        let tops = parse_to_trees(s, file, text)?;
        // Checked first, by the checker written in FX-26, which says where
        // each `extract`'s field is.
        let checked = s.call_global(&format!("{READER_PREFIX}check-program"), &[standard, tops]).map_err(|e| fail(e.to_string()))?;
        if let Some(m) = s.view(|v| {
            let r = v.get(checked);
            (r.field(2).and_then(|t| t.symbol_name()).as_deref() == Some("k-err"))
                .then(|| r.field(3).and_then(|p| p.field(2)).and_then(|m| m.string()).unwrap_or_default())
        }) {
            return Ok(format!("!! check: {m}"));
        }
        let facts = s.call_global(&format!("{READER_PREFIX}checked-extracts"), &[]).map_err(|e| fail(e.to_string()))?;
        let result = s.call_global(&format!("{READER_PREFIX}compile-program"), &[tops, facts]).map_err(|e| fail(e.to_string()))?;
        let (tag, word) = s.view(|v| {
            let r = v.get(result);
            let tag = r.field(2).and_then(|t| t.symbol_name()).unwrap_or_default();
            let payload = r.field(3).expect("a sum");
            (tag, payload.field(2).map(|x| x.string()))
        });
        if tag == "c-err" {
            return Ok(format!("!! compile: {}", word.flatten().unwrap_or_default()));
        }
        let word = s.make(|m| {
            let r = m.get(result);
            let payload = m.heap().bloblet_slot(r, 3);
            m.heap().bloblet_slot(payload, 2)
        });
        let no_args = s.make(|_| Value::NULL);
        match s.call_global("%run-word", &[word, no_args]) {
            Ok(v) => Ok(s.write(v)),
            Err(e) => Ok(format!("!! {}", e.to_string().trim_start_matches("error: threaded word: "))),
        }
    })
}

/// What the checker written in FX-26 made of a program: for each definition
/// and expression, in order, `define name : type ! effect` or `type !
/// effect`; or its first error.
pub type Checked26 = Result<Vec<String>, FxError>;

/// Read, parse and check `text` with the reader, the parser and the checker
/// written in FX-26, in the initial environment of [`crate::standard`].
/// The outer error is the front end failing to read or parse.
pub fn check_with_fx26_checker(scheme: &mut Session, standard: Handle, file: FileId, text: &str) -> R<Checked26> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    // With `FIXPT_TIME_PHASES` set, how long each phase took.
    let timing = std::env::var_os("FIXPT_TIME_PHASES").is_some();
    let started = std::time::Instant::now();
    let phase = |name: &str| {
        if timing {
            eprintln!("check-program: {name} at {:.3} s", started.elapsed().as_secs_f64());
        }
    };
    scheme.scope(|s| {
        let tops = parse_to_trees(s, file, text)?;
        phase("program parsed");
        let result = s.call_global(&format!("{READER_PREFIX}check-program"), &[standard, tops]).map_err(|e| fail(e.to_string()))?;
        phase("checked");
        let offsets = byte_offsets(text);
        let at = |c: i64| offsets.get(c as usize).copied().unwrap_or(text.len()) as u32;
        Ok(s.view(|v| {
            let r = v.get(result);
            let tag = r.field(2).and_then(|t| t.symbol_name()).unwrap_or_default();
            let p = r.field(3).expect("a sum");
            if tag == "k-ok" {
                let lines = p.field(2).and_then(|l| l.list()).unwrap_or_default();
                Ok(lines.into_iter().map(|l| l.string().unwrap_or_default()).collect())
            } else {
                let message = p.field(2).and_then(|m| m.string()).unwrap_or_default();
                let (a, b) = (p.field(3).and_then(|x| x.fixnum()).unwrap_or(0), p.field(4).and_then(|x| x.fixnum()).unwrap_or(0));
                Err(FxError::at(Span::new(file, at(a), at(b)), message))
            }
        }))
    })
}

/// The initial environment of [`crate::standard`], read by the FX-26
/// reader, as `(name type)` for each binding: what `check-program` takes.
pub fn read_standard(scheme: &mut Session) -> R<Handle> {
    let text: String = crate::standard::ENTRIES.iter().map(|(n, t)| format!("({n} {t})\n")).collect();
    read_to_syns(scheme, FileId(0), &text)
}

/// What the FX-26 reader reads from `text`: a list of `syn`s, as a handle
/// in the caller's scope.
pub fn read_to_syns(scheme: &mut Session, file: FileId, text: &str) -> R<Handle> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let mut reader =
        EagerReader::attach_starting(scheme, READER_PREFIX, "eager-start-fx26").map_err(|e| fail(e.to_string()))?;
    let st = reader.state_after(scheme, text, true).map_err(|e| fail(e.to_string()))?;
    let name = |n: &str| format!("{READER_PREFIX}{n}");
    let status = scheme.call_global(&name("eager-status"), &[st]).map_err(|e| fail(e.to_string()))?;
    if scheme.view(|v| v.get(status).symbol_name()).as_deref() != Some("complete") {
        return Err(fail("the FX-26 reader did not read the whole text".into()));
    }
    scheme.call_global(&name("eager-state-syntax"), &[st]).map_err(|e| fail(e.to_string()))
}

/// What the Rust checker finds about `text` that the compiler written in
/// FX-26 needs, as `checked-extracts` would give it: each `extract`'s
/// field, keyed by where it is, in characters. A handle in the caller's
/// scope; or the check's error.
pub fn rust_facts(scheme: &mut Session, file: FileId, text: &str) -> R<Handle> {
    let mut c = crate::Checker::new();
    let forms = c.read_in(file, text)?;
    let done = c.declare_ahead(&forms)?;
    for (f, done) in forms.iter().zip(done) {
        if !done {
            c.top(f)?;
        }
    }
    let offsets = byte_offsets(text);
    let char_at = |byte: u32| offsets.partition_point(|&o| o < byte as usize) as i64;
    let facts: Vec<(i64, i64, i64)> = c
        .facts
        .field_index
        .iter()
        .map(|(e, i)| {
            let span = c.arena.span_of(*e);
            (char_at(span.start), char_at(span.end), *i as i64)
        })
        .collect();
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let mut list = scheme.make(|_| Value::NULL);
    for (a, b, i) in facts {
        let args = [37, a, b, i].map(|n| scheme.make(|_| Value::fixnum(n)));
        let fact = scheme.call_global("%make-frozen", &args).map_err(|e| fail(e.to_string()))?;
        list = scheme.call_global("cons", &[fact, list]).map_err(|e| fail(e.to_string()))?;
    }
    Ok(list)
}

/// Compile `text` with the compiler written in FX-26, given what checking
/// it found (`facts`, from `checked-extracts` or [`rust_facts`]): the word
/// that runs the program, as a handle in the caller's scope, or why the
/// compiler would not make one.
pub fn compile_to_word(scheme: &mut Session, file: FileId, text: &str, facts: Handle) -> R<Result<Handle, String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let tops = parse_to_trees(scheme, file, text)?;
    let result = scheme.call_global(&format!("{READER_PREFIX}compile-program"), &[tops, facts]).map_err(|e| fail(e.to_string()))?;
    let err = scheme.view(|v| {
        let r = v.get(result);
        (r.field(2).and_then(|t| t.symbol_name()).as_deref() == Some("c-err"))
            .then(|| r.field(3).and_then(|p| p.field(2)).and_then(|m| m.string()).unwrap_or_default())
    });
    Ok(match err {
        Some(m) => Err(m),
        None => Ok(scheme.make(|m| {
            let r = m.get(result);
            let payload = m.heap().bloblet_slot(r, 3);
            m.heap().bloblet_slot(payload, 2)
        })),
    })
}

/// The parser's trees for `text`: a list of `top`s, as a handle in the
/// caller's scope.
fn parse_to_trees(scheme: &mut Session, file: FileId, text: &str) -> R<Handle> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let syns = read_to_syns(scheme, file, text)?;
    let result = scheme.call_global(&format!("{READER_PREFIX}parse-program"), &[syns]).map_err(|e| fail(e.to_string()))?;
    let (tag, err) = scheme.view(|v| {
        let r = v.get(result);
        let tag = r.field(2).and_then(|t| t.symbol_name()).unwrap_or_default();
        let p = r.field(3).expect("a sum");
        let err = (tag == "p-err").then(|| {
            (p.field(2).and_then(|m| m.string()).unwrap_or_default(), p.field(3).and_then(|x| x.fixnum()).unwrap_or(0), p.field(4).and_then(|x| x.fixnum()).unwrap_or(0))
        });
        (tag, err)
    });
    if let Some((msg, a, b)) = err {
        let offsets = byte_offsets(text);
        let at = |c: i64| offsets.get(c as usize).copied().unwrap_or(text.len()) as u32;
        return Err(FxError::at(Span::new(file, at(a), at(b)), msg));
    }
    debug_assert_eq!(tag, "p-ok");
    Ok(scheme.make(|m| {
        let r = m.get(result);
        let payload = m.heap().bloblet_slot(r, 3);
        m.heap().bloblet_slot(payload, 2)
    }))
}

/// The byte offset of each character, and of the end.
fn byte_offsets(text: &str) -> Vec<usize> {
    let mut v: Vec<usize> = text.char_indices().map(|(i, _)| i).collect();
    v.push(text.len());
    v
}

/// Field `i` (from 0) of a product: the object model's field `i + 2`.
fn part(product: Local<'_>, i: usize) -> Local<'_> {
    product.field(i + 2).expect("a product's field")
}

fn to_syntax(interner: &mut Interner, file: FileId, at: &dyn Fn(i64) -> u32, s: Local<'_>) -> R<Syntax> {
    let tag = s.field(2).and_then(|t| t.symbol_name()).unwrap_or_default();
    let p = s.field(3).expect("a sum");
    let span = |a: Local<'_>, b: Local<'_>| Span::new(file, at(a.fixnum().unwrap_or(0)), at(b.fixnum().unwrap_or(0)));
    let many = |interner: &mut Interner, list: Local<'_>| -> R<Vec<Syntax>> {
        let items = list.list().expect("a list");
        items.into_iter().map(|x| to_syntax(interner, file, at, x)).collect()
    };
    match tag.as_str() {
        "atom" => {
            let sp = span(part(p, 1), part(p, 2));
            let d = atom(interner, part(p, 0)).ok_or_else(|| FxError::at(sp, "a datum FX-26 does not read"))?;
            Ok(Syntax::new(sp, d))
        }
        "lst" => {
            let sp = span(part(p, 2), part(p, 3));
            let items = many(interner, part(p, 0))?;
            Ok(if items.is_empty() { Syntax::new(sp, Datum::Nil) } else { Syntax::new(sp, Datum::List { items, tail: None }) })
        }
        "dotted" => {
            let sp = span(part(p, 3), part(p, 4));
            let items = many(interner, part(p, 0))?;
            let tail = to_syntax(interner, file, at, part(p, 1))?;
            Ok(Syntax::new(sp, Datum::List { items, tail: Some(Box::new(tail)) }))
        }
        "vec" => {
            let sp = span(part(p, 2), part(p, 3));
            Ok(Syntax::new(sp, Datum::Vector(many(interner, part(p, 0))?)))
        }
        other => unreachable!("the reader makes no `{other}`"),
    }
}

/// A datum that is not a list, as the Rust reader would have it.
fn atom(interner: &mut Interner, v: Local<'_>) -> Option<Datum> {
    if let Some(n) = v.fixnum() {
        return Some(Datum::Number(Num::Int(n)));
    }
    if v.is_true() || v.is_false() {
        return Some(Datum::Bool(v.is_true()));
    }
    if let Some(c) = v.char() {
        return Some(Datum::Char(c));
    }
    if let Some(n) = v.symbol_name() {
        return Some(Datum::Symbol(interner.intern(&n)));
    }
    if let Some(s) = v.string() {
        return Some(Datum::Str(s));
    }
    if let Some(b) = v.bytevector() {
        return Some(Datum::Bytevector(b));
    }
    v.flonum().map(|f| Datum::Number(Num::Real(f)))
}
