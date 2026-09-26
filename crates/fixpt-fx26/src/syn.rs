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
use fixpt_heap::{Heap, ObjType, Value};
use fixpt_read::{Datum, FileId, Interner, Num, Span, Syntax};
use fixpt_scheme::Session;
use fixpt_scheme::eager::EagerReader;

/// Read `text` with the FX-26 reader, already loaded into `scheme` (see
/// [`crate::session::load_eager_reader`]), interning names in `interner`.
pub fn read_with_fx26_reader(scheme: &mut Session, interner: &mut Interner, file: FileId, text: &str) -> R<Vec<Syntax>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let mut reader =
        EagerReader::attach_starting(scheme, READER_PREFIX, "eager-start-fx26").map_err(|e| fail(e.to_string()))?;
    // As though Enter were pressed: a newline ends a trailing atom.
    let st = reader.state_after(scheme, text, true).map_err(|e| fail(e.to_string()))?;
    let root = scheme.rt.heap.push_root(st);
    let call = |scheme: &mut Session, name: &str| -> R<Value> {
        let f = scheme.global_value(&format!("{READER_PREFIX}{name}")).expect("the reader is loaded");
        let st = scheme.rt.heap.root_at(root);
        scheme.call(f, &[st]).map_err(|e| fail(e.to_string()))
    };
    let out = (|| {
        let status = call(scheme, "eager-status")?;
        let offsets = byte_offsets(text);
        let at = |c: i64| offsets.get(c as usize).copied().unwrap_or(text.len()) as u32;
        match scheme.rt.heap.symbol_name(status).as_str() {
            "complete" => {}
            "error" => {
                let pos = call(scheme, "eager-state-position")?.as_fixnum();
                let msg = call(scheme, "eager-state-message")?;
                let msg = scheme.rt.heap.string_to_rust(msg);
                return Err(FxError::at(Span::new(file, at(pos), at(pos)), msg));
            }
            _ => return Err(FxError::at(Span::new(file, text.len() as u32, text.len() as u32), "the text ends in the middle of a form")),
        }
        let syns = call(scheme, "eager-state-syntax")?;
        let heap = &scheme.rt.heap;
        let items = heap.list_to_vec(syns).expect("a list");
        items.into_iter().map(|s| to_syntax(heap, interner, file, &at, s)).collect()
    })();
    scheme.rt.heap.pop_roots_to(root);
    out
}

/// The byte offset of each character, and of the end.
fn byte_offsets(text: &str) -> Vec<usize> {
    let mut v: Vec<usize> = text.char_indices().map(|(i, _)| i).collect();
    v.push(text.len());
    v
}

/// Field `i` (from 0) of a product: the object model's field `i + 2`.
fn part(heap: &Heap, product: Value, i: usize) -> Value {
    heap.bloblet_slot(product, i + 2)
}

fn to_syntax(heap: &Heap, interner: &mut Interner, file: FileId, at: &dyn Fn(i64) -> u32, s: Value) -> R<Syntax> {
    let tag = heap.symbol_name(heap.bloblet_slot(s, 2));
    let p = heap.bloblet_slot(s, 3);
    let span = |a: Value, b: Value| Span::new(file, at(a.as_fixnum()), at(b.as_fixnum()));
    let many = |interner: &mut Interner, list: Value| -> R<Vec<Syntax>> {
        let items = heap.list_to_vec(list).expect("a list");
        items.into_iter().map(|x| to_syntax(heap, interner, file, at, x)).collect()
    };
    match tag.as_str() {
        "atom" => {
            let sp = span(part(heap, p, 1), part(heap, p, 2));
            let d = atom(heap, interner, part(heap, p, 0)).ok_or_else(|| FxError::at(sp, "a datum FX-26 does not read"))?;
            Ok(Syntax::new(sp, d))
        }
        "lst" => {
            let sp = span(part(heap, p, 2), part(heap, p, 3));
            let items = many(interner, part(heap, p, 0))?;
            Ok(if items.is_empty() { Syntax::new(sp, Datum::Nil) } else { Syntax::new(sp, Datum::List { items, tail: None }) })
        }
        "dotted" => {
            let sp = span(part(heap, p, 3), part(heap, p, 4));
            let items = many(interner, part(heap, p, 0))?;
            let tail = to_syntax(heap, interner, file, at, part(heap, p, 1))?;
            Ok(Syntax::new(sp, Datum::List { items, tail: Some(Box::new(tail)) }))
        }
        "vec" => {
            let sp = span(part(heap, p, 2), part(heap, p, 3));
            Ok(Syntax::new(sp, Datum::Vector(many(interner, part(heap, p, 0))?)))
        }
        other => unreachable!("the reader makes no `{other}`"),
    }
}

/// A datum that is not a list, as the Rust reader would have it.
fn atom(heap: &Heap, interner: &mut Interner, v: Value) -> Option<Datum> {
    if v.is_fixnum() {
        return Some(Datum::Number(Num::Int(v.as_fixnum())));
    }
    if v == Value::TRUE || v == Value::FALSE {
        return Some(Datum::Bool(v == Value::TRUE));
    }
    if v.is_char() {
        return Some(Datum::Char(v.as_char()));
    }
    match heap.obj_type(v)? {
        ObjType::Symbol => Some(Datum::Symbol(interner.intern(&heap.symbol_name(v)))),
        ObjType::String => Some(Datum::Str(heap.string_to_rust(v))),
        ObjType::Bytevector => Some(Datum::Bytevector(heap.bytevector_to_vec(v))),
        ObjType::Flonum => Some(Datum::Number(Num::Real(heap.flonum_value(v)))),
        _ => None,
    }
}
