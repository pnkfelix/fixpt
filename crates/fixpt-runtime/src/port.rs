//! Textual ports.
//!
//! An input port holds the whole file as a heap string plus a cursor. That is
//! not how a production runtime would do it, but it makes a port an ordinary
//! heap object with no external resource attached — so it survives collection,
//! and it will survive being written into a heap image without a dangling file
//! descriptor.
//!
//! Output goes through the session's sink rather than being buffered, so
//! `display` to standard output and a write to a port reach the same place in
//! the same order.

use crate::error::Outcome;
use crate::runtime::Runtime;
use fixpt_heap::{ObjType, Value};
use fixpt_read::{Datum, Num, Syntax, SyntaxProfile};

/// `[kind, content, position, name]`
pub const PORT_INPUT: i64 = 0;
pub const PORT_STDOUT: i64 = 1;

pub fn make_input_port(rt: &mut Runtime, name: &str, contents: &str) -> Value {
    let text = rt.heap.make_string(contents);
    let label = rt.heap.make_string(name);
    let p = rt.heap.alloc(ObjType::Port, 4, Value::UNSPECIFIED);
    rt.heap.obj_set(p, 0, Value::fixnum(PORT_INPUT));
    rt.heap.obj_set(p, 1, text);
    rt.heap.obj_set(p, 2, Value::fixnum(0));
    rt.heap.obj_set(p, 3, label);
    p
}

pub fn make_stdout_port(rt: &mut Runtime) -> Value {
    let label = rt.heap.make_string("standard-output");
    let p = rt.heap.alloc(ObjType::Port, 4, Value::UNSPECIFIED);
    rt.heap.obj_set(p, 0, Value::fixnum(PORT_STDOUT));
    rt.heap.obj_set(p, 1, Value::FALSE);
    rt.heap.obj_set(p, 2, Value::fixnum(0));
    rt.heap.obj_set(p, 3, label);
    p
}

fn as_port(rt: &mut Runtime, v: Value) -> Outcome<(i64, Value, usize)> {
    if !rt.heap.is_a(v, ObjType::Port) {
        return rt.type_error("a port", v);
    }
    let kind = rt.heap.obj_ref(v, 0).as_fixnum();
    let content = rt.heap.obj_ref(v, 1);
    let pos = rt.heap.obj_ref(v, 2).as_fixnum() as usize;
    Ok((kind, content, pos))
}

/// The remaining text of an input port, as Rust.
fn rest(rt: &Runtime, content: Value, pos: usize) -> String {
    let n = rt.heap.string_len(content);
    (pos.min(n)..n).map(|i| rt.heap.string_ref(content, i)).collect()
}

pub fn read_char(rt: &mut Runtime, port: Value, advance: bool) -> Outcome<Value> {
    let (kind, content, pos) = as_port(rt, port)?;
    if kind != PORT_INPUT {
        return rt.fail("not an input port", &[port]);
    }
    if pos >= rt.heap.string_len(content) {
        return Ok(Value::EOF);
    }
    let c = rt.heap.string_ref(content, pos);
    if advance {
        rt.heap.obj_set(port, 2, Value::fixnum(pos as i64 + 1));
    }
    Ok(Value::char(c))
}

pub fn at_eof(rt: &mut Runtime, port: Value) -> Outcome<bool> {
    let (kind, content, pos) = as_port(rt, port)?;
    if kind != PORT_INPUT {
        return Ok(false);
    }
    Ok(pos >= rt.heap.string_len(content))
}

/// Read one datum, advancing past it.
///
/// `fold` selects the FX dialects' case-folding reader; FX-91's own
/// `stream-read-sexp` goes through `fx-read`, which folds.
pub fn read_datum(rt: &mut Runtime, port: Value, fold: bool) -> Outcome<Value> {
    let (kind, content, pos) = as_port(rt, port)?;
    if kind != PORT_INPUT {
        return rt.fail("not an input port", &[port]);
    }
    // The cursor counts characters; the reader counts bytes. Slice first, then
    // translate back, so the two never have to agree on units.
    let text = rest(rt, content, pos);
    let profile = if fold { SyntaxProfile::FX91 } else { SyntaxProfile::SCHEME };
    let file = fixpt_read::FileId(0);
    let mut interner = std::mem::take(&mut rt.interner);
    let mut reader = fixpt_read::Reader::new(&text, file, profile, &mut interner);
    let result = reader.read();
    let consumed = reader.position();
    rt.interner = interner;
    let datum = match result {
        Ok(Some(d)) => d,
        Ok(None) => return Ok(Value::EOF),
        Err(e) => return rt.fail(&format!("read: {}", e.message), &[]),
    };
    let chars = text[..consumed].chars().count();
    rt.heap.obj_set(port, 2, Value::fixnum((pos + chars) as i64));
    Ok(syntax_to_value(rt, &datum))
}

pub fn write_string(rt: &mut Runtime, port: Value, text: &str) -> Outcome<Value> {
    let (kind, _, _) = as_port(rt, port)?;
    if kind != PORT_STDOUT {
        return rt.fail("not an output port", &[port]);
    }
    rt.emit(text);
    Ok(Value::UNSPECIFIED)
}

/// Materialise read syntax as a heap value.
pub fn syntax_to_value(rt: &mut Runtime, s: &Syntax) -> Value {
    match &s.datum {
        Datum::Bool(b) => Value::boolean(*b),
        Datum::Char(c) => Value::char(*c),
        Datum::Nil => Value::NULL,
        Datum::Number(n) => number(rt, n),
        Datum::Str(text) => rt.heap.make_string(text),
        Datum::Symbol(sym) => {
            let name = rt.interner.name(*sym).to_string();
            rt.heap.intern(&name)
        }
        Datum::List { items, tail } => {
            let mut acc = match tail {
                Some(t) => syntax_to_value(rt, t),
                None => Value::NULL,
            };
            for item in items.iter().rev() {
                let v = syntax_to_value(rt, item);
                acc = rt.heap.cons(v, acc);
            }
            acc
        }
        Datum::Vector(items) => {
            let vals: Vec<Value> = items.iter().map(|i| syntax_to_value(rt, i)).collect();
            rt.heap.vector_from(&vals)
        }
        Datum::Bytevector(bytes) => rt.heap.make_bytevector(bytes),
    }
}

fn number(rt: &mut Runtime, n: &Num) -> Value {
    crate::num_from_literal(rt, n)
}
