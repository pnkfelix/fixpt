//! `write` and `display` for heap values.
//!
//! Cycle-safe: a self-referential list prints with datum labels (`#0=(1 . #0#)`)
//! rather than running forever, which matters because FX-87 builds genuinely
//! circular type structures and the REPL will be asked to print them.

use crate::num::N;
use fixpt_heap::{Heap, ObjType, Value};
use std::collections::HashMap;
use std::fmt::Write as _;

pub fn write_value(heap: &Heap, v: Value) -> String {
    print(heap, v, true)
}

pub fn display_value(heap: &Heap, v: Value) -> String {
    print(heap, v, false)
}

fn print(heap: &Heap, v: Value, write: bool) -> String {
    let shared = find_shared(heap, v);
    let mut labels: HashMap<Value, (u32, bool)> = HashMap::new();
    for (i, s) in shared.iter().enumerate() {
        labels.insert(*s, (i as u32, false));
    }
    let mut out = String::new();
    put(heap, v, write, &mut labels, &mut out);
    out
}

/// Find the nodes that lie on a cycle, so only those get datum labels.
///
/// R7RS asks for labels where they are needed for the output to be finite, not
/// wherever structure happens to be shared. Labelling mere sharing is legal but
/// surprising — a value built twice from the same constant would print as
/// `#0=…` and `#0#` — so this looks for a node reachable from itself, which is
/// a depth-first search with the current path marked, not a visit count.
fn find_shared(heap: &Heap, root: Value) -> Vec<Value> {
    #[derive(Copy, Clone)]
    enum Step {
        Enter(Value),
        Leave(Value),
    }
    let mut on_path: HashMap<Value, ()> = HashMap::new();
    let mut finished: HashMap<Value, ()> = HashMap::new();
    let mut cyclic = Vec::new();
    let mut stack = vec![Step::Enter(root)];
    // A bound on total work, so a pathological structure cannot hang the
    // printer even if the analysis is somehow defeated.
    let mut budget = 1_000_000u32;
    while let Some(step) = stack.pop() {
        if budget == 0 {
            break;
        }
        budget -= 1;
        match step {
            Step::Leave(v) => {
                on_path.remove(&v);
                finished.insert(v, ());
            }
            Step::Enter(v) => {
                let interesting =
                    v.is_pair() || matches!(heap.obj_type(v), Some(ObjType::Vector));
                if !interesting || finished.contains_key(&v) {
                    continue;
                }
                if on_path.contains_key(&v) {
                    if !cyclic.contains(&v) {
                        cyclic.push(v);
                    }
                    continue;
                }
                on_path.insert(v, ());
                stack.push(Step::Leave(v));
                if v.is_pair() {
                    stack.push(Step::Enter(heap.cdr(v)));
                    stack.push(Step::Enter(heap.car(v)));
                } else {
                    for i in (0..heap.obj_len(v)).rev() {
                        stack.push(Step::Enter(heap.obj_ref(v, i)));
                    }
                }
            }
        }
    }
    cyclic
}

fn put(
    heap: &Heap,
    v: Value,
    write: bool,
    labels: &mut HashMap<Value, (u32, bool)>,
    out: &mut String,
) {
    if let Some((n, emitted)) = labels.get(&v).copied() {
        if emitted {
            let _ = write!(out, "#{n}#");
            return;
        }
        labels.insert(v, (n, true));
        let _ = write!(out, "#{n}=");
    }

    if v.is_fixnum() {
        let _ = write!(out, "{}", v.as_fixnum());
        return;
    }
    if v.is_immediate() {
        out.push_str(match v {
            _ if v == Value::TRUE => "#t",
            _ if v == Value::FALSE => "#f",
            _ if v.is_null() => "()",
            _ if v.is_unit() => "#u",
            _ if v.is_eof() => "#<eof>",
            _ if v == Value::UNSPECIFIED => "#<unspecified>",
            _ if v == Value::DEFAULT => "#<default>",
            _ if v.is_unbound() => "#<unbound>",
            _ if v.is_char() => {
                if write {
                    put_char(out, v.as_char());
                } else {
                    out.push(v.as_char());
                }
                return;
            }
            _ => "#<immediate>",
        });
        return;
    }
    if v.is_pair() {
        out.push('(');
        put(heap, heap.car(v), write, labels, out);
        let mut rest = heap.cdr(v);
        loop {
            if rest.is_null() {
                break;
            }
            // A labelled tail has to be printed as a dotted tail, or the label
            // would have nowhere to go.
            if rest.is_pair() && !labels.contains_key(&rest) {
                out.push(' ');
                put(heap, heap.car(rest), write, labels, out);
                rest = heap.cdr(rest);
            } else {
                out.push_str(" . ");
                put(heap, rest, write, labels, out);
                break;
            }
        }
        out.push(')');
        return;
    }

    match heap.obj_type(v) {
        Some(ObjType::String) => {
            if write {
                put_string(out, &heap.string_to_rust(v));
            } else {
                out.push_str(&heap.string_to_rust(v));
            }
        }
        Some(ObjType::Symbol) => out.push_str(&heap.symbol_name(v)),
        Some(ObjType::Flonum) | Some(ObjType::Bignum) | Some(ObjType::Ratnum) => {
            let n = N::load(heap, v).expect("numeric object");
            out.push_str(&n.to_string_radix(10));
        }
        Some(ObjType::Vector) => {
            out.push_str("#(");
            for i in 0..heap.obj_len(v) {
                if i > 0 {
                    out.push(' ');
                }
                put(heap, heap.obj_ref(v, i), write, labels, out);
            }
            out.push(')');
        }
        Some(ObjType::Bytevector) => {
            out.push_str("#u8(");
            for i in 0..heap.bytevector_len(v) {
                if i > 0 {
                    out.push(' ');
                }
                let _ = write!(out, "{}", heap.bytevector_ref(v, i));
            }
            out.push(')');
        }
        Some(ObjType::Closure) => {
            let code = heap.closure_code(v);
            let name = heap.bloblet_slot(code, fixpt_heap::layout::code::CODE_NAME);
            if heap.is_a(name, ObjType::Symbol) {
                let _ = write!(out, "#<procedure:{}>", heap.symbol_name(name));
            } else {
                out.push_str("#<procedure>");
            }
        }
        Some(ObjType::Primitive) => {
            let name = heap.obj_ref(v, 0);
            let _ = write!(out, "#<primitive:{}>", heap.symbol_name(name));
        }
        Some(ObjType::Record) => {
            let rtd = heap.obj_ref(v, 0);
            let name = heap.obj_ref(rtd, 0);
            let _ = write!(out, "#<{}", heap.symbol_name(name));
            for i in 1..heap.obj_len(v) {
                out.push(' ');
                put(heap, heap.obj_ref(v, i), write, labels, out);
            }
            out.push('>');
        }
        Some(ObjType::RecordType) => {
            let _ = write!(out, "#<record-type:{}>", heap.symbol_name(heap.obj_ref(v, 0)));
        }
        Some(ObjType::Box) => {
            out.push_str("#<box ");
            put(heap, heap.unbox(v), write, labels, out);
            out.push('>');
        }
        Some(ObjType::Values) => {
            out.push_str("#<values");
            for i in 0..heap.obj_len(v) {
                out.push(' ');
                put(heap, heap.obj_ref(v, i), write, labels, out);
            }
            out.push('>');
        }
        Some(ObjType::Promise) => out.push_str("#<promise>"),
        Some(ObjType::Continuation) => out.push_str("#<continuation>"),
        Some(ObjType::Port) => out.push_str("#<port>"),
        Some(ObjType::HashTable) => out.push_str("#<hash-table>"),
        Some(ObjType::Environment) => out.push_str("#<environment>"),
        Some(ObjType::Code) => out.push_str("#<code>"),
        None if v.is_bloblet() => {
            let h = heap.bloblet_head(v);
            let kind = fixpt_heap::layout::KINDS.iter().find(|k| k.code == h.kind).map_or("?", |k| k.name);
            // A continuation, or the closure that stands for one.
            if heap.continuation_of(v).is_some() {
                out.push_str("#<continuation>");
            } else if kind == "sum" {
                let tag = heap.bloblet_slot(v, 2);
                out.push_str(&format!("#<sum {}>", write_value(heap, tag)));
            } else if kind == "product" {
                out.push_str(&format!("#<product of {}>", h.fields - 1));
            } else if h.kind == fixpt_heap::layout::threaded::KIND {
                let name = heap.bloblet_slot(v, fixpt_heap::layout::threaded::WORD_NAME);
                out.push_str(&format!("#<threaded-word {}>", write_value(heap, name)));
            } else {
                out.push_str(&format!("#<{kind} {} fields {} bytes>", h.fields, h.bytes));
            }
        }
        None => out.push_str("#<unknown>"),
    }
}

fn put_char(out: &mut String, c: char) {
    out.push_str("#\\");
    match c {
        ' ' => out.push_str("space"),
        '\n' => out.push_str("newline"),
        '\t' => out.push_str("tab"),
        '\r' => out.push_str("return"),
        '\0' => out.push_str("null"),
        '\u{7}' => out.push_str("alarm"),
        '\u{8}' => out.push_str("backspace"),
        '\u{7f}' => out.push_str("delete"),
        '\u{1b}' => out.push_str("escape"),
        c if (c as u32) < 0x20 => {
            let _ = write!(out, "x{:x}", c as u32);
        }
        c => out.push(c),
    }
}

fn put_string(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\x{:x};", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}
