//! Literals written in full, exactly, in a form a reader can build again:
//! the compile listing's `--literals full` (kayak's request, 2026-10-16;
//! `docs/fx26.md`, "The compile listing's literals").
//!
//! [`print`](crate::print)'s `write` is for people: it cuts nothing, but it
//! writes a float in decimal, a symbol bare, and an FX-26 product as
//! `#<product of 2>`. Here every value is written so that its bits come
//! back: a float by its bits, a symbol between bars, any bloblet by its
//! kind, its fields and its suffix's bytes. And an object reached more than
//! once anywhere in the listing (sharing, or a cycle) is labelled where it
//! is first written, `#n=`, and named after, `#n#`, so that what is `eq?`
//! stays `eq?`: the labels are the whole listing's, not one literal's.
//!
//! What a word is, a closure is: a word by its name, `#word "NAME"`, the
//! listing's own; a closure `#bloblet(cellular-closure …)`, its word and its
//! captured values among its fields.

use fixpt_heap::layout::cellular::{GLOBAL_FIELDS, GLOBAL_NAME, WORD_NAME};
use fixpt_heap::{Heap, ObjType, Value};
use std::collections::HashMap;
use std::fmt::Write as _;

/// Every literal of a listing: first each is [`seen`](Literals::seen), in the
/// order the listing writes them; then each is [`written`](Literals::written)
/// in that order again, the objects met more than once labelled.
#[derive(Default)]
pub struct Literals {
    /// How many times each object has been reached, while seeing.
    reached: HashMap<u64, u32>,
    /// The label of each object reached more than once, and whether it has
    /// been written yet.
    labels: HashMap<u64, (u32, bool)>,
    next: u32,
}

impl Literals {
    /// Note literal `v`, and what it reaches.
    pub fn seen(&mut self, heap: &Heap, v: Value) {
        let mut todo = vec![v];
        while let Some(v) = todo.pop() {
            if !labelled(heap, v) {
                continue;
            }
            let n = self.reached.entry(v.raw()).or_insert(0);
            *n += 1;
            if *n == 1 {
                todo.extend(children(heap, v));
            }
        }
    }

    /// Literal `v`, written in full.
    pub fn written(&mut self, heap: &Heap, v: Value) -> String {
        let mut out = String::new();
        self.put(heap, v, &mut out);
        out
    }

    fn put(&mut self, heap: &Heap, v: Value, out: &mut String) {
        if labelled(heap, v) && self.reached.get(&v.raw()).copied().unwrap_or(0) > 1 {
            match self.labels.get(&v.raw()).copied() {
                Some((n, true)) => {
                    let _ = write!(out, "#{n}#");
                    return;
                }
                _ => {
                    let n = self.next;
                    self.next += 1;
                    self.labels.insert(v.raw(), (n, true));
                    let _ = write!(out, "#{n}=");
                }
            }
        }
        if v.is_fixnum() {
            let _ = write!(out, "{}", v.as_fixnum());
        } else if v.is_immediate() {
            immediate(v, out);
        } else if v.is_pair() {
            out.push('(');
            self.put(heap, heap.car(v), out);
            out.push_str(" . ");
            self.put(heap, heap.cdr(v), out);
            out.push(')');
        } else if v.is_suffix_ref() {
            out.push_str("#suffix-ref(");
            self.put(heap, heap.suffix_ref_owner(v), out);
            let _ = write!(out, " {})", v.offset());
        } else if heap.is_cellular_word(v) || heap.is_register_word(v) {
            let name = heap.symbol_name(heap.bloblet_slot(v, WORD_NAME));
            let which = if heap.is_cellular_word(v) { "word" } else { "register-word" };
            let _ = write!(out, "#{which} ");
            string(out, &name);
        } else if let Some(name) = global_name(heap, v) {
            out.push_str("#global ");
            string(out, &name);
        } else {
            self.object(heap, v, out);
        }
    }

    fn object(&mut self, heap: &Heap, v: Value, out: &mut String) {
        match heap.obj_type(v) {
            Some(ObjType::String) => string(out, &heap.string_to_rust(v)),
            Some(ObjType::Symbol) => symbol(out, &heap.symbol_name(v)),
            Some(ObjType::Flonum) => {
                let _ = write!(out, "#f64x{:016x}", heap.flonum_value(v).to_bits());
            }
            Some(ObjType::Bignum) | Some(ObjType::Ratnum) => {
                let n = crate::num::N::load(heap, v).expect("numeric object");
                out.push_str(&n.to_string_radix(10));
            }
            Some(ObjType::Vector) => {
                out.push_str("#(");
                for i in 0..heap.obj_len(v) {
                    if i > 0 {
                        out.push(' ');
                    }
                    self.put(heap, heap.obj_ref(v, i), out);
                }
                out.push(')');
            }
            Some(ObjType::Bytevector) => {
                out.push_str("#u8(");
                let bytes: Vec<String> = (0..heap.bytevector_len(v)).map(|i| heap.bytevector_ref(v, i).to_string()).collect();
                out.push_str(&bytes.join(" "));
                out.push(')');
            }
            _ if v.is_bloblet() => {
                let h = heap.bloblet_head(v);
                let kind = fixpt_heap::layout::KINDS.iter().find(|k| k.code == h.kind).map_or("?", |k| k.name);
                let _ = write!(out, "#bloblet({kind} (");
                for k in 1..=h.fields {
                    if k > 1 {
                        out.push(' ');
                    }
                    let f = heap.bloblet_slot(v, k);
                    if f.tag() == fixpt_heap::value::TAG_TRAILER {
                        let _ = write!(out, "#trailer {}", f.raw() >> 3);
                    } else {
                        self.put(heap, f, out);
                    }
                }
                out.push_str(") #u8(");
                let bytes: Vec<String> = heap.bloblet_bytes(v).iter().map(u8::to_string).collect();
                out.push_str(&bytes.join(" "));
                out.push_str("))");
            }
            // A Scheme object no FX-26 literal is: said, not built.
            _ => out.push_str(&crate::print::write_value(heap, v)),
        }
    }
}

/// Whether `v` is an object a label may stand for: one with an identity.
/// Symbols are interned, so their name is their identity; words and globals
/// are written by name.
fn labelled(heap: &Heap, v: Value) -> bool {
    (v.is_pair() || v.is_bloblet() || v.is_suffix_ref())
        && !heap.is_cellular_word(v)
        && !heap.is_register_word(v)
        && global_name(heap, v).is_none()
        && heap.obj_type(v) != Some(ObjType::Symbol)
}

/// What `v` holds that is written with it.
fn children(heap: &Heap, v: Value) -> Vec<Value> {
    if v.is_pair() {
        return vec![heap.car(v), heap.cdr(v)];
    }
    if v.is_suffix_ref() {
        return vec![heap.suffix_ref_owner(v)];
    }
    match heap.obj_type(v) {
        Some(ObjType::Vector) => (0..heap.obj_len(v)).map(|i| heap.obj_ref(v, i)).collect(),
        Some(_) => Vec::new(),
        None if v.is_bloblet() => (1..=heap.bloblet_head(v).fields)
            .map(|k| heap.bloblet_slot(v, k))
            .filter(|f| f.tag() != fixpt_heap::value::TAG_TRAILER)
            .collect(),
        None => Vec::new(),
    }
}

/// A global's cell (`layout::cellular::GLOBAL_*`): a plain bloblet of its
/// fields whose name is a symbol. Its name, if `v` is one.
fn global_name(heap: &Heap, v: Value) -> Option<String> {
    if !v.is_bloblet() || heap.obj_type(v).is_some() || heap.bloblet_kind(v) != const { fixpt_heap::layout::kind("bloblet") } {
        return None;
    }
    let h = heap.bloblet_head(v);
    if h.fields != GLOBAL_FIELDS + 1 || h.bytes != 0 {
        return None;
    }
    let n = heap.bloblet_slot(v, GLOBAL_NAME);
    (n.is_bloblet() && heap.obj_type(n) == Some(ObjType::Symbol)).then(|| heap.symbol_name(n))
}

fn immediate(v: Value, out: &mut String) {
    if v.is_char() {
        let _ = write!(out, "#\\x{:x}", v.as_char() as u32);
    } else if v.is_f32() {
        let _ = write!(out, "#f32x{:08x}", v.as_f32().to_bits());
    } else {
        out.push_str(match v {
            _ if v == Value::TRUE => "#t",
            _ if v == Value::FALSE => "#f",
            _ if v.is_null() => "()",
            _ if v.is_unit() => "#u",
            _ if v.is_eof() => "#eof",
            _ if v == Value::UNSPECIFIED => "#unspecified",
            _ if v == Value::DEFAULT => "#default",
            _ if v.is_unbound() => "#unbound",
            _ => "#<immediate>",
        });
    }
}

/// A string, every character not printable ASCII (and `"` and `\`) by its
/// code, `\xHH;`, as R7RS reads it.
fn string(out: &mut String, s: &str) {
    out.push('"');
    escaped(out, s, '"');
    out.push('"');
}

/// A symbol between bars, as R7RS reads `|…|`.
fn symbol(out: &mut String, s: &str) {
    out.push('|');
    escaped(out, s, '|');
    out.push('|');
}

fn escaped(out: &mut String, s: &str, quote: char) {
    for c in s.chars() {
        if c == quote || c == '\\' || !(' '..='~').contains(&c) {
            let _ = write!(out, "\\x{:x};", c as u32);
        } else {
            out.push(c);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What is reached twice is labelled where first written and named after,
    /// across literals; a cycle too; a symbol never, its name its identity.
    #[test]
    fn sharing_and_cycles_are_labelled_across_literals() {
        let mut heap = Heap::new();
        let s = heap.make_string("shared");
        let a = heap.intern("a");
        let x = heap.cons(s, Value::NULL);
        let y = heap.cons(a, x);
        let cyc = heap.cons(Value::fixnum(1), Value::NULL);
        heap.set_cdr(cyc, cyc);
        let mut lits = Literals::default();
        for v in [y, x, cyc, a] {
            lits.seen(&heap, v);
        }
        let shown: Vec<String> = [y, x, cyc, a].iter().map(|v| lits.written(&heap, *v)).collect();
        assert_eq!(shown, ["(|a| . #0=(\"shared\" . ()))", "#0#", "#1=(1 . #1#)", "|a|"]);
    }

    /// A float by its bits, a character by its code, a string's every
    /// character not printable ASCII by its code.
    #[test]
    fn values_are_written_exactly() {
        let mut heap = Heap::new();
        let f = heap.make_flonum(0.1);
        let s = heap.make_string("a\"b\\c\nd é");
        let mut lits = Literals::default();
        let shown: Vec<String> = [f, Value::char('λ'), s].iter().map(|v| lits.written(&heap, *v)).collect();
        assert_eq!(shown, ["#f64x3fb999999999999a", "#\\x3bb", "\"a\\x22;b\\x5c;c\\xa;d \\xe9;\""]);
    }
}
