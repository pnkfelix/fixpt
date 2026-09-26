//! Syntax trees as text, to compare the parser written in FX-26 with the
//! Rust one (`PLAN.md` §11, step 9a).
//!
//! [`show_value`] prints any FX-26 data from the heap: a sum as its tag and
//! its product's fields, `(tag f …)`; a product elsewhere as `[f …]`; a list
//! as `(x …)`; a `syn` (a description, kept as it was written) as `_`.
//! [`show_top`] prints the Rust parser's tree in exactly that shape, from the
//! parser's datatypes in `parser.fx`, with spans in characters.

use crate::ast::{ArmBind, BlobletOp, Exp, ExpId};
use crate::check::Checker;
use crate::top::Top;
use fixpt_heap::layout::kind;
use fixpt_heap::{Heap, ObjType, Value};

/// FX-26 data on the heap, as text.
pub fn show_value(heap: &Heap, v: Value) -> String {
    if v.is_fixnum() {
        return v.as_fixnum().to_string();
    }
    if v == Value::TRUE || v == Value::FALSE {
        return (if v == Value::TRUE { "#t" } else { "#f" }).into();
    }
    if v.is_char() {
        return format!("{:?}", v.as_char());
    }
    if v == Value::NULL || v.is_pair() {
        let items = heap.list_to_vec(v).expect("a proper list");
        let parts: Vec<String> = items.iter().map(|x| show_value(heap, *x)).collect();
        return format!("({})", parts.join(" "));
    }
    match heap.obj_type(v) {
        Some(ObjType::Symbol) => return heap.symbol_name(v),
        Some(ObjType::String) => return format!("{:?}", heap.string_to_rust(v)),
        _ => {}
    }
    if v.is_bloblet() && heap.bloblet_kind(v) == kind("sum") {
        let tag = heap.symbol_name(heap.bloblet_slot(v, 2));
        if matches!(tag.as_str(), "atom" | "lst" | "dotted" | "vec") {
            return "_".into();
        }
        let payload = heap.bloblet_slot(v, 3);
        let mut out = format!("({tag}");
        for f in fields(heap, payload) {
            out.push(' ');
            out.push_str(&show_value(heap, f));
        }
        out.push(')');
        return out;
    }
    if v.is_bloblet() && heap.bloblet_kind(v) == kind("product") {
        let parts: Vec<String> = fields(heap, v).into_iter().map(|x| show_value(heap, x)).collect();
        return format!("[{}]", parts.join(" "));
    }
    format!("#<{:?}>", v)
}

/// A product's fields, in order.
fn fields(heap: &Heap, p: Value) -> Vec<Value> {
    let n = heap.bloblet_head(p).fields - 1;
    (0..n).map(|i| heap.bloblet_slot(p, i + 2)).collect()
}

/// Byte offset to character position, for text with non-ASCII in it.
pub struct Chars(Vec<u32>);

impl Chars {
    pub fn of(text: &str) -> Chars {
        let mut v = vec![0u32; text.len() + 1];
        let mut c = 0u32;
        for (i, ch) in text.char_indices() {
            for b in 0..ch.len_utf8() {
                v[i + b] = c;
            }
            c += 1;
        }
        v[text.len()] = c;
        Chars(v)
    }
    fn at(&self, byte: u32) -> u32 {
        self.0[byte as usize]
    }
}

/// A top-level form the Rust side checked, in the shape of `parser.fx`'s
/// `top`. `span` is the form's.
pub fn show_top(c: &Checker, chars: &Chars, top: &Top, span: fixpt_read::Span) -> String {
    let (a, b) = (chars.at(span.start), chars.at(span.end));
    match top {
        Top::Define { name, exp, recursive, .. } => {
            let ty = if *recursive { "(_)" } else { "()" };
            format!("(t-define {} {ty} {} {a} {b})", c.interner.name(*name), show_exp(c, chars, *exp))
        }
        Top::DefineType { .. } | Top::DefineTypeFamily { .. } => format!("(t-define-type _ _ {a} {b})"),
        Top::DefineEffect { .. } => format!("(t-define-effect _ _ {a} {b})"),
        Top::PrivateRegions { regions } => {
            format!("(t-private-regions ({}) {a} {b})", vec!["_"; regions.len()].join(" "))
        }
        Top::Exp(k) => format!("(t-exp {})", show_exp(c, chars, k.exp)),
    }
}

fn show_exp(c: &Checker, chars: &Chars, e: ExpId) -> String {
    let sp = c.arena.span_of(e);
    let (a, b) = (chars.at(sp.start), chars.at(sp.end));
    let name = |s| c.interner.name(s).to_string();
    let go = |x: ExpId| show_exp(c, chars, x);
    let list = |xs: Vec<String>| format!("({})", xs.join(" "));
    match c.arena.exp_at(e).clone() {
        Exp::Var(s) => format!("(e-var {} {a} {b})", name(s)),
        Exp::Int(n) => format!("(e-int {n} {a} {b})"),
        Exp::Bool(x) => format!("(e-bool {} {a} {b})", if x { "#t" } else { "#f" }),
        Exp::Str(s) => format!("(e-str {s:?} {a} {b})"),
        Exp::Char(ch) => format!("(e-char {ch:?} {a} {b})"),
        Exp::Symbol(s) => format!("(e-sym {} {a} {b})", name(s)),
        Exp::Unit => format!("(e-unit {a} {b})"),
        Exp::Lambda { params, body } => {
            let ps = params
                .iter()
                .map(|(n, t)| format!("[{} {}]", name(*n), if t.is_some() { "(_)" } else { "()" }))
                .collect();
            format!("(e-lambda {} {} {a} {b})", list(ps), go(body))
        }
        Exp::App { fun, args } => format!("(e-app {} {} {a} {b})", go(fun), list(args.iter().map(|x| go(*x)).collect())),
        Exp::PLambda { body, .. } => format!("(e-plambda _ {} {a} {b})", go(body)),
        Exp::Proj { body, args } => format!("(e-proj {} {} {a} {b})", go(body), list(vec!["_".into(); args.len()])),
        Exp::If { test, then, els } => format!("(e-if {} {} {} {a} {b})", go(test), go(then), go(els)),
        Exp::Letrec { bindings, body } => {
            let bs = bindings.iter().map(|(n, _, x)| format!("[{} _ {}]", name(*n), go(*x))).collect();
            format!("(e-letrec {} {} {a} {b})", list(bs), go(body))
        }
        Exp::Let { bindings, body } => {
            let bs = bindings.iter().map(|(n, x)| format!("[{} {}]", name(*n), go(*x))).collect();
            format!("(e-let {} {} {a} {b})", list(bs), go(body))
        }
        Exp::Begin(items) => format!("(e-begin {} {a} {b})", list(items.iter().map(|x| go(*x)).collect())),
        Exp::Prompt { tag, body, handler } => format!("(e-prompt {} {} {} {a} {b})", go(tag), go(body), go(handler)),
        Exp::The { exp, .. } => format!("(e-the _ {} {a} {b})", go(exp)),
        Exp::Bloblet { op, args } => {
            let (n, i) = match op {
                BlobletOp::Make => ("make-bloblet", -1),
                BlobletOp::Ref(i) => ("bloblet-ref", i as i64),
                BlobletOp::Set(i) => ("bloblet-set!", i as i64),
                BlobletOp::Freeze => ("bloblet-freeze", -1),
                BlobletOp::Byte => ("bloblet-byte", -1),
                BlobletOp::SetByte => ("bloblet-set-byte!", -1),
                BlobletOp::Bytes => ("bloblet-bytes", -1),
            };
            format!("(e-bloblet {n} {i} {} {a} {b})", list(args.iter().map(|x| go(*x)).collect()))
        }
        Exp::Product(fields) => {
            let fs = fields.iter().map(|(l, x)| format!("[{} {}]", name(*l), go(*x))).collect();
            format!("(e-product {} {a} {b})", list(fs))
        }
        Exp::Extract(x, l) => format!("(e-extract {} {} {a} {b})", go(x), name(l)),
        Exp::Sum(t, x) => format!("(e-sum {} {} {a} {b})", name(t), go(x)),
        Exp::TagCase { scrutinee, arms, els } => {
            let arms = arms
                .iter()
                .map(|arm| {
                    let fields = matches!(arm.bind, ArmBind::Fields(_));
                    let names: Vec<String> = arm.names().iter().map(|n| name(*n)).collect();
                    format!("[{} {} {} {}]", name(arm.tag), if fields { "#t" } else { "#f" }, list(names), go(arm.body))
                })
                .collect();
            let els = els.iter().map(|(y, x)| format!("[{} {}]", name(*y), go(*x))).collect();
            format!("(e-tagcase {} {} {} {a} {b})", go(scrutinee), list(arms), list(els))
        }
    }
}
