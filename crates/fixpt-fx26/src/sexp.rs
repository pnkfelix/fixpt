//! Syntax trees as text, to compare the parser written in FX-26 with the
//! Rust one (`PLAN.md` §11, step 9a).
//!
//! [`show_value`] prints any FX-26 data from the heap: a sum as its tag and
//! its product's fields, `(tag f …)`; a product elsewhere as `[f …]`; a list
//! as `(x …)`; a `syn` (a description, kept as it was written) as `_`.
//! [`show_top`] prints the Rust parser's tree in exactly that shape, from the
//! parser's datatypes in `parser.fx`, with spans in characters.

use crate::ast::{ArmBind, BlobletOp, Exp, ExpId, RegionForm};
use crate::check::Checker;
use crate::top::Top;
use fixpt_heap::layout::kind;
use fixpt_scheme::Local;

/// FX-26 data on the heap, as text.
pub fn show_value(v: Local<'_>) -> String {
    if let Some(n) = v.fixnum() {
        return n.to_string();
    }
    if v.is_true() || v.is_false() {
        return (if v.is_true() { "#t" } else { "#f" }).into();
    }
    if let Some(c) = v.char() {
        return format!("{c:?}");
    }
    if let Some(x) = v.flonum() {
        return fixpt_runtime::num::format_flonum(x);
    }
    if let Some(items) = v.list() {
        let parts: Vec<String> = items.into_iter().map(show_value).collect();
        return format!("({})", parts.join(" "));
    }
    if let Some(n) = v.symbol_name() {
        return n;
    }
    if let Some(s) = v.string() {
        return format!("{s:?}");
    }
    if v.bloblet_kind() == Some(kind("sum")) {
        let tag = v.field(2).and_then(|t| t.symbol_name()).unwrap_or_default();
        if matches!(tag.as_str(), "atom" | "lst" | "dotted" | "vec") {
            return "_".into();
        }
        let mut out = format!("({tag}");
        for f in fields(v.field(3).expect("a sum's value")) {
            out.push(' ');
            out.push_str(&show_value(f));
        }
        out.push(')');
        return out;
    }
    if v.bloblet_kind() == Some(kind("product")) {
        let parts: Vec<String> = fields(v).into_iter().map(show_value).collect();
        return format!("[{}]", parts.join(" "));
    }
    v.write()
}

/// A product's fields, in order.
fn fields(p: Local<'_>) -> Vec<Local<'_>> {
    (2..).map_while(|k| p.field(k)).collect()
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
        Top::Define { name, exp, typed, inferred, .. } => {
            // A `define*`'s type is a list of the type and the `define*`.
            let ty = match (typed, inferred) {
                (_, true) => "(_ _)",
                (true, _) => "(_)",
                _ => "()",
            };
            format!("(t-define {} {ty} {} {a} {b})", c.interner.name(*name), show_exp(c, chars, *exp))
        }
        Top::DefineRec { bindings, .. } => {
            let bs: Vec<String> =
                bindings.iter().map(|(n, _, e)| format!("[{} _ {}]", c.interner.name(*n), show_exp(c, chars, *e))).collect();
            format!("(t-define-rec ({}) {a} {b})", bs.join(" "))
        }
        Top::DefineType { .. } | Top::DefineTypeFamily { .. } => format!("(t-define-type _ _ {a} {b})"),
        Top::DefineGenerative { .. } => format!("(t-define-generative _ _ {a} {b})"),
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
        Exp::Float(x) => format!("(e-float {} {a} {b})", fixpt_runtime::num::format_flonum(x)),
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
        Exp::RLambda { region, lambda } => format!("(e-rlambda {} {} {a} {b})", go(region), go(lambda)),
        Exp::LetRegion { form, region, body } => {
            let (k, into) = match form {
                RegionForm::Region => (0, None),
                RegionForm::Arena => (1, None),
                RegionForm::Reap => (2, None),
                RegionForm::Freeze(into) => (3, into),
            };
            let into = into.map_or("heap".to_string(), |p| name(c.arena.dvar_name(p)));
            format!("(e-letregion {k} {} {into} {} {a} {b})", name(c.arena.dvar_name(region)), go(body))
        }
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
        Exp::Convention { exp, .. } => format!("(e-convention _ {} {a} {b})", go(exp)),
        Exp::Bloblet { op, args } => {
            let (n, i) = match op {
                BlobletOp::Make => ("make-bloblet", -1),
                BlobletOp::RMake => ("rmake-bloblet", -1),
                BlobletOp::Ref(i) => ("bloblet-ref", i as i64),
                BlobletOp::Set(i) => ("bloblet-set!", i as i64),
                BlobletOp::Freeze => ("bloblet-freeze", -1),
                BlobletOp::Byte => ("bloblet-byte", -1),
                BlobletOp::SetByte => ("bloblet-set-byte!", -1),
                BlobletOp::Bytes => ("bloblet-bytes", -1),
            };
            format!("(e-bloblet {n} {i} {} {a} {b})", list(args.iter().map(|x| go(*x)).collect()))
        }
        // Not in the parser written in FX-26 yet (`first-class-modules.md`, M2).
        Exp::Module(_) => format!("(e-module {a} {b})"),
        Exp::With { module, body } => format!("(e-with {} {} {a} {b})", name(module), go(body)),
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
