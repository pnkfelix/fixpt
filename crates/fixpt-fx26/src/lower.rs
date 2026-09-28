//! Lowering to Scheme that keeps what the checker proved.
//!
//! Not erasure. FX-87's eraser threw the checker's knowledge away, and adding
//! it back as `%fx-note` claims was an afterthought (README, "What a front end
//! proves, the compiler uses"). Here the claims are the point: the output is
//! ordinary Scheme, runnable by any Scheme, and wherever the checker proved
//! something the compiler can use, the expression carries it as an inert
//! quoted note —
//!
//! ```scheme
//! (begin '(%fx-note (integrable car) (pure) (basis checked) (because "pure"))
//!        (car fx:p))
//! ```
//!
//! — which the expander reads into the Core IR's facts table. Three claims:
//!
//! * `(integrable P)` — the operator is the standard binding for the Scheme
//!   primitive `P`. The initial environment cannot be assigned (a later
//!   `define` of the same name *shadows* it, and is lowered to another
//!   global), so the call may skip the global.
//! * `(pure)` — the application's effect, after masking, is `pure`, so its
//!   value may be dropped when unused.
//! * `(no-escape)` — the expression allocates, masking removed every
//!   allocation, and its value is first-order data, which could hold no
//!   closure keeping an allocation its type does not name: nothing it
//!   allocates outlives it.
//!
//! Descriptions go: `plambda` lowers to its body, `proj` to its operand, `the`
//! to its expression, and parameter types are dropped. A program's own names
//! are prefixed `fx:`, so they can neither capture nor clobber a Scheme name,
//! and a top-level name defined twice becomes two globals, since the second
//! `define` shadows the first rather than assigning it.

use crate::ast::{ArmBind, BlobletOp, Exp, ExpId};
use crate::check::Checker;
use fixpt_read::Sym;
use std::collections::HashMap;

/// How each standard FX-26 name is lowered, and whether it means exactly what
/// the Scheme name does — in which case, if the engine has it as a
/// primitive, an application may be claimed `integrable`.
pub const STANDARD: &[(&str, &str, bool)] = &[
    ("+", "+", true),
    ("-", "-", true),
    ("length", "length", true),
    ("=", "=", true),
    ("cons", "cons", true),
    ("rcons", "%region-cons", false),
    ("rnew", "%region-new", false),
    ("rmake-array", "%region-make-array", false),
    ("rmake-icell", "%region-make-icell", false),
    ("car", "car", true),
    ("cdr", "cdr", true),
    ("null?", "null?", true),
    ("nil", "'()", false),
    ("set-car!", "%fx26-set-car!", false),
    ("stay-cellular", "%stay-cellular", false),
    ("set-cdr!", "%fx26-set-cdr!", false),
    ("new", "%fx26-new", false),
    ("get", "%fx26-get", false),
    ("set", "%fx26-set", false),
    ("cwcc", "call/cc", false),
    ("<", "<", true),
    (">", ">", true),
    ("<=", "<=", true),
    (">=", ">=", true),
    ("*", "*", true),
    ("modulo", "modulo", true),
    ("quotient", "quotient", true),
    ("not", "not", true),
    ("char=?", "char=?", true),
    ("char-whitespace?", "char-whitespace?", true),
    ("char-numeric?", "char-numeric?", true),
    ("char-alphabetic?", "char-alphabetic?", true),
    ("char-downcase", "char-downcase", true),
    ("char->integer", "char->integer", true),
    ("integer->char", "integer->char", true),
    ("char-in?", "%fx26-char-in?", false),
    ("string-append", "string-append", true),
    ("string-length", "string-length", true),
    ("string-ref", "string-ref", true),
    ("substring", "substring", true),
    ("string=?", "string=?", true),
    ("string-ci=?", "%fx26-string-ci=?", false),
    ("string-downcase", "%fx26-string-downcase", false),
    ("char->string", "string", false),
    ("list->string", "list->string", true),
    ("string->list", "string->list", true),
    ("reverse", "reverse", true),
    ("parse-number", "%fx26-parse-number", false),
    ("parse-int", "%fx26-parse-int", false),
    ("datum-char", "%fx26-identity", false),
    ("datum-string", "%fx26-string-copy", false),
    ("datum-symbol", "string->symbol", false),
    ("datum-bool", "%fx26-identity", false),
    ("datum-int", "%fx26-identity", false),
    ("datum-list", "%fx26-list-copy", false),
    ("datum-cons", "cons", true),
    ("datum-dotted", "append", false),
    ("datum-list->vector", "list->vector", false),
    ("datum-list->bytevector", "%fx26-bytevector", false),
    ("datum-char-value", "%fx26-identity", false),
    ("datum-byte?", "%fx26-byte?", false),
    ("datum-proper-list?", "%fx26-list?", false),
    ("datum-pair?", "pair?", false),
    ("datum-null?", "null?", false),
    ("datum-car", "car", false),
    ("acyclic?", "%fx26-acyclic?", false),
    ("certify-acyclic", "%fx26-identity", false),
    ("nat?", "%fx26-nat?", false),
    ("certify-nat", "%fx26-identity", false),
    ("length-is?", "%fx26-length-is?", false),
    ("certify-length", "%fx26-first", false),
    ("datum-cdr", "cdr", false),
    ("datum-symbol?", "symbol?", false),
    ("datum-symbol-name", "symbol->string", false),
    ("datum-int?", "%fx26-fixnum?", false),
    ("datum-int-value", "%fx26-identity", false),
    ("datum-string?", "string?", false),
    ("datum-string-value", "%fx26-identity", false),
    ("datum-bool?", "boolean?", false),
    ("datum-bool-value", "%fx26-identity", false),
    ("datum-char?", "char?", false),
    ("datum->symbol", "%fx26-identity", false),
    ("int->string", "number->string", false),
    ("string->symbol", "string->symbol", true),
    ("symbol->string", "symbol->string", true),
    ("symbol=?", "eq?", false),
    ("string-hash", "%string-hash", false),
    ("symbol-name-hash", "%symbol-hash", false),
    ("make-array", "%fx26-make-array", false),
    ("array-ref", "%fx26-array-ref", false),
    ("array-set!", "%fx26-array-set!", false),
    ("array-length", "%fx26-array-length", false),
    ("make-icell", "%fx26-make-icell", false),
    ("icell-put!", "%fx26-icell-put!", false),
    ("icell-get", "%fx26-icell-get", false),
    ("make-word", "%make-word", false),
    ("set-register-twin", "%set-register-twin", false),
    ("tword-fields", "%tword-fields", false),
    ("disassemble", "%disassemble", false),
    ("tword-int?", "%tword-fixnum?", false),
    ("tword-int", "%tword-int", false),
    ("wcell-routine", "%fx26-identity", false),
    ("wcell-int", "%fx26-identity", false),
    ("wcell-bool", "%fx26-identity", false),
    ("wcell-string", "%fx26-identity", false),
    ("wcell-char", "%fx26-identity", false),
    ("wcell-symbol", "%fx26-identity", false),
    ("wcell-unit", "%fx26-unit-cell", false),
    ("wcell-word", "%fx26-identity", false),
    ("wcell-global", "%fx26-identity", false),
    ("wcell-self", "%default-object", false),
    ("wcell-nil", "%fx26-nil-cell", false),
    ("make-global", "%fx26-make-global", false),
    ("runtime-primitive", "%runtime-primitive", false),
    ("make-continuation-prompt-tag", "%fx26-make-prompt-tag", false),
    ("abort-current-continuation", "%fx26-abort", false),
    ("call-with-composable-continuation", "%fx26-call/comp", false),
    ("make-continuation-mark-key", "%fx26-make-mark-key", false),
    ("with-mark", "%fx26-with-mark", false),
    ("first-mark", "%fx26-first-mark", false),
    ("current-marks", "%fx26-current-marks", false),
    ("marks-of", "%fx26-marks-of", false),
];

/// The FX-26 copy of what [`STANDARD`] says the compiler written in FX-26
/// can use: for each standard name the lowering runs as a runtime primitive
/// the cellular machine can call (`prim`), that primitive; for one it runs
/// as the identity, `%fx26-identity`. `src/standard.fx` is this, and a test
/// keeps it so.
pub fn standard_fx26_module() -> String {
    let mut out = String::from(include_str!("standard-header.fx"));
    for (fx, scheme, _) in STANDARD {
        if *scheme == "%fx26-identity" || fixpt_engine::cellular::runtime_primitive(scheme).is_some() {
            out.push_str(&format!("      ((string=? n {fx:?}) {scheme:?})\n"));
        }
    }
    out.push_str("      (else \"\"))))\n");
    out
}

/// The Scheme names of a program's top-level definitions.
#[derive(Debug, Clone)]
pub struct Globals {
    /// What every one of them starts with: `fx:`, unless the program is to
    /// share a Scheme session with another FX-26 program and keep out of its
    /// way — the eager reader loaded beside the REPL's user program.
    prefix: String,
    /// The current global for each name.
    current: HashMap<Sym, String>,
    /// How many times each name has been defined.
    defined: HashMap<Sym, usize>,
    /// Names whose next definition keeps their global (`keep_next`).
    keep: Vec<Sym>,
}

impl Default for Globals {
    fn default() -> Globals {
        Globals::with_prefix("fx:")
    }
}

impl Globals {
    pub fn with_prefix(prefix: &str) -> Globals {
        Globals { prefix: prefix.to_string(), current: HashMap::new(), defined: HashMap::new(), keep: Vec::new() }
    }

    /// The next definition of `name` keeps the global it has: every use of
    /// it, before and after, sees the new value (a redefinition of a type
    /// its users can take; `Fx26Session`'s redefinition).
    pub fn keep_next(&mut self, name: Sym) {
        self.keep.push(name);
    }

    /// The global a new definition of `name` gets, which becomes the one
    /// later uses of `name` refer to: a new one, unless `keep_next` asked
    /// for the one it has.
    pub fn define(&mut self, c: &Checker, name: Sym) -> String {
        if let Some(k) = self.keep.iter().position(|n| *n == name) {
            self.keep.remove(k);
            if let Some(g) = self.current.get(&name) {
                return g.clone();
            }
        }
        let n = self.defined.entry(name).or_insert(0);
        *n += 1;
        let base = format!("{}{}", self.prefix, fixpt_read::escape_symbol(c.interner.name(name)));
        let global = if *n == 1 { base } else { format!("{base}:{n}") };
        self.current.insert(name, global.clone());
        global
    }

    pub fn get(&self, name: Sym) -> Option<&str> {
        self.current.get(&name).map(String::as_str)
    }
}

pub struct Lowerer<'a> {
    c: &'a Checker,
    globals: &'a Globals,
    /// Names bound by an enclosing `lambda`, `let` or `letrec`.
    locals: Vec<Sym>,
}

/// Lower one checked expression.
pub fn lower(c: &Checker, globals: &Globals, e: ExpId) -> String {
    Lowerer { c, globals, locals: Vec::new() }.go(e)
}

impl Lowerer<'_> {
    fn local(&self, s: Sym) -> String {
        format!("fx:{}", fixpt_read::escape_symbol(self.c.interner.name(s)))
    }

    fn var(&self, s: Sym) -> String {
        if self.locals.contains(&s) {
            return self.local(s);
        }
        if let Some(g) = self.globals.get(s) {
            return g.to_string();
        }
        let name = self.c.interner.name(s);
        match STANDARD.iter().find(|(n, _, _)| *n == name) {
            Some((_, scheme, _)) => scheme.to_string(),
            // Checked code names nothing else; keep it visible if it does.
            None => format!("{}{}", self.globals.prefix, fixpt_read::escape_symbol(name)),
        }
    }

    fn body(&mut self, bound: &[Sym], e: ExpId) -> String {
        let depth = self.locals.len();
        self.locals.extend_from_slice(bound);
        let out = self.go(e);
        self.locals.truncate(depth);
        out
    }

    fn go(&mut self, e: ExpId) -> String {
        let code = match self.c.arena.exp_at(e).clone() {
            Exp::Var(s) => self.var(s),
            Exp::Int(n) => n.to_string(),
            Exp::Bool(b) => (if b { "#t" } else { "#f" }).into(),
            Exp::Str(s) => scheme_string(&s),
            Exp::Symbol(s) => format!("'{}", fixpt_read::escape_symbol(self.c.interner.name(s))),
            Exp::Char(c) if c.is_ascii_alphanumeric() => format!("#\\{c}"),
            Exp::Char(c) => format!("#\\x{:x}", c as u32),
            Exp::Unit => "%fx26-unit".into(),
            Exp::Lambda { params, body } => {
                let names: Vec<Sym> = params.iter().map(|(n, _)| *n).collect();
                let ps: Vec<String> = names.iter().map(|n| self.local(*n)).collect();
                format!("(lambda ({}) {})", ps.join(" "), self.body(&names, body))
            }
            Exp::App { fun, args } => {
                let mut parts = vec![self.go(fun)];
                parts.extend(args.iter().map(|a| self.go(*a)));
                format!("({})", parts.join(" "))
            }
            // Regions are erased: a `letrena`'s or `letreap`'s allocation is the heap's.
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } => self.go(body),
            // Regions are erased here: the closure is the heap's.
            Exp::RLambda { lambda, .. } => self.go(lambda),
            // A region's name is its handle, the region left however the
            // body is, by a return or an escape: a `dynamic-wind`'s after
            // (the checker lets no body of a region be resumed, so its
            // before never runs again).
            Exp::LetRegion { form, region, body } => {
                let n = self.c.arena.dvar_name(region);
                let Some(enter) = form.enter() else {
                    // A region for analysis only: nothing at run time.
                    return self.go(body);
                };
                let l = self.local(n);
                let b = self.body(&[n], body);
                format!("(let (({l} ({enter}))) (dynamic-wind (lambda () #f) (lambda () {b}) (lambda () (%region-exit {l} #f))))")
            }
            Exp::The { exp, .. } | Exp::Convention { exp, .. } => self.go(exp),
            Exp::If { test, then, els } => {
                format!("(if {} {} {})", self.go(test), self.go(then), self.go(els))
            }
            Exp::Letrec { bindings, body } => {
                let names: Vec<Sym> = bindings.iter().map(|(n, _, _)| *n).collect();
                let depth = self.locals.len();
                self.locals.extend_from_slice(&names);
                let bs: Vec<String> =
                    bindings.iter().map(|(n, _, init)| format!("({} {})", self.local(*n), self.go(*init))).collect();
                let b = self.go(body);
                self.locals.truncate(depth);
                format!("(letrec* ({}) {b})", bs.join(" "))
            }
            Exp::Let { bindings, body } => {
                let bs: Vec<String> =
                    bindings.iter().map(|(n, init)| format!("({} {})", self.local(*n), self.go(*init))).collect();
                let names: Vec<Sym> = bindings.iter().map(|(n, _)| *n).collect();
                format!("(let ({}) {})", bs.join(" "), self.body(&names, body))
            }
            Exp::Begin(items) => {
                let parts: Vec<String> = items.iter().map(|i| self.go(*i)).collect();
                format!("(begin {})", parts.join(" "))
            }
            Exp::Bloblet { op, args } => {
                let a: Vec<String> = args.iter().map(|x| self.go(*x)).collect();
                // Field `i` is the object model's field `i + 2`, after the
                // trailer.
                match op {
                    BlobletOp::Make => format!("(%make-bloblet {})", a.join(" ")),
                    BlobletOp::RMake => format!("(%region-make-bloblet {})", a.join(" ")),
                    BlobletOp::Ref(i) => format!("(%bloblet-ref {} {})", a[0], i + 2),
                    BlobletOp::Set(i) => format!("(%fx26-bloblet-set! {} {} {})", a[0], i + 2, a[1]),
                    BlobletOp::Freeze => format!("(%fx26-bloblet-freeze {})", a[0]),
                    BlobletOp::Byte => format!("(%bloblet-byte {} {})", a[0], a[1]),
                    BlobletOp::SetByte => format!("(%fx26-bloblet-set-byte! {} {} {})", a[0], a[1], a[2]),
                    BlobletOp::Bytes => format!("(%bloblet-bytes {})", a[0]),
                }
            }
            // Immutable data is a frozen bloblet: a product's fields in
            // order; a sum's tag, as a symbol, and its value.
            Exp::Product(fields) => {
                let a: Vec<String> = fields.iter().map(|(_, x)| self.go(*x)).collect();
                format!("(%fx26-product {})", a.join(" "))
            }
            Exp::Extract(x, _) => {
                let i = self.c.facts.field_index[&e];
                format!("(%bloblet-ref {} {})", self.go(x), i + 2)
            }
            Exp::Sum(tag, x) => {
                format!("(%fx26-sum '{} {})", fixpt_read::escape_symbol(self.c.interner.name(tag)), self.go(x))
            }
            Exp::TagCase { scrutinee, arms, els } => {
                let s = self.go(scrutinee);
                let mut out = match els {
                    Some((y, body)) => format!("(let (({} %fx26-tc)) {})", self.local(y), self.body(&[y], body)),
                    None => "(%fx26-no-arm %fx26-tc)".to_string(),
                };
                for arm in arms.iter().rev() {
                    let names = arm.names();
                    let binds: Vec<String> = match &arm.bind {
                        ArmBind::Value(x) => vec![format!("({} (%bloblet-ref %fx26-tc 3))", self.local(*x))],
                        ArmBind::Fields(xs) => xs
                            .iter()
                            .enumerate()
                            .map(|(i, x)| format!("({} (%bloblet-ref (%bloblet-ref %fx26-tc 3) {}))", self.local(*x), i + 2))
                            .collect(),
                    };
                    let body = self.body(&names, arm.body);
                    out = format!(
                        "(if (eq? (%bloblet-ref %fx26-tc 2) '{}) (let ({}) {body}) {out})",
                        fixpt_read::escape_symbol(self.c.interner.name(arm.tag)),
                        binds.join(" ")
                    );
                }
                format!("(let ((%fx26-tc {s})) {out})")
            }
            Exp::Prompt { tag, body, handler } => format!(
                "(call-with-continuation-prompt (lambda () {}) {} {})",
                self.go(body),
                self.go(tag),
                self.go(handler)
            ),
        };
        self.annotate(e, code)
    }

    /// Wrap `code` in the claims the checker proved about `e`, if any.
    fn annotate(&self, e: ExpId, code: String) -> String {
        let facts = &self.c.facts;
        let mut claims = Vec::new();
        let is_app = matches!(self.c.arena.exp_at(e), Exp::App { .. });
        if is_app
            && let Some(s) = facts.standard_operator.get(&e)
        {
            let name = self.c.interner.name(*s);
            if let Some((_, scheme, true)) = STANDARD.iter().find(|(n, _, _)| *n == name) {
                claims.push(format!("(integrable {scheme})"));
            }
        }
        let effect = facts.effects.get(&e);
        if is_app && effect.is_some_and(|x| x.is_pure()) {
            claims.push("(pure)".into());
        }
        if facts.no_escape.contains(&e) {
            claims.push("(no-escape)".into());
        }
        if claims.is_empty() {
            return code;
        }
        let because = effect.map(|x| self.c.show_effect(x)).unwrap_or_default();
        format!("(begin '(%fx-note {} (basis checked) (because {because:?})) {code})", claims.join(" "))
    }
}

/// A string literal in Scheme's syntax.
fn scheme_string(s: &str) -> String {
    let mut out = String::from("\"");
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
