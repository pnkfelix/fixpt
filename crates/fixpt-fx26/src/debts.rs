//! Failure as proof debt, measured (`TODO.md` §86, stage 1;
//! `docs/research/failure-and-blame.md`, section 7). A research tool: what
//! the checker already knows, read back after a program is checked with
//! `Checker::record_operands`, to say how far an inferred "may fail" would
//! spread.
//!
//! A *debt* is an application of a standard operation that may fail. It is
//! *discharged* where types rule the failure out (`car` of a `pairof`, a
//! division by a nonzero literal); else it is *passed* to callers where the
//! operand comes from a parameter (the parameter itself, or a `car`, `cdr`
//! or `extract` of one), *owed* within the definition otherwise, and
//! *stated* for `error`. A *unit* is a definition: a top-level `define` or
//! `define-rec`, or a module's item. Its nested `lambda`s are its own; a
//! nested `module`'s items are units of their own.
//!
//! Approximations, each on the side of more debt: a local bound from a
//! parameter is not followed (its debts count as owed, not passed); a call
//! is linked to every unit of its name, whichever module defines it.

use crate::ast::{Arm, Exp, ExpId, ModItem, Ty};
use crate::check::Checker;
use crate::top::Top;
use fixpt_read::Sym;
use std::collections::{HashMap, HashSet};

/// How one debt stands.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Debt {
    Discharged,
    Owed,
    Passed,
    Stated,
}

/// A definition, and what it does that may fail.
#[derive(Debug)]
pub struct Unit {
    pub name: Sym,
    /// Each debt: the standard operation's name, and how it stands.
    pub debts: Vec<(String, Debt)>,
    /// The other units' names it calls.
    pub calls: HashSet<Sym>,
    /// How many of its calls are of a procedure it was given.
    pub calls_given: usize,
}

impl Unit {
    /// The worst of its own debts: `Stated` over `Passed` over `Owed`; none
    /// if every one is discharged.
    pub fn worst(&self) -> Option<Debt> {
        [Debt::Stated, Debt::Passed, Debt::Owed].into_iter().find(|k| self.debts.iter().any(|(_, d)| d == k))
    }
}

/// Standard operations that are not `pure` but cannot fail: the store's,
/// the I/O primitives' (a failure a value), control's that always return.
const FAIL_FREE: &[&str] = &[
    "new", "get", "set", "make-icell", "write-out", "write-err", "read-line", "read-byte", "stdin-ready?", "terminal-raw",
    "terminal-restore", "terminal-size", "read-file", "type-at", "list-dir", "write-file", "clock", "args",
    "sleep-until", "exit", "list", "length", "array-length", "bytevector-length", "flatarray-length", "string->list", "int->string",
    "acyclic?", "length-is?", "nat?", "certify-acyclic", "certify-nat", "certify-length", "cwcc", "make-continuation-prompt-tag",
    "make-continuation-mark-key", "with-mark", "current-marks", "first-mark", "marks-of", "%quote", "string->utf8", "utf8->string",
    "bytevector=?", "make-table", "table-ref", "table-set!", "table-delete!", "table-count",
];

/// Whether standard operation `n` cannot fail.
fn fail_free(n: &str) -> bool {
    crate::lower::total_operation(n) || FAIL_FREE.contains(&n)
}

/// `e` under any `the` and `proj`.
fn under(c: &Checker, mut e: ExpId) -> ExpId {
    while let Exp::The { exp: x, .. } | Exp::Proj { body: x, .. } = c.arena.exp_at(e) {
        e = *x;
    }
    e
}

struct Walk<'a> {
    c: &'a Checker,
    units: Vec<Unit>,
}

impl Walk<'_> {
    /// A unit of `name`, its value `init`.
    fn unit(&mut self, name: Sym, init: ExpId) {
        let mut x = under(self.c, init);
        while let Exp::PLambda { body, .. } = self.c.arena.exp_at(x) {
            x = under(self.c, *body);
        }
        let params: Vec<Sym> = match self.c.arena.exp_at(x) {
            Exp::Lambda { params, .. } => params.iter().map(|(p, _)| *p).collect(),
            _ => Vec::new(),
        };
        let i = self.units.len();
        self.units.push(Unit { name, debts: Vec::new(), calls: HashSet::new(), calls_given: 0 });
        self.walk(init, Some(i), &params);
    }

    /// Whether `e` is a parameter, or a path from one.
    fn from_param(&self, e: ExpId, params: &[Sym]) -> bool {
        let e = under(self.c, e);
        match self.c.arena.exp_at(e) {
            Exp::Var(v) => params.contains(v),
            Exp::Extract(x, _) => self.from_param(*x, params),
            Exp::App { args, .. } => {
                let path = self.c.facts.standard_operator.get(&e).is_some_and(|s| matches!(self.c.interner.name(*s), "car" | "cdr"));
                path && args.len() == 1 && self.from_param(args[0], params)
            }
            _ => false,
        }
    }

    /// How a debt on `operands` stands: passed if one comes from a parameter.
    fn owed_or_passed(&self, operands: &[ExpId], params: &[Sym]) -> Debt {
        if operands.iter().any(|a| self.from_param(*a, params)) { Debt::Passed } else { Debt::Owed }
    }

    /// Whether application `e`'s operand `i`, as instantiating it found its
    /// type, is one `ok` accepts.
    fn operand(&self, e: ExpId, i: usize, ok: impl Fn(&Ty) -> bool) -> bool {
        let ty = self.c.facts.operand_types.get(&e).and_then(|ts| ts.get(i).copied().flatten());
        ty.is_some_and(|t| ok(self.c.arena.get(self.c.arena.resolve(t))))
    }

    fn debt(&self, e: ExpId, name: &str, args: &[ExpId], params: &[Sym]) -> Option<Debt> {
        if fail_free(name) {
            return None;
        }
        Some(match name {
            "error" => Debt::Stated,
            // An index the facts showed within its array's length
            // (`NodeFacts::in_bounds`, `TODO.md` §77).
            "array-ref" | "array-set!" if self.c.facts.in_bounds.contains(&e) => Debt::Discharged,
            "car" | "cdr" => {
                let ty = self.c.facts.operand_types.get(&e).and_then(|ts| ts.first().copied().flatten());
                let pair = ty.is_some_and(|t| matches!(self.c.arena.get(self.c.arena.resolve(t)), Ty::Pair(_, _, _, false)));
                if pair { Debt::Discharged } else { self.owed_or_passed(&args[..1.min(args.len())], params) }
            }
            // A list walked, which only a cycle fails: none at a frozen region.
            "reverse" | "append" | "list-length" | "list->array" => {
                if self.operand(e, 0, |t| matches!(t, Ty::Nil) || matches!(t, Ty::Pair(_, _, r, _) if r.is_frozen())) {
                    Debt::Discharged
                } else {
                    self.owed_or_passed(&args[..1.min(args.len())], params)
                }
            }
            // A length below 0 fails: none of a `nat`, or a literal.
            "make-array" | "make-bytevector" => {
                let literal = args.first().is_some_and(|a| matches!(self.c.arena.exp_at(under(self.c, *a)), Exp::Int(k) if *k >= 0));
                if literal || self.operand(e, 0, |t| matches!(t, Ty::Nat(_))) {
                    Debt::Discharged
                } else {
                    self.owed_or_passed(&args[..1.min(args.len())], params)
                }
            }
            n if matches!(n, "quotient" | "remainder" | "modulo") || n.ends_with("-quotient") || n.ends_with("-remainder") => {
                match args.get(1).map(|d| self.c.arena.exp_at(under(self.c, *d))) {
                    Some(Exp::Int(k)) if *k != 0 => Debt::Discharged,
                    _ => self.owed_or_passed(&args[1.min(args.len())..], params),
                }
            }
            _ => self.owed_or_passed(args, params),
        })
    }

    /// `e`, within unit `at` (none outside every unit) whose parameters are
    /// `params`.
    fn walk(&mut self, e: ExpId, at: Option<usize>, params: &[Sym]) {
        let c = self.c;
        match c.arena.exp_at(e).clone() {
            // An element of a flat array: discharged where the facts showed
            // the index within its length (`NodeFacts::in_bounds`, N5c).
            Exp::Bloblet { op: crate::ast::BlobletOp::RefIndex, args } => {
                if let Some(i) = at {
                    let d = if c.facts.in_bounds.contains(&e) { Debt::Discharged } else { self.owed_or_passed(&args, params) };
                    self.units[i].debts.push(("blobref-index".into(), d));
                }
                for a in args {
                    self.walk(a, at, params);
                }
            }
            Exp::App { fun, args } => {
                if let (Some(i), Some(s)) = (at, c.facts.standard_operator.get(&e)) {
                    let name = c.interner.name(*s).to_string();
                    if let Some(d) = self.debt(e, &name, &args, params) {
                        self.units[i].debts.push((name, d));
                    }
                } else if let (Some(i), Exp::Var(f)) = (at, c.arena.exp_at(under(c, fun))) {
                    if params.contains(f) {
                        self.units[i].calls_given += 1;
                    } else {
                        self.units[i].calls.insert(*f);
                    }
                }
                self.walk(fun, at, params);
                for a in args {
                    self.walk(a, at, params);
                }
            }
            Exp::Module(items) => {
                for item in items {
                    match item {
                        ModItem::Val { name, init, .. } => self.unit(name, init),
                        ModItem::Rec(bs) => {
                            for (name, _, init) in bs {
                                self.unit(name, init);
                            }
                        }
                        ModItem::Abs { .. } | ModItem::Desc { .. } => {}
                    }
                }
            }
            Exp::Lambda { body, .. } | Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } => {
                self.walk(body, at, params)
            }
            Exp::Convention { exp, .. } | Exp::Extract(exp, _) | Exp::Sum(_, exp) | Exp::LetRegion { body: exp, .. } => {
                self.walk(exp, at, params)
            }
            Exp::With { body, .. } => self.walk(body, at, params),
            Exp::If { test, then, els } => {
                for x in [test, then, els] {
                    self.walk(x, at, params);
                }
            }
            Exp::Letrec { bindings, body } => {
                for (_, _, x) in bindings {
                    self.walk(x, at, params);
                }
                self.walk(body, at, params);
            }
            Exp::Let { bindings, body } => {
                for (_, x) in bindings {
                    self.walk(x, at, params);
                }
                self.walk(body, at, params);
            }
            Exp::Begin(xs) | Exp::Bloblet { args: xs, .. } => {
                for x in xs {
                    self.walk(x, at, params);
                }
            }
            Exp::Prompt { tag, body, handler } => {
                for x in [tag, body, handler] {
                    self.walk(x, at, params);
                }
            }
            Exp::RLambda { region, lambda } => {
                self.walk(region, at, params);
                self.walk(lambda, at, params);
            }
            Exp::Product(fs) => {
                for (_, x) in fs {
                    self.walk(x, at, params);
                }
            }
            Exp::TagCase { scrutinee, arms, els } => {
                self.walk(scrutinee, at, params);
                for Arm { body, .. } in arms {
                    self.walk(body, at, params);
                }
                if let Some((_, x)) = els {
                    self.walk(x, at, params);
                }
            }
            Exp::Var(_) | Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => {}
        }
    }
}

/// The units of a program checked with `record_operands`, from its
/// top-level forms as `Checker::top_all` gave them.
pub fn units(c: &Checker, tops: &[Top]) -> Vec<Unit> {
    let mut w = Walk { c, units: Vec::new() };
    for t in tops {
        match t {
            Top::Define { name, exp, .. } => w.unit(*name, *exp),
            Top::DefineRec { bindings, .. } => {
                for (name, _, init) in bindings {
                    w.unit(*name, *init);
                }
            }
            Top::Exp(k) => w.walk(k.exp, None, &[]),
            _ => {}
        }
    }
    w.units
}

/// What the measurement found, over some units.
#[derive(Default, Debug)]
pub struct Summary {
    pub units: usize,
    /// Units by their worst own debt; `None`, none undischarged.
    pub by_worst: HashMap<Option<Debt>, usize>,
    /// Units free of debt themselves, but calling one that may fail.
    pub by_call: usize,
    /// Units free of debt, calling none that may fail, but calling a
    /// procedure they were given.
    pub only_given: usize,
    /// Debts by operation and how each stands.
    pub ops: HashMap<(String, Debt), usize>,
}

/// The operations that index (an array, a string, a bytevector): what
/// N5's bounds would discharge (`docs/research/gadts.md`).
pub fn indexes(op: &str) -> bool {
    matches!(op, "array-ref" | "array-set!" | "string-ref" | "substring" | "bytevector-u8-ref" | "bytevector-u8-set!" | "bytevector-copy" | "bytevector-copy!" | "flatarray-ref" | "flatarray-set!")
}

/// The summary of `units`: each unit's own debts, and whether, through the
/// units it calls, it may fail (a fixpoint over the call graph by name).
/// With `discharged`, the debts of the operations it accepts count as
/// discharged: what a stronger type system would give.
pub fn summarize(units: &[Unit], discharged: &dyn Fn(&str) -> bool) -> Summary {
    let worst = |u: &Unit| {
        [Debt::Stated, Debt::Passed, Debt::Owed].into_iter().find(|k| u.debts.iter().any(|(op, d)| d == k && !discharged(op)))
    };
    let mut s = Summary { units: units.len(), ..Summary::default() };
    let mut fails: HashSet<Sym> = units.iter().filter(|u| worst(u).is_some()).map(|u| u.name).collect();
    loop {
        let more: Vec<Sym> = units.iter().filter(|u| !fails.contains(&u.name) && u.calls.iter().any(|f| fails.contains(f))).map(|u| u.name).collect();
        if more.is_empty() {
            break;
        }
        fails.extend(more);
    }
    for u in units {
        let worst = worst(u);
        *s.by_worst.entry(worst).or_default() += 1;
        if worst.is_none() {
            if fails.contains(&u.name) {
                s.by_call += 1;
            } else if u.calls_given > 0 {
                s.only_given += 1;
            }
        }
        for (op, d) in &u.debts {
            *s.ops.entry((op.clone(), *d)).or_default() += 1;
        }
    }
    s
}
