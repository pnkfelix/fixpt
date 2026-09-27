//! Well-founded recursion: which recursive groups need not say `spin`.
//!
//! Size-change termination (Lee, Jones and Ben-Amram, POPL 2001): each call
//! from one member of a group to another is a graph saying how the callee's
//! arguments relate to the caller's parameters — a part of one (strictly
//! smaller), the same (no larger), or unknown. The graphs are closed under
//! composition, and the group ends if every graph from a member to itself
//! that equals its own composition has a parameter strictly smaller.
//!
//! Three measures, each well-founded:
//! - **parts**: a component of a sum or product, the `car` or `cdr` of a
//!   pair at a `finite` region, the `datum-car` or `datum-cdr` of a datum.
//!   Each was made before what holds it, and none can be changed, so no
//!   cycle runs through them;
//! - **down**: an integer less by a literal, where a test has bounded the
//!   parameter below by a literal or a variable fixed for the whole
//!   recursion;
//! - **up**: the same, greater by a literal and bounded above.
//!
//! A member named anywhere but as the operator of a call escapes: something
//! else may call it, with anything, so the group does not pass.

use std::collections::{BTreeMap, HashSet};

use crate::ast::{ArmBind, Exp, ExpId, Region, Ty, TyId};
use fixpt_read::Sym;
use crate::check::Checker;

/// What is known of a value, relative to a parameter of the member whose
/// body is walked.
#[derive(Clone, Copy, Debug)]
enum Tracked {
    /// The parameter, or (`strict`) a part of it; of type `ty`.
    /// The type is `None` where it is not known, as past a generative
    /// type's conversion: a `tagcase` or `extract` still proves a sum or a
    /// product, but a `car` or `cdr` needs to know the list is finite.
    Part { param: usize, strict: bool, ty: Option<TyId> },
    /// The integer parameter plus `offset`.
    Int { param: usize, offset: i64 },
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum Measure {
    Part,
    Down,
    Up,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Bound {
    Lower,
    Upper,
}

/// A size-change graph: (caller slot, callee slot) to whether it is strict.
type Graph = BTreeMap<((usize, Measure), (usize, Measure)), bool>;

/// A graph's closure may grow; beyond this many, the group does not pass.
const MOST_GRAPHS: usize = 4000;

struct Walk<'a> {
    c: &'a Checker,
    members: Vec<Sym>,
    /// The member whose body is walked.
    current: usize,
    /// Names bound on the way down, and what is known of each.
    scope: Vec<(Sym, Vec<Tracked>)>,
    /// Bounds the tests on the way down have put on parameters.
    guards: Vec<(usize, Bound)>,
    calls: Vec<(usize, usize, Graph)>,
    /// For each call, whether it counts an integer down, or up, with no
    /// test bounding it that way.
    unbounded: Vec<Option<&'static str>>,
    /// For each call, what each argument is: a parameter of the caller,
    /// passed unchanged, or not.
    passed: Vec<(usize, usize, Vec<Option<usize>>)>,
    /// (member, parameter): passed unchanged by every call in the group,
    /// so the same for the whole recursion, and a bound as a literal is.
    invariant: HashSet<(usize, usize)>,
    /// A member named other than as a call's operator: (where, which).
    escapes: Option<(usize, usize)>,
}

impl Checker {
    /// Whether every run of the group `bindings` (names, declared types and
    /// lambdas) ends, so that calls within it need not say `spin`; if not,
    /// why not, in words for an error.
    pub(crate) fn termination(&self, bindings: &[(Sym, TyId, ExpId)]) -> Result<(), String> {
        let name = |i: usize| self.interner.name(bindings[i].0).to_string();
        let mut w = self.size_change_walk(bindings);
        let Some(w) = w.as_mut() else {
            return Err("it is not a lambda".into());
        };
        if let Some((at, m)) = w.escapes {
            return Err(format!(
                "`{}` is named in `{}` other than as a call's operator: whoever is given it may call it again, with anything",
                name(m),
                name(at)
            ));
        }
        match size_change_ends(&w.calls) {
            Ends::Yes => Ok(()),
            Ends::TooMany => Err("the calls combine in too many ways to follow".into()),
            Ends::No => {
                let mut flat: Vec<String> = Vec::new();
                for ((from, to, g), unbounded) in w.calls.iter().zip(&w.unbounded) {
                    let mut s = format!("the call of `{}` in `{}`", name(*to), name(*from));
                    if let Some(u) = unbounded {
                        s.push_str(&format!(" ({u})"));
                    }
                    // A call passing its caller's parameters on unchanged
                    // is harmless; one passing nothing related to them, or
                    // with a count unbounded or a part that may be cyclic,
                    // is the one to look at.
                    if (g.is_empty() || unbounded.is_some()) && !g.values().any(|strict| *strict) && !flat.contains(&s) {
                        flat.push(s);
                    }
                }
                Err(if flat.is_empty() {
                    "no argument keeps shrinking around every loop of calls".into()
                } else {
                    format!("nothing smaller, or related, is passed by {}", flat.join(", "))
                })
            }
        }
    }

    /// The walk of the group, with the calls it found; `None` if a member
    /// is not a lambda.
    fn size_change_walk<'a>(&'a self, bindings: &[(Sym, TyId, ExpId)]) -> Option<Walk<'a>> {
        let mut w = Walk {
            c: self,
            members: bindings.iter().map(|(n, _, _)| *n).collect(),
            current: 0,
            scope: Vec::new(),
            guards: Vec::new(),
            calls: Vec::new(),
            unbounded: Vec::new(),
            passed: Vec::new(),
            invariant: HashSet::new(),
            escapes: None,
        };
        let mut arity = Vec::new();
        for (_, _, init) in bindings {
            let Some((params, _)) = self.lambda_of(*init) else { return None };
            arity.push(params.len());
        }
        // Twice: first to learn which parameters every call passes on
        // unchanged, then with them as bounds.
        if !w.walk_members(bindings) {
            return w.escapes.is_some().then_some(w);
        }
        let mut inv: HashSet<(usize, usize)> =
            arity.iter().enumerate().flat_map(|(i, n)| (0..*n).map(move |j| (i, j))).collect();
        loop {
            let before = inv.len();
            for (from, to, args) in &w.passed {
                for j in 0..arity[*to] {
                    let kept = args.get(j).copied().flatten().is_some_and(|p| inv.contains(&(*from, p)));
                    if !kept {
                        inv.remove(&(*to, j));
                    }
                }
            }
            if inv.len() == before {
                break;
            }
        }
        if !inv.is_empty() {
            w.invariant = inv;
            w.calls.clear();
            w.unbounded.clear();
            w.passed.clear();
            if !w.walk_members(bindings) {
                return w.escapes.is_some().then_some(w);
            }
        }
        Some(w)
    }

    /// A binding's lambda, under `plambda`, `the` and `rlambda`: its
    /// parameters and body.
    fn lambda_of(&self, mut e: ExpId) -> Option<(Vec<Sym>, ExpId)> {
        loop {
            match self.arena.exp_at(e) {
                Exp::PLambda { body, .. } | Exp::The { exp: body, .. } => e = *body,
                Exp::RLambda { lambda, .. } => e = *lambda,
                Exp::Lambda { params, body } => return Some((params.iter().map(|(p, _)| *p).collect(), *body)),
                _ => return None,
            }
        }
    }

    /// The parameter types of a declared type, under its binders.
    fn param_types(&self, mut t: TyId) -> Vec<TyId> {
        loop {
            t = self.arena.resolve(t);
            match self.arena.get(t) {
                Ty::Poly { body, .. } => t = *body,
                Ty::Subr { params, .. } => return params.clone(),
                _ => return Vec::new(),
            }
        }
    }
}

impl Walk<'_> {
    /// Walk every member's body; `false` if one is not a lambda or a member
    /// escapes.
    fn walk_members(&mut self, bindings: &[(Sym, TyId, ExpId)]) -> bool {
        let c = self.c;
        for (i, (_, ty, init)) in bindings.iter().enumerate() {
            let Some((params, body)) = c.lambda_of(*init) else { return false };
            let tys = c.param_types(*ty);
            self.current = i;
            self.scope.clear();
            for (j, p) in params.iter().enumerate() {
                let Some(t) = tys.get(j).copied() else { return false };
                let mut known = vec![Tracked::Part { param: j, strict: false, ty: Some(t) }];
                if c.arena.resolve(t) == c.arena.resolve(c.int) {
                    known.push(Tracked::Int { param: j, offset: 0 });
                }
                self.scope.push((*p, known));
            }
            self.walk(body);
            if self.escapes.is_some() {
                return false;
            }
        }
        true
    }

    fn bound(&self, s: Sym) -> Option<&Vec<Tracked>> {
        self.scope.iter().rev().find(|(n, _)| *n == s).map(|(_, k)| k)
    }

    /// The member `s` names here, unless something on the way down hid it.
    fn member(&self, s: Sym) -> Option<usize> {
        if self.bound(s).is_some() {
            return None;
        }
        self.members.iter().position(|m| *m == s)
    }

    /// Whether `e` names a generative type's `up-` or `down-` conversion.
    fn conversion(&self, e: ExpId) -> bool {
        match self.c.arena.exp_at(strip(self.c, e)) {
            Exp::Var(s) => {
                self.bound(*s).is_none()
                    && self.member(*s).is_none()
                    && self.c.lookup(*s).is_some_and(|t| self.c.conversions.contains(&(*s, t)))
            }
            _ => false,
        }
    }

    /// Whether `e` names the standard binding `name`.
    fn is_op(&self, e: ExpId, name: &str) -> bool {
        match self.c.arena.exp_at(strip(self.c, e)) {
            Exp::Var(s) => self.c.interner.name(*s) == name && self.bound(*s).is_none() && self.c.is_standard(*s),
            _ => false,
        }
    }

    fn std_op(&self, e: ExpId) -> Option<&str> {
        match self.c.arena.exp_at(strip(self.c, e)) {
            Exp::Var(s) if self.bound(*s).is_none() && self.members.iter().all(|m| m != s) && self.c.is_standard(*s) => {
                Some(self.c.interner.name(*s))
            }
            _ => None,
        }
    }

    fn walk(&mut self, e: ExpId) {
        match self.c.arena.exp_at(e).clone() {
            Exp::Var(s) => {
                if let Some(m) = self.member(s) {
                    self.escapes.get_or_insert((self.current, m));
                }
            }
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Symbol(_) | Exp::Unit => {}
            Exp::App { fun, args } => {
                let callee = match self.c.arena.exp_at(strip(self.c, fun)) {
                    Exp::Var(s) => self.member(*s),
                    _ => None,
                };
                match callee {
                    Some(to) => self.call(to, &args),
                    None => self.walk(fun),
                }
                for a in args {
                    self.walk(a);
                }
            }
            Exp::Lambda { params, body } => {
                let depth = self.scope.len();
                self.scope.extend(params.iter().map(|(p, _)| (*p, Vec::new())));
                self.walk(body);
                self.scope.truncate(depth);
            }
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } => self.walk(body),
            Exp::LetRegion { body, .. } => self.walk(body),
            Exp::RLambda { region, lambda } => {
                self.walk(region);
                self.walk(lambda);
            }
            Exp::If { test, then, els } => {
                self.walk(test);
                let depth = self.guards.len();
                let facts = self.facts(test, true);
                self.guards.extend(facts);
                self.walk(then);
                self.guards.truncate(depth);
                let facts = self.facts(test, false);
                self.guards.extend(facts);
                self.walk(els);
                self.guards.truncate(depth);
            }
            Exp::Letrec { bindings, body } => {
                let depth = self.scope.len();
                self.scope.extend(bindings.iter().map(|(n, _, _)| (*n, Vec::new())));
                for (_, _, init) in &bindings {
                    self.walk(*init);
                }
                self.walk(body);
                self.scope.truncate(depth);
            }
            Exp::Let { bindings, body } => {
                let mut bound = Vec::new();
                for (n, init) in &bindings {
                    self.walk(*init);
                    bound.push((*n, self.tracked(*init)));
                }
                let depth = self.scope.len();
                self.scope.extend(bound);
                self.walk(body);
                self.scope.truncate(depth);
            }
            Exp::Begin(items) | Exp::Bloblet { args: items, .. } => {
                for i in items {
                    self.walk(i);
                }
            }
            Exp::Prompt { tag, body, handler } => {
                for x in [tag, body, handler] {
                    self.walk(x);
                }
            }
            Exp::Product(fields) => {
                for (_, x) in fields {
                    self.walk(x);
                }
            }
            Exp::Extract(x, _) | Exp::Sum(_, x) => self.walk(x),
            Exp::TagCase { scrutinee, arms, els } => {
                self.walk(scrutinee);
                let whole = self.tracked(scrutinee);
                for arm in &arms {
                    let depth = self.scope.len();
                    match &arm.bind {
                        ArmBind::Value(x) => {
                            let known = self.variant(&whole, arm.tag, None);
                            self.scope.push((*x, known));
                        }
                        ArmBind::Fields(xs) => {
                            for (i, x) in xs.iter().enumerate() {
                                let known = self.variant(&whole, arm.tag, Some(i));
                                self.scope.push((*x, known));
                            }
                        }
                    }
                    self.walk(arm.body);
                    self.scope.truncate(depth);
                }
                if let Some((y, body)) = els {
                    // The same value, its type narrowed.
                    let known = whole.iter().filter(|k| matches!(k, Tracked::Part { .. })).copied().collect();
                    self.scope.push((y, known));
                    self.walk(body);
                    self.scope.pop();
                }
            }
        }
    }

    /// What an arm of a `tagcase` on `whole` binds: the value of variant
    /// `tag`, or its field `field`.
    fn variant(&self, whole: &[Tracked], tag: Sym, field: Option<usize>) -> Vec<Tracked> {
        let arena = &self.c.arena;
        whole
            .iter()
            .filter_map(|k| {
                let Tracked::Part { param, ty, .. } = *k else { return None };
                // A `tagcase` proves a sum, and so a part, whether or not
                // the type is known here.
                let t = ty.and_then(|ty| {
                    let Ty::Sum(vs) = arena.get(arena.resolve(ty)) else { return None };
                    let mut t = vs.iter().find(|(l, _)| *l == tag)?.1;
                    if let Some(i) = field {
                        let Ty::Product(fs) = arena.get(arena.resolve(t)) else { return None };
                        t = fs.get(i)?.1;
                    }
                    Some(t)
                });
                Some(Tracked::Part { param, strict: true, ty: t })
            })
            .collect()
    }

    /// What is known of `e`'s value.
    fn tracked(&self, e: ExpId) -> Vec<Tracked> {
        let arena = &self.c.arena;
        match arena.exp_at(e).clone() {
            Exp::Var(s) => self.bound(s).cloned().unwrap_or_default(),
            Exp::The { exp, .. } => self.tracked(exp),
            // Either branch's value: what both say, the weaker of the two.
            Exp::If { then, els, .. } => {
                let (a, b) = (self.tracked(then), self.tracked(els));
                a.iter()
                    .filter_map(|x| {
                        b.iter().find_map(|y| match (*x, *y) {
                            (
                                Tracked::Part { param: p, strict: s, ty: t },
                                Tracked::Part { param: q, strict: r, ty: u },
                            ) if p == q => {
                                let same = matches!((t, u), (Some(t), Some(u)) if arena.resolve(t) == arena.resolve(u));
                                Some(Tracked::Part { param: p, strict: s && r, ty: if same { t } else { None } })
                            }
                            (Tracked::Int { param: p, offset: o }, Tracked::Int { param: q, offset: n }) if p == q && o == n => {
                                Some(*x)
                            }
                            _ => None,
                        })
                    })
                    .collect()
            }
            Exp::Extract(x, l) => self
                .tracked(x)
                .into_iter()
                .filter_map(|k| {
                    let Tracked::Part { param, ty, .. } = k else { return None };
                    // An `extract` proves a product, known here or not.
                    let t = ty.and_then(|ty| {
                        let Ty::Product(fs) = arena.get(arena.resolve(ty)) else { return None };
                        Some(fs.iter().find(|(f, _)| *f == l)?.1)
                    });
                    Some(Tracked::Part { param, strict: true, ty: t })
                })
                .collect(),
            // A generative type's conversion is the identity.
            Exp::App { fun, args } if args.len() == 1 && self.conversion(fun) => self
                .tracked(args[0])
                .into_iter()
                .map(|k| match k {
                    Tracked::Part { param, strict, .. } => Tracked::Part { param, strict, ty: None },
                    k => k,
                })
                .collect(),
            Exp::App { fun, args } => match (self.std_op(fun), &args[..]) {
                (Some(op @ ("car" | "cdr")), [x]) => self
                    .tracked(*x)
                    .into_iter()
                    .filter_map(|k| {
                        let Tracked::Part { param, ty: Some(ty), .. } = k else { return None };
                        let Ty::Pair(a, b, Region::Frozen(_, true)) = arena.get(arena.resolve(ty)) else { return None };
                        Some(Tracked::Part { param, strict: true, ty: Some(if op == "car" { *a } else { *b }) })
                    })
                    .collect(),
                (Some("datum-car" | "datum-cdr"), [x]) => self
                    .tracked(*x)
                    .into_iter()
                    .filter_map(|k| match k {
                        Tracked::Part { param, ty, .. } => Some(Tracked::Part { param, strict: true, ty }),
                        Tracked::Int { .. } => None,
                    })
                    .collect(),
                (Some(op @ ("+" | "-")), [a, b]) => {
                    let sign = if op == "+" { 1 } else { -1 };
                    let shift = |x: ExpId, k: i64| -> Vec<Tracked> {
                        self.tracked(x)
                            .into_iter()
                            .filter_map(|t| match t {
                                Tracked::Int { param, offset } => {
                                    offset.checked_add(k).map(|offset| Tracked::Int { param, offset })
                                }
                                Tracked::Part { .. } => None,
                            })
                            .collect()
                    };
                    match (literal(self.c, *a), literal(self.c, *b)) {
                        (_, Some(k)) => k.checked_mul(sign).map(|k| shift(*a, k)).unwrap_or_default(),
                        (Some(k), None) if op == "+" => shift(*b, k),
                        _ => Vec::new(),
                    }
                }
                _ => Vec::new(),
            },
            _ => Vec::new(),
        }
    }

    /// Whether `e` is the `car` or `cdr` of a parameter's part at a region
    /// that is not `finite`.
    fn written_part(&self, e: ExpId) -> bool {
        let arena = &self.c.arena;
        let Exp::App { fun, args } = arena.exp_at(e).clone() else { return false };
        matches!(self.std_op(fun), Some("car" | "cdr"))
            && args.len() == 1
            && self.tracked(args[0]).iter().any(|k| {
                matches!(k, Tracked::Part { ty: Some(ty), .. }
                    if matches!(arena.get(arena.resolve(*ty)), Ty::Pair(_, _, r) if !matches!(r, Region::Frozen(_, true))))
            })
    }

    /// Whether `e` is the same at every call of the group: a literal, a
    /// variable bound outside it, a parameter passed on unchanged, or the
    /// length of a string or the sum or difference of such.
    fn fixed(&self, e: ExpId) -> bool {
        match self.c.arena.exp_at(e).clone() {
            Exp::Int(_) => true,
            Exp::Var(s) => match self.bound(s) {
                None => self.member(s).is_none(),
                Some(known) => known.iter().any(|k| {
                    matches!(k, Tracked::Part { param, strict: false, .. } if self.invariant.contains(&(self.current, *param)))
                }),
            },
            Exp::The { exp, .. } => self.fixed(exp),
            Exp::App { fun, args } => {
                matches!((self.std_op(fun), args.len()), (Some("string-length"), 1) | (Some("+" | "-"), 2))
                    && args.iter().all(|a| self.fixed(*a))
            }
            _ => false,
        }
    }

    /// The bounds on parameters that `test` having the value `holds` shows.
    fn facts(&self, test: ExpId, holds: bool) -> Vec<(usize, Bound)> {
        let arena = &self.c.arena;
        match arena.exp_at(test).clone() {
            Exp::App { fun, args } if args.len() == 1 && self.is_op(fun, "not") => self.facts(args[0], !holds),
            Exp::App { fun, args } if args.len() == 2 => {
                let Some(op) = self.std_op(fun) else { return Vec::new() };
                // The bound `op`, holding or not, puts on its left operand.
                let left = match (op, holds) {
                    ("<" | "<=", true) | (">" | ">=", false) => vec![Bound::Upper],
                    ("<" | "<=", false) | (">" | ">=", true) => vec![Bound::Lower],
                    ("=", true) => vec![Bound::Lower, Bound::Upper],
                    _ => return Vec::new(),
                };
                let flip = |b: &Bound| if *b == Bound::Lower { Bound::Upper } else { Bound::Lower };
                let mut out = Vec::new();
                for (x, other, bounds) in
                    [(args[0], args[1], left.clone()), (args[1], args[0], left.iter().map(flip).collect())]
                {
                    if !self.fixed(other) {
                        continue;
                    }
                    for k in self.tracked(x) {
                        if let Tracked::Int { param, .. } = k {
                            out.extend(bounds.iter().map(|b| (param, *b)));
                        }
                    }
                }
                out
            }
            // `(and a b)` and `(or a b)`, as they are parsed.
            Exp::If { test: a, then: b, els } if holds && matches!(arena.exp_at(els), Exp::Bool(false)) => {
                let mut out = self.facts(a, true);
                out.extend(self.facts(b, true));
                out
            }
            Exp::If { test: a, then, els: b } if !holds && matches!(arena.exp_at(then), Exp::Bool(true)) => {
                let mut out = self.facts(a, false);
                out.extend(self.facts(b, false));
                out
            }
            _ => Vec::new(),
        }
    }

    /// A call of member `to` with `args`, from the member walked.
    fn call(&mut self, to: usize, args: &[ExpId]) {
        let unchanged = args
            .iter()
            .map(|a| {
                self.tracked(*a).iter().find_map(|k| match k {
                    Tracked::Part { param, strict: false, .. } => Some(*param),
                    _ => None,
                })
            })
            .collect();
        self.passed.push((self.current, to, unchanged));
        let mut g = Graph::new();
        let mut unbounded = None;
        let mut add = |from: (usize, Measure), to: (usize, Measure), strict: bool| {
            let e = g.entry((from, to)).or_insert(strict);
            *e |= strict;
        };
        for a in args {
            if self.written_part(*a) {
                unbounded.get_or_insert("a part of a list that may be written is no smaller: it may be cyclic");
            }
        }
        for (q, a) in args.iter().enumerate() {
            for k in self.tracked(*a) {
                match k {
                    Tracked::Part { param, strict, .. } => add((param, Measure::Part), (q, Measure::Part), strict),
                    Tracked::Int { param, offset } => {
                        let has = |b| self.guards.contains(&(param, b));
                        if offset < 0 && !has(Bound::Lower) {
                            unbounded.get_or_insert("it counts down, but nothing fixed bounds the count below");
                        }
                        if offset > 0 && !has(Bound::Upper) {
                            unbounded.get_or_insert("it counts up, but nothing fixed bounds the count above");
                        }
                        if offset < 0 && has(Bound::Lower) {
                            add((param, Measure::Down), (q, Measure::Down), true);
                        } else if offset <= 0 {
                            add((param, Measure::Down), (q, Measure::Down), false);
                        }
                        if offset > 0 && has(Bound::Upper) {
                            add((param, Measure::Up), (q, Measure::Up), true);
                        } else if offset >= 0 {
                            add((param, Measure::Up), (q, Measure::Up), false);
                        }
                    }
                }
            }
        }
        self.calls.push((self.current, to, g));
        self.unbounded.push(unbounded);
    }
}

/// `e` under projections and ascriptions.
fn strip(c: &Checker, mut e: ExpId) -> ExpId {
    while let Exp::Proj { body, .. } | Exp::The { exp: body, .. } = c.arena.exp_at(e) {
        e = *body;
    }
    e
}

fn literal(c: &Checker, e: ExpId) -> Option<i64> {
    match c.arena.exp_at(e) {
        Exp::Int(k) => Some(*k),
        _ => None,
    }
}

fn compose(a: &Graph, b: &Graph) -> Graph {
    let mut out = Graph::new();
    for ((x, y), s1) in a {
        for ((y2, z), s2) in b {
            if y == y2 {
                let e = out.entry((*x, *z)).or_insert(false);
                *e |= *s1 || *s2;
            }
        }
    }
    out
}

enum Ends {
    Yes,
    No,
    TooMany,
}

/// The size-change criterion over the group's calls.
fn size_change_ends(calls: &[(usize, usize, Graph)]) -> Ends {
    let mut all: HashSet<(usize, usize, Graph)> = calls.iter().cloned().collect();
    let mut todo: Vec<(usize, usize, Graph)> = all.iter().cloned().collect();
    while let Some((f, g, a)) = todo.pop() {
        for (g2, h, b) in calls {
            if *g2 != g {
                continue;
            }
            let c = (f, *h, compose(&a, b));
            if !all.contains(&c) {
                if all.len() >= MOST_GRAPHS {
                    return Ends::TooMany;
                }
                all.insert(c.clone());
                todo.push(c);
            }
        }
    }
    let ends = all
        .iter()
        .filter(|(f, g, a)| f == g && compose(a, a) == *a)
        .all(|(_, _, a)| a.iter().any(|((x, y), strict)| x == y && *strict));
    if ends { Ends::Yes } else { Ends::No }
}
