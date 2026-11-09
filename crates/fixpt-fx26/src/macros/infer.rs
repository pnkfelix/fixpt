//! Signatures inferred (`docs/research/typed-macros.md`, "Inferred
//! signatures"): a `syntax-rules` macro's, where its `define-syntax` writes
//! none, from its clauses alone.
//!
//! - Its shape is its patterns', merged where they differ: a `union` of
//!   their shapes there, or a list given by ellipsis that takes in the
//!   patterns that write its elements one by one (`(e)`, `(e r ...)`), if
//!   one of them is a list by ellipsis or `()`.
//! - Each pattern variable's syntax type is what its template places it as;
//!   `(many …)` if it places one with an expression in it more than once.
//! - The bindings it is in the scope of are those its template places it in
//!   (Herman's environments, `Aligner::walk`'s), each said where an address
//!   can say it: on the part itself, or on the part around it that the
//!   binder is outside of; a binder inside a list's element or a `union`'s
//!   member reached through what that exports.
//! - A template's use of the macro itself, or of another of its
//!   `define-syntax-rec`, is aligned with the signature so far, until the
//!   signature says the same twice.
//!
//! What is inferred is then checked as a written signature is: inference
//! decides which macros need none written, never what is safe.

use super::{ellipsis, exports, normal, reserved, split, Addr, Aligner, Atom, Bind, Delta, Kids, Level, Macro, Macros, Mode, Ns, PInfo, Ring, STy};
use crate::error::{FxError, R};
use fixpt_read::{Datum, Interner, Span, Sym, Syntax};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// A macro whose signature is inferred: its name, the literals its
/// `syntax-rules` lists, and its clauses, `((_ . pattern) template)`.
pub(super) struct Unsigned {
    pub name: Sym,
    pub lits: Vec<Sym>,
    pub clauses: Vec<Syntax>,
    pub span: Span,
}

/// What a macro makes, as its templates say.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Makes {
    Expr,
    Defn,
    Type,
}

impl Makes {
    fn said(self) -> &'static str {
        match self {
            Makes::Expr => "an expression",
            Makes::Defn => "definitions",
            Makes::Type => "a description",
        }
    }
}

/// A part of the shape of a macro's operands.
#[derive(Clone, Debug, PartialEq)]
enum Shape {
    Nil,
    Pair(usize, usize),
    /// A list by ellipsis, its element.
    Seq(usize),
    Lit(Sym),
    /// A pattern variable's (or `_`'s), of more than one, the clauses'.
    Leaf,
    Union(Vec<usize>),
}

/// A part: its shape, its address from its region's root, and that root (a
/// macro's operands, a list's element, a `union`'s member: what a
/// signature's addresses are from there).
struct Part {
    shape: Shape,
    path: Addr,
    root: usize,
}

/// A pattern's part, of a clause, under so many ellipses in its pattern.
#[derive(Clone)]
struct Item {
    cid: usize,
    syn: Syntax,
    depth: usize,
}

enum Class {
    Seq(Syntax),
    Wild,
    Lit(Sym),
    Var(Sym),
    Nil,
    Pair(Syntax, Syntax),
}

/// The shape of a group's macros' operands.
#[derive(Default)]
struct Parts {
    parts: Vec<Part>,
    roots: Vec<usize>,
    /// Each pattern variable's part, by its clause, and how many ellipses
    /// its pattern has it under.
    at: HashMap<(usize, Sym), usize>,
    depth: HashMap<(usize, Sym), usize>,
    /// The pattern variables, in the order found.
    order: Vec<(usize, Sym)>,
    /// Each region's root, a list's element or a `union`'s member, and the
    /// part whose region it is.
    boundary: HashMap<usize, usize>,
    /// The clauses each `union`'s member is of.
    members: HashMap<usize, Vec<usize>>,
    /// Each list by ellipsis that took in patterns written one by one, by
    /// the place of the first: one whose element turns out to be of more
    /// than one syntax type is not, next time.
    absorbed: HashMap<usize, Span>,
}

/// What a pattern variable's part is of: a syntax type, or a part of the
/// signature being inferred (a list by ellipsis, a `union`).
#[derive(Clone, Debug, PartialEq)]
enum K {
    Ty(Rc<STy>),
    Ref(usize),
}

/// One level of an environment, its atoms by part: a rib, each binder with
/// what it binds and how many lists by ellipsis gathered it (`Atom::Var`'s);
/// the ribcage a part exports.
#[derive(Clone, Debug, PartialEq)]
enum Lv {
    Rib(Vec<(usize, Delta, usize)>),
    Cage(usize),
}

/// One of a ribcage's, by part: what a part exports as a ribcage, or a rib.
#[derive(Clone, Debug, PartialEq)]
enum RingD {
    At(usize),
    Rib(Vec<(usize, Delta)>),
}

/// What a region's root must export: a rib, or a ribcage.
#[derive(Clone, Debug, PartialEq)]
enum Demand {
    Rib(Vec<(usize, Delta)>),
    Cage(Vec<RingD>),
}

/// A pattern variable placed by a template: where, as what, in what scope.
struct Placed {
    n: Sym,
    core: Rc<STy>,
    env: Vec<Level>,
    many: bool,
    depth: usize,
}

/// What an iteration infers, by part.
#[derive(Default)]
struct Sol {
    kinds: HashMap<usize, K>,
    pkinds: HashMap<(usize, Sym), K>,
    many: HashSet<usize>,
    imports: HashMap<usize, Bind>,
    exports: HashMap<usize, Bind>,
    root_exports: HashMap<usize, Bind>,
    sticky: HashSet<Span>,
}

impl Parts {
    fn region(&self, p: usize) -> usize {
        self.parts[p].root
    }

    /// The regions part `p` is in, innermost first.
    fn regions(&self, p: usize) -> Vec<usize> {
        let mut out = Vec::new();
        let mut r = self.region(p);
        loop {
            out.push(r);
            match self.boundary.get(&r) {
                Some(&b) => r = self.region(b),
                None => return out,
            }
        }
    }

    /// How part `x` is reached from region `r`: directly, or through the
    /// part `b` in `r` whose region it is in; `None` if `r` is not around it.
    fn via(&self, x: usize, r: usize) -> Option<Option<usize>> {
        let mut q = self.region(x);
        if q == r {
            return Some(None);
        }
        loop {
            let b = *self.boundary.get(&q)?;
            if self.region(b) == r {
                return Some(Some(b));
            }
            q = self.region(b);
        }
    }

    /// How many lists by ellipsis are between part `x` and region `r`
    /// around it.
    fn seqs_between(&self, x: usize, r: usize) -> usize {
        let (mut q, mut n) = (self.region(x), 0);
        while q != r {
            let Some(&b) = self.boundary.get(&q) else { return n };
            n += usize::from(matches!(self.parts[b].shape, Shape::Seq(_)));
            q = self.region(b);
        }
        n
    }

    fn is_union(&self, p: usize) -> bool {
        matches!(self.parts[p].shape, Shape::Union(_))
    }

    /// The region inside part `b` that clause `cid` is in: a list's
    /// element, or the member of a `union` its pattern is of.
    fn inner(&self, b: usize, cid: usize) -> Option<usize> {
        match &self.parts[b].shape {
            Shape::Seq(e) => Some(*e),
            Shape::Union(ms) => ms.iter().copied().find(|m| self.members.get(m).is_some_and(|cs| cs.contains(&cid))),
            _ => None,
        }
    }

    fn var(&mut self, key: (usize, Sym), p: usize, depth: usize) {
        if self.at.insert(key, p).is_none() {
            self.order.push(key);
        }
        self.depth.insert(key, depth);
    }

    fn part(&mut self, path: Addr, root: Option<usize>) -> usize {
        let id = self.parts.len();
        self.parts.push(Part { shape: Shape::Leaf, path: if root.is_some() { path } else { Vec::new() }, root: root.unwrap_or(id) });
        id
    }

    fn class(it: &Item, lits: &[Sym], interner: &Interner) -> R<Class> {
        if let Some(x) = ellipsis(&it.syn, interner) {
            return Ok(Class::Seq(x));
        }
        Ok(match &it.syn.datum {
            Datum::Symbol(n) => match interner.name(*n) {
                "_" => Class::Wild,
                "..." => return Err(FxError::at(it.syn.span, "`...` follows the part it repeats, last in a list")),
                name if lits.contains(n) || reserved(name) => Class::Lit(*n),
                _ => Class::Var(*n),
            },
            Datum::Nil => Class::Nil,
            Datum::List { .. } => {
                let (a, d) = split(&it.syn).expect("a list");
                Class::Pair(a, d)
            }
            // A datum matches itself: its part takes anything.
            _ => Class::Wild,
        })
    }

    /// The part for `items`, at `path` from region `root` (none: a region of
    /// its own).
    fn merge(&mut self, items: &[Item], path: Addr, root: Option<usize>, cx: &Cx) -> R<usize> {
        let id = self.part(path, root);
        let classes = items.iter().map(|i| Self::class(i, cx.lits(i.cid), cx.interner)).collect::<R<Vec<_>>>()?;
        if classes.iter().all(|c| matches!(c, Class::Var(_) | Class::Wild)) {
            for (i, c) in items.iter().zip(&classes) {
                if let Class::Var(n) = c {
                    self.var((i.cid, *n), id, i.depth);
                }
            }
            return Ok(id);
        }
        if let Some((elems, vars, took)) = self.absorbable(items, &classes, cx)? {
            for (cid, n, depth) in vars {
                self.var((cid, n), id, depth);
            }
            let e = self.merge(&elems, Vec::new(), None, cx)?;
            self.boundary.insert(e, id);
            self.parts[id].shape = Shape::Seq(e);
            if took {
                self.absorbed.insert(id, items[0].syn.span);
            }
            return Ok(id);
        }
        // Each shape the patterns have here, in the order first written.
        let tag = |c: &Class| match c {
            Class::Nil => 0,
            Class::Pair(..) => 1,
            Class::Seq(_) => 2,
            Class::Var(_) | Class::Wild => 3,
            Class::Lit(n) => 4 + n.0 as usize,
        };
        let mut groups: Vec<(usize, Vec<usize>)> = Vec::new();
        for (k, c) in classes.iter().enumerate() {
            match groups.iter_mut().find(|(t, _)| *t == tag(c)) {
                Some((_, g)) => g.push(k),
                None => groups.push((tag(c), vec![k])),
            }
        }
        if groups.len() == 1 {
            self.one(id, items, &classes, cx)?;
            return Ok(id);
        }
        let mut members = Vec::new();
        for (_, g) in groups {
            let its: Vec<Item> = g.iter().map(|k| items[*k].clone()).collect();
            let m = self.merge(&its, Vec::new(), None, cx)?;
            self.boundary.insert(m, id);
            let mut cs: Vec<usize> = its.iter().map(|i| i.cid).collect();
            cs.dedup();
            self.members.insert(m, cs);
            members.push(m);
        }
        self.parts[id].shape = Shape::Union(members);
        Ok(id)
    }

    /// Part `id`, of `items` all of one shape.
    fn one(&mut self, id: usize, items: &[Item], classes: &[Class], cx: &Cx) -> R<()> {
        let (root, base) = (self.parts[id].root, self.parts[id].path.clone());
        self.parts[id].shape = match &classes[0] {
            Class::Nil => Shape::Nil,
            Class::Lit(n) => Shape::Lit(*n),
            Class::Pair(..) => {
                let (mut cars, mut cdrs) = (Vec::new(), Vec::new());
                for (i, c) in items.iter().zip(classes) {
                    if let Class::Pair(a, d) = c {
                        cars.push(Item { cid: i.cid, syn: a.clone(), depth: i.depth });
                        cdrs.push(Item { cid: i.cid, syn: d.clone(), depth: i.depth });
                    }
                }
                let (mut ap, mut dp) = (base.clone(), base);
                ap.push(true);
                dp.push(false);
                let a = self.merge(&cars, ap, Some(root), cx)?;
                let d = self.merge(&cdrs, dp, Some(root), cx)?;
                Shape::Pair(a, d)
            }
            _ => unreachable!("a list by ellipsis takes in the rest"),
        };
        Ok(())
    }

    /// If `items` may be one list by ellipsis: its elements' patterns, the
    /// pattern variables of the whole list, and whether it took in patterns
    /// written one by one. So if one is a list by ellipsis or `()`, and the
    /// rest are, or lists ending in one, whose elements are of one syntax
    /// type as far as is known.
    #[allow(clippy::type_complexity)]
    fn absorbable(&self, items: &[Item], classes: &[Class], cx: &Cx) -> R<Option<(Vec<Item>, Vec<(usize, Sym, usize)>, bool)>> {
        if !classes.iter().any(|c| matches!(c, Class::Nil | Class::Seq(_))) || classes.iter().all(|c| matches!(c, Class::Nil)) {
            return Ok(None);
        }
        let (mut elems, mut vars, mut took, mut seq) = (Vec::new(), Vec::new(), false, false);
        for i in items {
            if !self.take(i, cx, &mut elems, &mut vars, &mut took, &mut seq)? {
                return Ok(None);
            }
        }
        // Patterns written one by one are a list by ellipsis where another
        // writes one: `(e)`, `(e r ...)`; not `()` and `(x . rest)`, whose
        // elements may each be in the scope of those before.
        if !seq {
            return Ok(None);
        }
        if took {
            if cx.sticky.contains(&items[0].syn.span) {
                return Ok(None);
            }
            let known: Vec<&K> = elems.iter().filter_map(|e| match &e.syn.datum {
                Datum::Symbol(n) => cx.pkinds.get(&(e.cid, *n)).filter(|k| matches!(k, K::Ty(_))),
                _ => None,
            }).collect();
            if known.iter().any(|a| known.iter().any(|b| !reconcile(a, b) && !reconcile(b, a))) {
                return Ok(None);
            }
        }
        Ok(Some((elems, vars, took)))
    }

    fn take(&self, it: &Item, cx: &Cx, elems: &mut Vec<Item>, vars: &mut Vec<(usize, Sym, usize)>, took: &mut bool, seq: &mut bool) -> R<bool> {
        Ok(match Self::class(it, cx.lits(it.cid), cx.interner)? {
            Class::Nil | Class::Wild => true,
            Class::Seq(x) => {
                *seq = true;
                elems.push(Item { cid: it.cid, syn: x, depth: it.depth + 1 });
                true
            }
            Class::Var(n) => {
                vars.push((it.cid, n, it.depth));
                true
            }
            Class::Pair(a, d) => {
                *took = true;
                elems.push(Item { cid: it.cid, syn: a, depth: it.depth });
                self.take(&Item { cid: it.cid, syn: d, depth: it.depth }, cx, elems, vars, took, seq)?
            }
            Class::Lit(_) => false,
        })
    }

    /// The shape, as compared from one iteration to the next.
    fn fingerprint(&self) -> String {
        let mut s = format!("{:?}", self.roots);
        for p in &self.parts {
            s.push_str(&format!("{:?}{:?}{};", p.shape, p.path, p.root));
        }
        s
    }
}

/// What the shape is built from: each clause's macro's literals, the
/// pattern variables' syntax types last found, and the lists by ellipsis
/// that are not to take in patterns written one by one.
struct Cx<'a> {
    lits: Vec<&'a [Sym]>,
    of: Vec<usize>,
    pkinds: &'a HashMap<(usize, Sym), K>,
    sticky: &'a HashSet<Span>,
    interner: &'a Interner,
}

impl Cx<'_> {
    fn lits(&self, cid: usize) -> &[Sym] {
        self.lits[self.of[cid]]
    }
}

/// How specific a syntax type is, where a pattern variable is placed as
/// more than one: a binder before the references to it, a tag before the
/// application its use at a list's head looked like, a variable before an
/// expression, an expression before a lambda.
fn rank(k: &K) -> u8 {
    match k {
        K::Ty(t) => match &**t {
            STy::Bvar => 0,
            STy::Dvar => 1,
            STy::Label => 2,
            STy::Id => 3,
            STy::Expr => 6,
            STy::Lambda => 7,
            STy::Data => 8,
            _ => 4,
        },
        K::Ref(_) => 4,
    }
}

/// Whether a part of syntax type `a` may be placed where `b` is too (the
/// rest the checker says).
fn reconcile(a: &K, b: &K) -> bool {
    if a == b {
        return true;
    }
    let (K::Ty(a), K::Ty(b)) = (a, b) else { return false };
    use STy::*;
    matches!((&**a, &**b), (Bvar, Expr | Id | Lambda) | (Dvar, Type | Expr | Id) | (Label, Expr) | (Id, Expr) | (Expr, Lambda))
}

/// One syntax type for a part placed as each of `ks`, and whether some of
/// them do not agree with it.
fn combine(ks: &[K]) -> (Option<K>, bool) {
    let Some(chosen) = ks.iter().min_by_key(|k| rank(k)) else { return (None, false) };
    let conflict = ks.iter().any(|k| !reconcile(chosen, k));
    (Some(chosen.clone()), conflict)
}

/// Whether a part of syntax type `k` is placed in a scope its signature
/// says: as `Aligner::placed` compares them (binders, names and
/// descriptions are not).
fn scoped(k: &K) -> bool {
    match k {
        K::Ty(t) => !matches!(&**t, STy::Bvar | STy::Dvar | STy::Data | STy::Type | STy::Label | STy::Kind | STy::Defn),
        K::Ref(_) => true,
    }
}

/// Whether a part of syntax type `k` with an expression in it would run
/// each time it is placed.
fn affine(k: &K) -> bool {
    match k {
        K::Ty(t) => !matches!(&**t, STy::Bvar | STy::Dvar | STy::Id | STy::Label | STy::Data | STy::Type | STy::Kind),
        K::Ref(_) => true,
    }
}

/// Whether `t` has an annotation whose addresses are from outside it: one
/// not under a `mu` or a `union` of its own.
fn open(t: &STy) -> bool {
    match t {
        STy::Import(..) | STy::Export(..) => true,
        STy::Pair(a, d) => open(a) || open(d),
        STy::Many(b) | STy::Typed(b, _) => open(b),
        _ => false,
    }
}

impl Macros {
    /// The signatures of macros `us`, defined together, inferred: each as
    /// written, `(-> σ defn)` and `(-> σ type)` for what makes definitions
    /// or a description.
    pub(super) fn infer(&mut self, us: &[Unsigned], interner: &mut Interner) -> R<Vec<Syntax>> {
        let usage = "a clause is `((_ . pattern) template)`";
        let mut clauses = Vec::new();
        for (mi, u) in us.iter().enumerate() {
            for c in &u.clauses {
                let Some([p, t]) = c.as_proper_list() else {
                    return Err(FxError::at(c.span, usage));
                };
                let Some((_, p)) = split(p) else {
                    return Err(FxError::at(p.span, usage));
                };
                clauses.push((mi, p, t.clone()));
            }
        }
        let makes = self.makes_all(us, &clauses, interner)?;
        let saved: Vec<Option<Rc<Macro>>> = us.iter().map(|u| self.defined.get(&u.name).cloned()).collect();
        let r = self.infer_loop(us, &clauses, &makes, interner);
        for (u, s) in us.iter().zip(saved) {
            match s {
                Some(m) => self.defined.insert(u.name, m),
                None => self.defined.remove(&u.name),
            };
        }
        let sigs = r?;
        Ok(sigs
            .into_iter()
            .zip(&makes)
            .zip(us)
            .map(|((s, m), u)| match m {
                Makes::Expr => s,
                _ => {
                    let made = if *m == Makes::Defn { "defn" } else { "type" };
                    Syntax::list(u.span, vec![Syntax::symbol(u.span, interner.intern("->")), s, Syntax::symbol(u.span, interner.intern(made))])
                }
            })
            .collect())
    }

    fn infer_loop(&mut self, us: &[Unsigned], clauses: &[(usize, Syntax, Syntax)], makes: &[Makes], interner: &mut Interner) -> R<Vec<Syntax>> {
        let mut sol = Sol::default();
        let mut sticky: HashSet<Span> = HashSet::new();
        let mut last: Option<(Vec<String>, Vec<Syntax>)> = None;
        let mut shape_was = String::new();
        let lits: Vec<&[Sym]> = us.iter().map(|u| &u.lits[..]).collect();
        let of: Vec<usize> = clauses.iter().map(|c| c.0).collect();
        for _ in 0..16 {
            let parts = {
                let cx = Cx { lits: lits.clone(), of: of.clone(), pkinds: &sol.pkinds, sticky: &sticky, interner };
                let mut ps = Parts::default();
                for mi in 0..us.len() {
                    let items: Vec<Item> = clauses.iter().enumerate().filter(|(_, c)| c.0 == mi).map(|(cid, c)| Item { cid, syn: c.1.clone(), depth: 0 }).collect();
                    let r = ps.merge(&items, Vec::new(), None, &cx)?;
                    ps.roots.push(r);
                }
                ps
            };
            // A shape not the last one's: what was found of the last is of
            // other parts.
            let shape = parts.fingerprint();
            if shape != shape_was {
                let pkinds = std::mem::take(&mut sol.pkinds).into_iter().filter(|(_, k)| matches!(k, K::Ty(_))).collect();
                sol = Sol { pkinds, ..Sol::default() };
                shape_was = shape;
            }
            let (tys, mu_parts) = self.build(&parts, &sol);
            let shown: Vec<Syntax> = tys.iter().zip(us).map(|(t, u)| self.shown_sty(t, u.span, interner, &mut Vec::new())).collect();
            let strings: Vec<String> = shown.iter().map(|s| fixpt_read::write_syntax(s, interner)).collect();
            if last.as_ref().is_some_and(|(l, _)| *l == strings) {
                return Ok(shown);
            }
            for ((u, t), m) in us.iter().zip(&tys).zip(makes) {
                self.defined.insert(u.name, Rc::new(Macro { sig: t.clone(), defn: *m == Makes::Defn, desc: *m == Makes::Type, poly: Vec::new(), clauses: Vec::new(), text: None, procedural: None }));
            }
            let mut placed = Vec::new();
            let mut made = Vec::new();
            for (cid, (mi, _, t)) in clauses.iter().enumerate() {
                match self.placements(&parts, &sol, cid, t, makes[*mi], interner) {
                    Ok((p, m)) => {
                        placed.push(Some(p));
                        made.push(m);
                    }
                    // The checker says what, of what is inferred.
                    Err(_) => {
                        placed.push(None);
                        made.push(None);
                    }
                }
            }
            sol = self.solve(&parts, &placed, &made, &sol, &mu_parts, makes, &of);
            sticky.extend(sol.sticky.iter().copied());
            last = Some((strings, shown));
        }
        Ok(last.map(|(_, s)| s).unwrap_or_default())
    }

    /// What each macro makes, by its templates: a definition's form or a
    /// use of a macro that makes definitions, definitions; a description's
    /// form or such a macro's use, a description; an expression's form, a
    /// literal, an expression; else (a name, an application) whatever
    /// another clause says, an expression if none does.
    fn makes_all(&self, us: &[Unsigned], clauses: &[(usize, Syntax, Syntax)], interner: &Interner) -> R<Vec<Makes>> {
        let mut known: Vec<Option<Makes>> = vec![None; us.len()];
        for _ in 0..=us.len() {
            let mut next: Vec<Option<Makes>> = vec![None; us.len()];
            for (mi, p, t) in clauses {
                let pv: HashSet<Sym> = super::pattern_names(p, interner).into_iter().filter(|n| !us[*mi].lits.contains(n)).collect();
                if let Some(k) = self.makes(t, &pv, us, &known, interner) {
                    match next[*mi] {
                        Some(j) if j != k => {
                            return Err(FxError::at(t.span, format!("this template makes {}, and another of `{}`'s {}", k.said(), interner.name(us[*mi].name), j.said())));
                        }
                        _ => next[*mi] = Some(k),
                    }
                }
            }
            if next == known {
                break;
            }
            known = next;
        }
        Ok(known.into_iter().map(|k| k.unwrap_or(Makes::Expr)).collect())
    }

    fn makes(&self, t: &Syntax, pv: &HashSet<Sym>, us: &[Unsigned], known: &[Option<Makes>], interner: &Interner) -> Option<Makes> {
        match &t.datum {
            Datum::Symbol(_) | Datum::Nil => None,
            Datum::List { items, .. } => match &items[0].datum {
                Datum::Symbol(h) if pv.contains(h) => None,
                Datum::Symbol(h) => {
                    if let Some(i) = us.iter().position(|u| u.name == *h) {
                        return known[i];
                    }
                    if let Some(m) = self.defined.get(h) {
                        return Some(if m.defn { Makes::Defn } else if m.desc { Makes::Type } else { Makes::Expr });
                    }
                    match interner.name(*h) {
                        "define" | "define*" | "define-rec" | "define-type" | "define-effect" => Some(Makes::Defn),
                        "begin" => {
                            let each: Vec<Makes> = items[1..].iter().filter_map(|i| self.makes(i, pv, us, known, interner)).collect();
                            if each.contains(&Makes::Defn) { Some(Makes::Defn) } else { each.first().copied() }
                        }
                        n if self.kernel.contains_key(n) => Some(Makes::Expr),
                        // A type form's head; not `+` and the like, which
                        // descriptions share with expressions.
                        n if self.type_forms.contains(n) => Some(Makes::Type),
                        _ => None,
                    }
                }
                Datum::Keyword(_) => Some(Makes::Expr),
                _ => None,
            },
            _ => Some(Makes::Expr),
        }
    }

    /// The signature so far, of each macro, from `sol`: its syntax types,
    /// and each `mu` made for a list by ellipsis, a `union`, or a part of a
    /// syntax type not known yet, by its part.
    fn build(&mut self, parts: &Parts, sol: &Sol) -> (Vec<Rc<STy>>, HashMap<usize, usize>) {
        let mut mu_of = HashMap::new();
        for (p, part) in parts.parts.iter().enumerate() {
            if matches!(part.shape, Shape::Seq(_) | Shape::Union(_)) || (part.shape == Shape::Leaf && !sol.kinds.contains_key(&p)) {
                mu_of.insert(p, self.mus.len());
                self.mus.push(Rc::new(STy::Nil));
            }
        }
        let mut tys = Vec::new();
        for (mi, &r) in parts.roots.iter().enumerate() {
            let t = self.part_ty(parts, sol, r, &mu_of);
            tys.push(match sol.root_exports.get(&mi) {
                Some(b) => Rc::new(STy::Export(t, b.clone())),
                None => t,
            });
        }
        let mu_parts = mu_of.into_iter().map(|(p, id)| (id, p)).collect();
        (tys, mu_parts)
    }

    fn part_ty(&mut self, parts: &Parts, sol: &Sol, p: usize, mu_of: &HashMap<usize, usize>) -> Rc<STy> {
        let base = match parts.parts[p].shape.clone() {
            Shape::Nil => Rc::new(STy::Nil),
            Shape::Lit(n) => Rc::new(STy::Literal(n)),
            Shape::Pair(a, d) => Rc::new(STy::Pair(self.part_ty(parts, sol, a, mu_of), self.part_ty(parts, sol, d, mu_of))),
            Shape::Leaf => match sol.kinds.get(&p) {
                    Some(K::Ty(t)) => match &**t {
                        STy::Pair(..) | STy::Mu(_) | STy::Union(_) | STy::Import(..) | STy::Export(..) | STy::Many(_) | STy::Typed(..) if open(t) => {
                            let id = self.mus.len();
                            self.mus.push(t.clone());
                            Rc::new(STy::Mu(id))
                        }
                        STy::Pair(..) | STy::Mu(_) | STy::Union(_) | STy::Import(..) | STy::Export(..) | STy::Many(_) | STy::Typed(..) => t.clone(),
                        simple => Rc::new(simple.clone()),
                    },
                Some(K::Ref(q)) => Rc::new(STy::Mu(mu_of[q])),
                // Not known: anything, by a `mu` of its own, which says
                // where it is placed is this part.
                None => {
                    let id = mu_of[&p];
                    self.mus[id] = Rc::new(STy::Data);
                    Rc::new(STy::Mu(id))
                }
            },
            Shape::Seq(e) => {
                let id = mu_of[&p];
                let elem = self.part_ty(parts, sol, e, mu_of);
                // As `Macros::seq` makes `(elem ...)`.
                let elem = match (sol.exports.get(&e), &*elem) {
                    (Some(b), _) => Rc::new(STy::Export(elem, b.clone())),
                    (None, STy::Bvar) => Rc::new(STy::Export(elem, Bind::Rib(vec![(Vec::new(), Delta::Var)]))),
                    (None, STy::Dvar) => Rc::new(STy::Export(elem, Bind::Rib(vec![(Vec::new(), Delta::Dvar)]))),
                    _ => elem,
                };
                let pair = Rc::new(STy::Pair(elem.clone(), Rc::new(STy::Mu(id))));
                let body = if matches!(&*elem, STy::Export(..)) {
                    let none = Rc::new(STy::Export(Rc::new(STy::Nil), Bind::Rib(Vec::new())));
                    vec![none, Rc::new(STy::Export(pair, Bind::Rib(vec![(vec![true], Delta::Rib), (vec![false], Delta::Rib)])))]
                } else {
                    vec![Rc::new(STy::Nil), pair]
                };
                self.mus[id] = Rc::new(STy::Union(body));
                Rc::new(STy::Mu(id))
            }
            Shape::Union(ms) => {
                let id = mu_of[&p];
                let members = ms
                    .iter()
                    .map(|m| {
                        let t = self.part_ty(parts, sol, *m, mu_of);
                        match sol.exports.get(m) {
                            Some(b) => Rc::new(STy::Export(t, b.clone())),
                            None => t,
                        }
                    })
                    .collect();
                self.mus[id] = Rc::new(STy::Union(members));
                Rc::new(STy::Mu(id))
            }
        };
        let t = if sol.many.contains(&p) { Rc::new(STy::Many(base)) } else { base };
        match sol.imports.get(&p) {
            Some(b) => Rc::new(STy::Import(t, b.clone())),
            None => t,
        }
    }

    /// Where clause `cid`'s template places its pattern variables, with the
    /// signature so far; and, if it makes definitions, what of what a use
    /// gives it defines.
    #[allow(clippy::type_complexity)]
    fn placements(&self, parts: &Parts, sol: &Sol, cid: usize, template: &Syntax, made: Makes, interner: &Interner) -> R<(Vec<Placed>, Option<(Vec<Atom>, Vec<Sym>)>)> {
        // A pattern variable whose syntax type is not known yet taken for a
        // name, where a form takes a name or a list (`define-type`'s); if
        // the template is then refused, for anything.
        self.placed_as(parts, sol, cid, template, made, interner, true).or_else(|_| self.placed_as(parts, sol, cid, template, made, interner, false))
    }

    #[allow(clippy::too_many_arguments, clippy::type_complexity)]
    fn placed_as(&self, parts: &Parts, sol: &Sol, cid: usize, template: &Syntax, made: Makes, interner: &Interner, names: bool) -> R<(Vec<Placed>, Option<(Vec<Atom>, Vec<Sym>)>)> {
        let mut pvars = HashMap::new();
        for (&(c, n), &p) in &parts.at {
            if c != cid {
                continue;
            }
            let core = match (&parts.parts[p].shape, sol.kinds.get(&p)) {
                (Shape::Leaf, Some(K::Ty(t))) => t.clone(),
                (Shape::Leaf, None) if names => Rc::new(STy::Id),
                _ => Rc::new(STy::Data),
            };
            pvars.insert(n, PInfo { core, declared: Vec::new(), many: false, hole: None, depth: parts.depth[&(c, n)] });
        }
        let mut t = Aligner { m: self, interner, mode: Mode::Template, pvars: &pvars, nodes: Vec::new() };
        let ty = Rc::new(match made {
            Makes::Defn => STy::Defn,
            Makes::Type => STy::Type,
            Makes::Expr => STy::Expr,
        });
        let root = t.align(&ty, template, None, Vec::new())?;
        let (mut found, mut seqs) = (Vec::new(), Vec::new());
        t.walk(root, &Vec::new(), false, 0, &mut found, &mut seqs)?;
        let mut out = Vec::new();
        for (at, env, many, depth) in found {
            if let Kids::PVar(n) = t.nodes[at].kids {
                out.push(Placed { n, core: t.nodes[at].core.clone(), env: normal(&env), many, depth });
            }
        }
        let defined = if made == Makes::Defn { Some(exports(&t.levels_of(root, template.span)?)) } else { None };
        Ok((out, defined))
    }

    /// What the templates' placements say of each part: its syntax type,
    /// whether `many`, and the scopes, as imports and exports.
    #[allow(clippy::too_many_arguments)]
    fn solve(&self, parts: &Parts, placed: &[Option<Vec<Placed>>], made: &[Option<(Vec<Atom>, Vec<Sym>)>], prev: &Sol, mu_parts: &HashMap<usize, usize>, makes: &[Makes], of: &[usize]) -> Sol {
        let mut sol = Sol::default();
        // A part of the signature so far: a list by ellipsis or a `union`,
        // itself; one whose syntax type is not known yet, none.
        let classify = |core: &Rc<STy>| -> Option<K> {
            if let STy::Mu(id) = &**core
                && let Some(&q) = mu_parts.get(id)
            {
                return (parts.parts[q].shape != Shape::Leaf).then_some(K::Ref(q));
            }
            Some(K::Ty(core.clone()))
        };
        // Each pattern variable's syntax type, then each part's.
        for (cid, ps) in placed.iter().enumerate() {
            let Some(ps) = ps else { continue };
            let mut by: Vec<(Sym, Vec<K>)> = Vec::new();
            for p in ps {
                let k = classify(&p.core);
                match by.iter_mut().find(|(n, _)| *n == p.n) {
                    Some((_, ks)) => ks.extend(k),
                    None => by.push((p.n, k.into_iter().collect())),
                }
            }
            for (n, ks) in by {
                if let (Some(k), _) = combine(&ks) {
                    sol.pkinds.insert((cid, n), k);
                }
            }
        }
        // Kept from before where a clause's template is not aligned, yet.
        for (key, k) in &prev.pkinds {
            if placed[key.0].is_none() && !sol.pkinds.contains_key(key) && matches!(k, K::Ty(_)) {
                sol.pkinds.insert(*key, k.clone());
            }
        }
        let mut of_part: HashMap<usize, Vec<(usize, Sym)>> = HashMap::new();
        for key in &parts.order {
            of_part.entry(parts.at[key]).or_default().push(*key);
        }
        for (p, vars) in &of_part {
            if parts.parts[*p].shape != Shape::Leaf {
                continue;
            }
            let ks: Vec<K> = vars.iter().filter_map(|v| sol.pkinds.get(v).cloned()).collect();
            let (k, conflict) = combine(&ks);
            if let Some(k) = k {
                sol.kinds.insert(*p, k);
            }
            if conflict
                && let Some(s) = parts.boundary.get(p)
                && let Some(span) = parts.absorbed.get(s)
            {
                sol.sticky.insert(*span);
            }
        }
        let kind_of = |p: usize| -> Option<K> {
            match parts.parts[p].shape {
                Shape::Leaf => sol.kinds.get(&p).cloned(),
                _ => Some(K::Ref(p)),
            }
        };
        // `many`: placed more than once, in a part another macro's signature
        // says is, or under more ellipses than the pattern has it.
        for (cid, ps) in placed.iter().enumerate() {
            let Some(ps) = ps else { continue };
            let mut counts: HashMap<Sym, usize> = HashMap::new();
            for pl in ps {
                *counts.entry(pl.n).or_default() += 1;
            }
            for pl in ps {
                let Some(&p) = parts.at.get(&(cid, pl.n)) else { continue };
                if !kind_of(p).is_some_and(|k| affine(&k)) {
                    continue;
                }
                if counts[&pl.n] > 1 || pl.many || pl.depth > parts.depth[&(cid, pl.n)] {
                    sol.many.insert(p);
                }
            }
        }
        // The scopes: what each part placed in a scope is in, as imports on
        // it or the parts around it, and what the parts between export.
        let mut sites: HashMap<usize, Vec<(usize, Vec<RingD>)>> = HashMap::new();
        let mut demands: Vec<(usize, Demand)> = Vec::new();
        for (cid, ps) in placed.iter().enumerate() {
            let Some(ps) = ps else { continue };
            let mut seen = HashSet::new();
            for pl in ps {
                let Some(&p) = parts.at.get(&(cid, pl.n)) else { continue };
                if !seen.insert(pl.n) || !kind_of(p).is_some_and(|k| scoped(&k)) {
                    continue;
                }
                let Some(lvs) = Self::lvs(parts, cid, &pl.env) else { continue };
                let Some(at) = Self::sites(parts, p, &lvs) else { continue };
                if at.first().is_none_or(|(s, _, _)| *s != p) {
                    sites.entry(p).or_default().push((cid, Vec::new()));
                }
                for (site, region, run) in at {
                    if let Some(rings) = Self::rings(parts, &run, region, cid, &mut demands) {
                        sites.entry(site).or_default().push((cid, rings));
                    }
                }
            }
        }
        let mut sites: Vec<(usize, Vec<(usize, Vec<RingD>)>)> = sites.into_iter().collect();
        sites.sort_by_key(|(s, _)| *s);
        for (site, list) in sites {
            let rings = Self::merge_rings(parts, &list, &mut demands);
            if !rings.is_empty() {
                sol.imports.insert(site, Self::bind_of(parts, &rings));
            }
        }
        // What a macro that makes definitions defines of what a use gives.
        for (mi, &root) in parts.roots.iter().enumerate() {
            if makes[mi] != Makes::Defn {
                continue;
            }
            let mut list = Vec::new();
            for (cid, m) in made.iter().enumerate() {
                let Some((atoms, cages)) = m.as_ref().filter(|_| of[cid] == mi) else { continue };
                let mut lvs = Vec::new();
                if !atoms.is_empty() {
                    if let Some(Lv::Rib(es)) = Self::lvs(parts, cid, &[Level::Rib(atoms.clone())]).and_then(|l| l.into_iter().next()) {
                        lvs.push(Lv::Rib(es));
                    }
                }
                let mut cs: Vec<usize> = cages.iter().filter_map(|y| parts.at.get(&(cid, *y)).copied()).collect();
                cs.sort();
                lvs.extend(cs.into_iter().map(Lv::Cage));
                if let Some(rings) = Self::rings(parts, &lvs, root, cid, &mut demands) {
                    list.push((cid, rings));
                }
            }
            let rings = Self::merge_rings(parts, &list, &mut demands);
            if !rings.is_empty() {
                sol.root_exports.insert(mi, Self::bind_of(parts, &rings));
            }
        }
        // Each region's export, the first said (an empty one only where none
        // is); each other member of a `union` one that exports, an empty one.
        let mut got: HashMap<usize, Demand> = HashMap::new();
        for (inner, d) in demands {
            let empty = matches!(&d, Demand::Rib(es) if es.is_empty()) || matches!(&d, Demand::Cage(rs) if rs.is_empty());
            match got.get(&inner) {
                None => _ = got.insert(inner, d),
                Some(Demand::Rib(es)) if es.is_empty() && !empty => _ = got.insert(inner, d),
                Some(Demand::Cage(rs)) if rs.is_empty() && !empty => _ = got.insert(inner, d),
                _ => {}
            }
        }
        for part in &parts.parts {
            let Shape::Union(ms) = &part.shape else { continue };
            let Some(d) = ms.iter().find_map(|m| got.get(m).cloned()) else { continue };
            for m in ms {
                got.entry(*m).or_insert_with(|| match d {
                    Demand::Rib(_) => Demand::Rib(Vec::new()),
                    Demand::Cage(_) => Demand::Cage(Vec::new()),
                });
            }
        }
        for (inner, d) in got {
            let b = match d {
                Demand::Rib(es) => Bind::Rib(es.iter().map(|(x, d)| (parts.parts[*x].path.clone(), *d)).collect()),
                Demand::Cage(rs) => Bind::Cage(rs.iter().map(|r| Self::ring(parts, r)).collect()),
            };
            sol.exports.insert(inner, b);
        }
        sol
    }

    /// Environment `env` of clause `cid`, its atoms by part; none if it has
    /// a level an inferred signature does not say: what the repetitions
    /// before a repeated element bound.
    fn lvs(parts: &Parts, cid: usize, env: &[Level]) -> Option<Vec<Lv>> {
        let mut out = Vec::new();
        for l in env {
            match l {
                Level::Rib(atoms) => {
                    let mut es: Vec<(usize, Delta, usize)> = Vec::new();
                    for a in atoms {
                        let (n, d, g) = match a {
                            Atom::Var(n, Ns::Value, g) => (*n, Delta::Var, *g),
                            Atom::Var(n, Ns::Desc, g) => (*n, Delta::Dvar, *g),
                            Atom::RibOf(n) => (*n, Delta::Rib, 0),
                            Atom::Lit(..) => continue,
                        };
                        let p = *parts.at.get(&(cid, n))?;
                        match es.iter_mut().find(|(q, _, h)| *q == p && *h == g) {
                            Some((_, e @ (Delta::Var | Delta::Dvar), _)) if *e != d => *e = Delta::Place,
                            Some(_) => {}
                            None => es.push((p, d, g)),
                        }
                    }
                    es.sort_by_key(|(p, _, g)| (*p, *g));
                    out.push(Lv::Rib(es));
                }
                Level::Cage(n) => out.push(Lv::Cage(*parts.at.get(&(cid, *n))?)),
                Level::Earlier(_) => return None,
            }
        }
        Some(out)
    }

    fn atoms_of(lv: &Lv) -> Vec<usize> {
        match lv {
            Lv::Rib(es) => es.iter().map(|(p, _, _)| *p).collect(),
            Lv::Cage(p) => vec![*p],
        }
    }

    /// Where each of levels `lvs` (innermost first) of part `p` is said:
    /// on `p`, in its region, while each level's binders are in or under
    /// it; then on the part whose region that is, in the region around it,
    /// and so on out. Each site with its region and levels.
    fn sites(parts: &Parts, p: usize, lvs: &[Lv]) -> Option<Vec<(usize, usize, Vec<Lv>)>> {
        let regions = parts.regions(p);
        let mut out: Vec<(usize, usize, Vec<Lv>)> = Vec::new();
        let mut i = 0;
        for lv in lvs {
            // Each binder reached from `r`, through as many lists by
            // ellipsis as gathered it: its own repetition's from inside its
            // element, every repetition's from outside the list.
            let ok = |r: usize| match lv {
                Lv::Rib(es) => es.iter().all(|(x, _, g)| parts.via(*x, r).is_some() && parts.seqs_between(*x, r) == *g),
                Lv::Cage(y) => parts.via(*y, r).is_some(),
            };
            while i < regions.len() && !ok(regions[i]) {
                i += 1;
            }
            if i == regions.len() {
                return None;
            }
            let site = if i == 0 { p } else { parts.boundary[&regions[i - 1]] };
            match out.last_mut() {
                Some((s, _, v)) if *s == site => v.push(lv.clone()),
                _ => out.push((site, regions[i], vec![lv.clone()])),
            }
        }
        Some(out)
    }

    /// Levels `lvs`, said from region `r` for clause `cid`: a run of them
    /// all of binders in one `union`'s member, the ribcage it exports; a
    /// rib, its binders in `r` by address and those inside a part in `r`
    /// by the rib that part exports. What each region exports is pushed on
    /// `demands`.
    fn rings(parts: &Parts, lvs: &[Lv], r: usize, cid: usize, demands: &mut Vec<(usize, Demand)>) -> Option<Vec<RingD>> {
        let through = |lv: &Lv| -> Option<usize> {
            let xs = Self::atoms_of(lv);
            let first = parts.via(*xs.first()?, r)??;
            (parts.is_union(first) && xs.iter().all(|x| parts.via(*x, r) == Some(Some(first)))).then_some(first)
        };
        let mut out = Vec::new();
        let mut i = 0;
        while i < lvs.len() {
            if let Some(u) = through(&lvs[i]) {
                let mut j = i + 1;
                while j < lvs.len() && through(&lvs[j]) == Some(u) {
                    j += 1;
                }
                let m = parts.inner(u, cid)?;
                let inner = Self::rings(parts, &lvs[i..j], m, cid, demands)?;
                demands.push((m, Demand::Cage(inner)));
                out.push(RingD::At(u));
                i = j;
                continue;
            }
            match &lvs[i] {
                Lv::Cage(y) => match parts.via(*y, r)? {
                    None => out.push(RingD::At(*y)),
                    Some(_) => return None,
                },
                Lv::Rib(es) => out.push(RingD::Rib(Self::rib_entries(parts, es, r, cid, demands)?)),
            }
            i += 1;
        }
        Some(out)
    }

    fn rib_entries(parts: &Parts, es: &[(usize, Delta, usize)], r: usize, cid: usize, demands: &mut Vec<(usize, Demand)>) -> Option<Vec<(usize, Delta)>> {
        let mut out: Vec<(usize, Delta)> = Vec::new();
        let mut through: Vec<(usize, Vec<(usize, Delta, usize)>)> = Vec::new();
        for (x, d, g) in es {
            match parts.via(*x, r)? {
                None if *g == 0 => out.push((*x, *d)),
                None => return None,
                Some(b) => {
                    // A list gathers its elements' repetitions.
                    let seq = matches!(parts.parts[b].shape, Shape::Seq(_));
                    if seq && *g == 0 {
                        return None;
                    }
                    let g = if seq { g - 1 } else { *g };
                    match through.iter_mut().find(|(c, _)| *c == b) {
                        Some((_, v)) => v.push((*x, *d, g)),
                        None => through.push((b, vec![(*x, *d, g)])),
                    }
                }
            }
        }
        for (b, xs) in through {
            let inner = parts.inner(b, cid)?;
            let sub = Self::rib_entries(parts, &xs, inner, cid, demands)?;
            demands.push((inner, Demand::Rib(sub)));
            out.push((b, Delta::Rib));
        }
        out.sort_by_key(|(p, _)| *p);
        Some(out)
    }

    /// One site's rings, of each clause's: the longest, which each other's
    /// is, but for a `union`'s ribcage or rib its member in that clause
    /// has none of, which it exports empty (else the checker says how they
    /// differ).
    fn merge_rings(parts: &Parts, list: &[(usize, Vec<RingD>)], demands: &mut Vec<(usize, Demand)>) -> Vec<RingD> {
        let Some((_, longest)) = list.iter().max_by_key(|(_, rs)| rs.len()) else { return Vec::new() };
        let longest = longest.clone();
        for (cid, rs) in list {
            let mut j = 0;
            for l in &longest {
                match (rs.get(j), l) {
                    (Some(a), _) if a == l => j += 1,
                    (Some(RingD::Rib(a)), RingD::Rib(b)) if a.iter().all(|e| b.contains(e)) && b.iter().all(|e| a.contains(e) || (e.1 == Delta::Rib && parts.is_union(e.0))) => {
                        for (u, _) in b.iter().filter(|e| !a.contains(e)) {
                            if let Some(m) = parts.inner(*u, *cid) {
                                demands.push((m, Demand::Rib(Vec::new())));
                            }
                        }
                        j += 1;
                    }
                    (_, RingD::At(u)) if parts.is_union(*u) => {
                        if let Some(m) = parts.inner(*u, *cid) {
                            demands.push((m, Demand::Cage(Vec::new())));
                        }
                    }
                    _ => {}
                }
            }
        }
        longest
    }

    fn ring(parts: &Parts, r: &RingD) -> Ring {
        match r {
            RingD::At(x) => Ring::At(parts.parts[*x].path.clone()),
            RingD::Rib(es) => Ring::Rib(es.iter().map(|(x, d)| (parts.parts[*x].path.clone(), *d)).collect()),
        }
    }

    fn bind_of(parts: &Parts, rings: &[RingD]) -> Bind {
        match rings {
            [RingD::Rib(es)] => Bind::Rib(es.iter().map(|(x, d)| (parts.parts[*x].path.clone(), *d)).collect()),
            _ => Bind::Cage(rings.iter().map(|r| Self::ring(parts, r)).collect()),
        }
    }

    /// Syntax type `t` as a signature writes it: a `mu` whose variable is
    /// used, or whose addresses are from it; a list by ellipsis, `(σ ...)`.
    pub(super) fn shown_sty(&self, t: &Rc<STy>, at: Span, interner: &mut Interner, names: &mut Vec<(usize, Sym, bool)>) -> Syntax {
        let sym = |s: &str, i: &mut Interner| Syntax::symbol(at, i.intern(s));
        match &**t {
            STy::Expr => sym("expr", interner),
            STy::Lambda => sym("lambda", interner),
            STy::Bvar => sym("bvar", interner),
            STy::Id => sym("id", interner),
            STy::Data => sym("data", interner),
            STy::Type => sym("type", interner),
            STy::Label => sym("label", interner),
            STy::Dvar => sym("dvar", interner),
            STy::Kind => sym("kind", interner),
            STy::Defn => sym("defn", interner),
            STy::Nil => Syntax::new(at, Datum::Nil),
            STy::Literal(n) => Syntax::list(at, vec![sym("literal", interner), Syntax::symbol(at, *n)]),
            STy::Pair(..) => {
                let mut items = Vec::new();
                let mut cur = t.clone();
                loop {
                    match &*cur.clone() {
                        STy::Pair(a, d) => {
                            items.push(self.shown_sty(a, at, interner, names));
                            cur = d.clone();
                        }
                        STy::Nil => return Syntax::list(at, items),
                        STy::Mu(id) if !names.iter().any(|(j, ..)| j == id) && let Some(e) = self.seq_elem(*id) => {
                            items.push(self.shown_sty(&e, at, interner, names));
                            items.push(sym("...", interner));
                            return Syntax::list(at, items);
                        }
                        _ => {
                            let tail = self.shown_sty(&cur, at, interner, names);
                            return super::list_of(at, items, Some(tail));
                        }
                    }
                }
            }
            STy::Import(b, bind) | STy::Export(b, bind) => {
                let head = if matches!(&**t, STy::Import(..)) { "import" } else { "export" };
                let b = self.shown_sty(b, at, interner, names);
                Syntax::list(at, vec![sym(head, interner), b, shown_bind(bind, at, interner)])
            }
            STy::Many(b) => {
                let b = self.shown_sty(b, at, interner, names);
                Syntax::list(at, vec![sym("many", interner), b])
            }
            STy::Typed(b, _) => self.shown_sty(b, at, interner, names),
            STy::Union(ms) => {
                let mut items = vec![sym("union", interner)];
                for m in ms {
                    items.push(self.shown_sty(m, at, interner, names));
                }
                Syntax::list(at, items)
            }
            STy::Mu(id) => {
                if let Some(e) = names.iter_mut().find(|(j, ..)| j == id) {
                    e.2 = true;
                    return Syntax::symbol(at, e.1);
                }
                if let Some(e) = self.seq_elem(*id) {
                    let e = self.shown_sty(&e, at, interner, names);
                    return Syntax::list(at, vec![e, sym("...", interner)]);
                }
                let v = interner.intern(&format!("m{}", names.len() + 1));
                names.push((*id, v, false));
                let body = self.shown_sty(&self.mus[*id].clone(), at, interner, names);
                let (_, _, used) = names.pop().expect("pushed");
                if used || open(&self.mus[*id]) { Syntax::list(at, vec![sym("mu", interner), Syntax::symbol(at, v), body]) } else { body }
            }
        }
    }

    /// The element of `mu` `id`, if it is a list as `(σ ...)` writes one
    /// (`Macros::seq`): its element as written.
    fn seq_elem(&self, id: usize) -> Option<Rc<STy>> {
        let STy::Union(ms) = &*self.mus[id] else { return None };
        let [nil, pair] = &ms[..] else { return None };
        let tail = |d: &Rc<STy>| matches!(&**d, STy::Mu(j) if *j == id);
        match (&**nil, &**pair) {
            (STy::Nil, STy::Pair(e, d)) if tail(d) && !matches!(&**e, STy::Bvar | STy::Dvar | STy::Export(..)) => Some(e.clone()),
            (STy::Export(n, Bind::Rib(none)), STy::Export(p, Bind::Rib(both))) if matches!(&**n, STy::Nil) && none.is_empty() && *both == vec![(vec![true], Delta::Rib), (vec![false], Delta::Rib)] => {
                let STy::Pair(e, d) = &**p else { return None };
                if !tail(d) {
                    return None;
                }
                match &**e {
                    STy::Export(x, Bind::Rib(es)) if matches!(&**x, STy::Bvar) && *es == vec![(Vec::new(), Delta::Var)] => Some(x.clone()),
                    STy::Export(x, Bind::Rib(es)) if matches!(&**x, STy::Dvar) && *es == vec![(Vec::new(), Delta::Dvar)] => Some(x.clone()),
                    STy::Export(..) => Some(e.clone()),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

/// Signature `s` as a message says it: each annotation, `union`, `mu`,
/// `many` or literal that is a list's rest after a ` . `, as written,
/// `(bvar . (import expr (rho (A var))))`, which a list's printing would
/// run into its elements.
pub(super) fn sig_text(s: &Syntax, interner: &Interner) -> String {
    let Datum::List { items, tail } = &s.datum else { return fixpt_read::write_syntax(s, interner) };
    let words = ["import", "export", "union", "mu", "many", "literal"];
    let mut out = String::from("(");
    for (k, i) in items.iter().enumerate() {
        if k > 0 && tail.is_none() && i.as_symbol().is_some_and(|w| words.contains(&interner.name(w))) {
            let rest = Syntax::list(s.span, items[k..].to_vec());
            out.push_str(&format!(" . {})", sig_text(&rest, interner)));
            return out;
        }
        if k > 0 {
            out.push(' ');
        }
        out.push_str(&sig_text(i, interner));
    }
    if let Some(t) = tail {
        out.push_str(&format!(" . {}", sig_text(t, interner)));
    }
    out.push(')');
    out
}

fn shown_bind(b: &Bind, at: Span, interner: &mut Interner) -> Syntax {
    let sym = |s: &str, i: &mut Interner| Syntax::symbol(at, i.intern(s));
    let addr = |a: &Addr, i: &mut Interner| {
        if a.is_empty() {
            Syntax::new(at, Datum::Nil)
        } else {
            let w: String = a.iter().rev().map(|s| if *s { 'A' } else { 'D' }).collect();
            Syntax::symbol(at, i.intern(&w))
        }
    };
    let rib = |es: &[(Addr, Delta)], i: &mut Interner| {
        let mut items = vec![sym("rho", i)];
        for (a, d) in es {
            let d = match d {
                Delta::None => "none",
                Delta::Var => "var",
                Delta::Dvar => "dvar",
                Delta::Place => "place",
                Delta::Rib => "rib",
                Delta::Env => "env",
            };
            items.push(Syntax::list(at, vec![addr(a, i), sym(d, i)]));
        }
        Syntax::list(at, items)
    };
    match b {
        Bind::Rib(es) => rib(es, interner),
        Bind::Cage(rings) => {
            let mut items = vec![sym("cage", interner)];
            for r in rings {
                items.push(match r {
                    Ring::Rib(es) => rib(es, interner),
                    Ring::At(a) => Syntax::list(at, vec![sym("at", interner), addr(a, interner)]),
                });
            }
            Syntax::list(at, items)
        }
        Bind::Direct(_) | Bind::Earlier(_) => rib(&[], interner),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn literals(s: &Syntax, interner: &Interner, out: &mut Vec<Sym>) {
        if let Some([h, n]) = s.as_proper_list()
            && h.as_symbol().is_some_and(|h| interner.name(h) == "literal")
            && let Some(n) = n.as_symbol()
        {
            out.push(n);
            return;
        }
        if let Datum::List { items, tail } = &s.datum {
            for i in items.iter().chain(tail.as_deref()) {
                literals(i, interner, out);
            }
        }
    }

    /// Each macro of the tests' programs whose signature is written, its
    /// signature inferred from its clauses alone, against the written one.
    #[test]
    fn inferred_against_written() {
        let dir = format!("{}/tests/programs/macros", env!("CARGO_MANIFEST_DIR"));
        let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
        names.sort();
        let (mut same, mut other, mut failed) = (Vec::new(), Vec::new(), Vec::new());
        for path in &names {
            let text = std::fs::read_to_string(path).unwrap();
            let mut interner = Interner::default();
            let Ok(forms) = fixpt_read::Reader::new(&text, fixpt_read::FileId(1), fixpt_read::SyntaxProfile::FX26, &mut interner).read_all() else { continue };
            let mut m = Macros::default();
            m.ensure_kernel(&mut interner).unwrap();
            for f in &forms {
                let Some(items) = f.as_proper_list() else { continue };
                if !items.first().and_then(|h| h.as_symbol()).is_some_and(|h| interner.name(h) == "define-syntax") || items.len() != 4 {
                    continue;
                }
                let Some(rules) = items[3].as_proper_list() else { continue };
                let name = items[1].as_symbol().unwrap();
                let file = path.file_name().unwrap().to_string_lossy().to_string();
                let label = format!("{file} {}", interner.name(name));
                let Ok((poly, sty, defn, desc)) = m.signature(&items[2], &mut interner) else { continue };
                let typed = text.contains("#:type") || text.contains("#:effect");
                if !poly.is_empty() || typed {
                    let _ = m.define(f, &mut interner);
                    continue;
                }
                let mut w = m.shown_sty(&sty, f.span, &mut interner, &mut Vec::new());
                if defn || desc {
                    let made = if defn { "defn" } else { "type" };
                    w = Syntax::list(f.span, vec![Syntax::symbol(f.span, interner.intern("->")), w, Syntax::symbol(f.span, interner.intern(made))]);
                }
                let w = fixpt_read::write_syntax(&w, &interner);
                let mut lits = Vec::new();
                literals(&items[2], &interner, &mut lits);
                let u = Unsigned { name, lits, clauses: rules[2..].to_vec(), span: f.span };
                match m.infer(&[u], &mut interner) {
                    Ok(s) => {
                        let i = fixpt_read::write_syntax(&s[0], &interner);
                        if i == w { same.push(label) } else { other.push(format!("{label}\n    written  {w}\n    inferred {i}")) }
                    }
                    Err(e) => failed.push(format!("{label}: {}", e.message)),
                }
                let _ = m.define(f, &mut interner);
            }
        }
        println!("same ({}):\n  {}", same.len(), same.join("\n  "));
        println!("other ({}):\n  {}", other.len(), other.join("\n  "));
        println!("failed ({}):\n  {}", failed.len(), failed.join("\n  "));
        // As many as when inference was built: none refused outright, and
        // those the tests' signatures say, the same.
        assert!(failed.is_empty(), "{}", failed.join("\n"));
        assert!(same.len() >= 72, "only {} the same", same.len());
    }
}
