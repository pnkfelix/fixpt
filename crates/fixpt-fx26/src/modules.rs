//! First-class modules (`docs/research/first-class-modules.md`, stage M1):
//! `module`, `moduleof`, `with` and `select`, in the Rust checker.
//!
//! A module's type is an existential package: its abstract types are
//! binders of its `moduleof`. A variable of that type has them renamed for
//! itself as it is bound (`name_module`), each a type equal only to itself,
//! named `m..t`; `(select m t)` is that type (`resolve_selects`). Two
//! bindings of one module are two sets of abstract types: Sheldon's rule
//! that a `let`-bound module is opaque. Nothing that outlives a binding may
//! mention its abstract types (`forget_nats`, which also forgets sizes).

use crate::ast::{D, DVar, Effect, ExpId, Kind, ModItem, Ty, TyId};
use crate::check::Checker;
use crate::error::{FxError, R};
use fixpt_read::{Span, Sym};
use std::collections::{HashMap, HashSet};

impl Checker {
    /// `(module item …)`: each item checked in the scope of those before
    /// it; the module's type, its abstract types bound in it.
    pub(crate) fn synth_module(&mut self, e: ExpId, items: &[ModItem]) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let (depth, named) = (self.env.len(), self.skolems.len());
        let r = self.synth_module_items(items, span);
        self.truncate_env(depth);
        let r = r.and_then(|(abs, descs, vals, eff)| {
            // A component's module, bound inside, has abstract types no one
            // outside can name.
            let inner: Vec<DVar> = self.skolems[named..].to_vec();
            for (n, t) in &vals {
                if let Some(v) = inner.iter().find(|v| self.mentions_var(*t, **v)) {
                    let shown = self.interner.name(self.arena.dvar_name(*v)).to_string();
                    return Err(FxError::at(span, format!("`{}`'s type mentions `{shown}`, which is not known outside the module", self.interner.name(*n))));
                }
            }
            Ok((self.arena.ty(Ty::Module { abs, descs, vals }), eff))
        });
        self.skolems.truncate(named);
        let (t, eff) = r?;
        let eff = self.mask(e, &eff, t);
        Ok((t, eff))
    }

    #[allow(clippy::type_complexity)]
    fn synth_module_items(&mut self, items: &[ModItem], span: Span) -> R<(Vec<(Sym, DVar)>, Vec<(Sym, TyId)>, Vec<(Sym, TyId)>, Effect)> {
        let (mut abs, mut descs, mut vals) = (Vec::new(), Vec::new(), Vec::new());
        let mut eff = Effect::pure();
        for item in items {
            match item.clone() {
                // Its representation seen only through its own conversions,
                // which stay inside the module.
                ModItem::Abs { name, var, rep, up, down, up_fn, down_fn } => {
                    let rep = self.resolve_selects(rep, span)?;
                    let t = self.arena.ty(Ty::Var(var));
                    let identity = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: Effect::pure(), params: vec![rep], result: rep });
                    self.check(up_fn, identity)?;
                    self.check(down_fn, identity)?;
                    let up_t = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: Effect::pure(), params: vec![rep], result: t });
                    let down_t = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: Effect::pure(), params: vec![t], result: rep });
                    self.env.push((up, up_t));
                    self.env.push((down, down_t));
                    abs.push((name, var));
                }
                ModItem::Desc { name, ty } => descs.push((name, self.resolve_selects(ty, span)?)),
                ModItem::Val { name, ty, init } => {
                    let (t, ie) = match ty {
                        Some(t) => {
                            let t = self.resolve_selects(t, span)?;
                            (t, self.check(init, t)?)
                        }
                        None => self.synth(init)?,
                    };
                    eff = eff.union(&ie);
                    let bound = self.name_nat(name, t);
                    self.env.push((name, bound));
                    vals.push((name, t));
                }
                ModItem::Rec(group) => {
                    let mut bindings = Vec::new();
                    for (n, t, init) in group {
                        bindings.push((n, self.resolve_selects(t, span)?, init));
                    }
                    let base = self.env.len();
                    self.env.extend(bindings.iter().map(|(n, t, _)| (*n, *t)));
                    self.known.extend(bindings.iter().enumerate().map(|(i, (n, _, _))| (*n, base + i)));
                    if let Some((n, _, init)) = bindings.iter().find(|(_, _, init)| !self.is_lambda(*init)) {
                        return Err(FxError::at(self.arena.span_of(*init), format!("`{}`, in a `define-rec`, is a `lambda`", self.interner.name(*n))));
                    }
                    let rdepth = self.recursive.len();
                    self.note_termination(&bindings);
                    let r = (|| {
                        let mut ge = Effect::pure();
                        for (n, t, init) in &bindings {
                            ge = ge.union(&self.check(*init, *t).map_err(|err| self.declared_error(*n, *t, *init, err))?);
                        }
                        Ok(ge)
                    })();
                    self.recursive.truncate(rdepth);
                    eff = eff.union(&r?);
                    vals.extend(bindings.iter().map(|(n, t, _)| (*n, *t)));
                }
            }
        }
        Ok((abs, descs, vals, eff))
    }

    /// `(with m body)`: the body with `m`'s values in scope, by name, at
    /// their types for `m`.
    pub(crate) fn synth_with(&mut self, e: ExpId, m: Sym, body: ExpId) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let Some(mt) = self.lookup(m) else {
            return Err(FxError::at(span, format!("`{}` is not bound", self.interner.name(m))));
        };
        let Ty::Module { vals, .. } = self.arena.get(self.arena.resolve(mt)).clone() else {
            return Err(FxError::at(span, format!("`with` opens a module, and `{}` is a {}", self.interner.name(m), self.show_ty(mt))));
        };
        self.facts.with_vals.insert(e, vals.iter().map(|(n, _)| *n).collect());
        let naming = self.naming_effect(m, mt);
        let (t, be) = self.in_scope(&vals, |c| c.synth(body))?;
        let eff = self.mask(e, &naming.union(&be), t);
        Ok((t, eff))
    }

    /// A module's type, bound to `name`: its abstract types renamed for this
    /// binding, each `name..t`, kept until the binding's scope ends. Any
    /// other type as it is.
    pub(crate) fn name_module(&mut self, name: Sym, t: TyId) -> TyId {
        let Ty::Module { abs, descs, vals } = self.arena.get(self.arena.resolve(t)).clone() else { return t };
        if abs.is_empty() {
            return t;
        }
        let n = self.interner.name(name).to_string();
        let mut map: HashMap<DVar, D> = HashMap::new();
        let mut fresh = Vec::new();
        for (a, v) in &abs {
            let named = self.interner.intern(&format!("{n}..{}", self.interner.name(*a)));
            let w = self.arena.dvar_of(named, Kind::Type);
            self.skolems.push(w);
            self.module_vars.insert(w);
            map.insert(*v, D::Type(self.arena.ty(Ty::Var(w))));
            fresh.push((*a, w));
        }
        let descs = descs.iter().map(|(d, x)| (*d, self.subst(*x, &map))).collect();
        let vals = vals.iter().map(|(x, y)| (*x, self.subst(*y, &map))).collect();
        self.arena.ty(Ty::Module { abs: fresh, descs, vals })
    }

    /// `t` with each `(select m n)` in it replaced by what it is: `m`'s
    /// abstract type `n`, as `m` was bound, or its description `n`.
    pub(crate) fn resolve_selects(&mut self, t: TyId, span: Span) -> R<TyId> {
        let mut found = Vec::new();
        self.selects_in(t, &mut HashSet::new(), &mut found);
        if found.is_empty() {
            return Ok(t);
        }
        let mut sel = HashMap::new();
        for (m, n) in found {
            let shown = |c: &Checker| format!("`(select {} {})`", c.interner.name(m), c.interner.name(n));
            let Some(mt) = self.lookup(m) else {
                return Err(FxError::at(span, format!("{}: `{}` is not bound here", shown(self), self.interner.name(m))));
            };
            let Ty::Module { abs, descs, .. } = self.arena.get(self.arena.resolve(mt)).clone() else {
                return Err(FxError::at(span, format!("{}: `{}` is a {}, not a module", shown(self), self.interner.name(m), self.show_ty(mt))));
            };
            let to = match (abs.iter().find(|(a, _)| *a == n), descs.iter().find(|(d, _)| *d == n)) {
                (Some((_, v)), _) => self.arena.ty(Ty::Var(*v)),
                (None, Some((_, d))) => *d,
                (None, None) => {
                    return Err(FxError::at(span, format!("{}: `{}` has no type `{}`", shown(self), self.interner.name(m), self.interner.name(n))));
                }
            };
            sel.insert((m, n), to);
        }
        let outer = std::mem::replace(&mut self.select_map, sel);
        let r = self.subst(t, &HashMap::new());
        self.select_map = outer;
        Ok(r)
    }

    /// The same, where `params` are about to be bound and so may not be
    /// selected from: a parameter's type naming another is a dependent
    /// type, which waits for M5.
    pub(crate) fn resolve_selects_outside(&mut self, t: TyId, params: &[Sym], span: Span) -> R<TyId> {
        let mut found = Vec::new();
        self.selects_in(t, &mut HashSet::new(), &mut found);
        if let Some((m, n)) = found.iter().find(|(m, _)| params.contains(m)) {
            return Err(FxError::at(
                span,
                format!(
                    "`(select {} {})` names a parameter of the same `lambda`: a dependent type, not supported yet",
                    self.interner.name(*m),
                    self.interner.name(*n)
                ),
            ));
        }
        self.resolve_selects(t, span)
    }

    fn selects_in(&self, t: TyId, seen: &mut HashSet<TyId>, out: &mut Vec<(Sym, Sym)>) {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return;
        }
        if let Ty::Select(m, n) = self.arena.get(t) {
            if !out.contains(&(*m, *n)) {
                out.push((*m, *n));
            }
            return;
        }
        for k in self.ty_kids(t) {
            self.selects_in(k, seen, out);
        }
    }

    /// Whether type variable `v` is somewhere in `t`.
    pub(crate) fn mentions_var(&self, t: TyId, v: DVar) -> bool {
        let mut stack = vec![t];
        let mut seen = HashSet::new();
        while let Some(t) = stack.pop() {
            let t = self.arena.resolve(t);
            if !seen.insert(t) {
                continue;
            }
            if matches!(self.arena.get(t), Ty::Var(w) if *w == v) {
                return true;
            }
            stack.extend(self.ty_kids(t));
        }
        false
    }

    /// The types `t` is made of, one level down.
    pub(crate) fn ty_kids(&self, t: TyId) -> Vec<TyId> {
        match self.arena.get(self.arena.resolve(t)) {
            Ty::Base(_) | Ty::Void | Ty::Var(_) | Ty::Nat(_) | Ty::Place(_) | Ty::Select(..) | Ty::Link(_) => Vec::new(),
            Ty::Subr { params, result, .. } => params.iter().copied().chain([*result]).collect(),
            Ty::Poly { body, .. } => vec![*body],
            Ty::Ref(a, _) | Ty::Array(a, _) | Ty::ICell(a, _) | Ty::MarkKey(a, _) => vec![*a],
            Ty::Pair(a, b, _) => vec![*a, *b],
            Ty::PromptTag { answer, payload, .. } => vec![*answer, *payload],
            Ty::Composable { arg, answer, .. } => vec![*arg, *answer],
            Ty::Product(ps) | Ty::Sum(ps) => ps.iter().map(|(_, x)| *x).collect(),
            Ty::Bloblet { fields, .. } => fields.clone(),
            Ty::Named { args, .. } => args.iter().filter_map(|d| if let D::Type(x) = d { Some(*x) } else { None }).collect(),
            Ty::NList { elem, .. } => vec![*elem],
            Ty::Module { descs, vals, .. } => descs.iter().chain(vals).map(|(_, x)| *x).collect(),
        }
    }

    /// Whether `v` was made for a module's abstract type as it was bound.
    pub(crate) fn is_module_var(&self, v: DVar) -> bool {
        self.module_vars.contains(&v)
    }
}
