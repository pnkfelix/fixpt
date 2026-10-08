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

use crate::ast::{Atom, D, DVar, Effect, ExpId, Kind, ModItem, Ty, TyId};
use crate::check::Checker;
use crate::error::{FxError, R};
use fixpt_read::{Span, Sym};
use std::collections::{HashMap, HashSet};

impl Checker {
    /// `(module item …)`: each item checked in the scope of those before
    /// it; the module's type, its abstract types bound in it.
    pub(crate) fn synth_module(&mut self, e: ExpId, items: &[ModItem]) -> R<(TyId, Effect)> {
        // Read from a file: it sees only the standard environment.
        if let Some((path, text, file)) = self.loaded.get(&e).cloned() {
            let span = self.arena.span_of(e);
            let outer = self.hidden.replace(((self.standard_len, self.env.len()), (self.standard_dscope, self.dscope.len())));
            let r = self.synth_module_here(e, items);
            self.hidden = outer;
            return r.map_err(|err| self.in_loaded(err, span, &path, &text, file));
        }
        self.synth_module_here(e, items)
    }

    fn synth_module_here(&mut self, e: ExpId, items: &[ModItem]) -> R<(TyId, Effect)> {
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

    /// A module's items, as `letrec*`'s (`crate::modorder`): its typed
    /// lambdas bound first, at their written types; every other item checked
    /// in order, in the scope of all of those and the items before it; then
    /// the lambdas, in the scope of everything, each with its recursive group
    /// (`module_groups`) checked to end, as a `define-rec`'s members are.
    #[allow(clippy::type_complexity)]
    fn synth_module_items(&mut self, items: &[ModItem], span: Span) -> R<(Vec<(Sym, DVar)>, Vec<(Sym, TyId)>, Vec<(Sym, TyId)>, Effect)> {
        let (mut abs, mut descs) = (Vec::new(), Vec::new());
        let mut eff = Effect::pure();
        let mut lambdas = self.module_lambdas(items);
        if let Some(init) = items.iter().find_map(|it| match it {
            ModItem::Val { init, infer: true, .. } if !self.is_lambda(*init) => Some(*init),
            _ => None,
        }) {
            return Err(FxError::at(self.arena.span_of(init), "`define*` defines a procedure: a `lambda`"));
        }
        if let Some((n, _, init, _)) = lambdas.iter().find(|(_, _, init, i)| matches!(items[*i], ModItem::Rec(_)) && !self.is_lambda(*init)) {
            return Err(FxError::at(self.arena.span_of(*init), format!("`{}`, in a `define-rec`, is a `lambda`", self.interner.name(*n))));
        }
        // An item whose value is a module as written, naming no item but such
        // earlier ones (`early_modules`), checked first, so that the typed
        // lambdas' types may select from it, and the order check knows its
        // values: `(define m (load-module "f"))`
        // and `(define g (subr pure ((select m t)) int) …)`. Checking it first
        // does not change when it is made.
        let mut typed: Vec<(usize, Sym, TyId)> = Vec::new();
        let early = self.early_modules(items);
        for &i in &early {
            let ModItem::Val { name, init, .. } = items[i] else { unreachable!("a value") };
            let (t, ie) = self.synth(init)?;
            eff = eff.union(&ie);
            let bound = self.name_nat(name, t);
            self.fixed_slots.insert(self.env.len());
            self.env.push((name, bound));
            typed.push((i, name, t));
        }
        // Each of those a module, its values' names bound in a `with` of it
        // not checked yet (`crate::modorder`).
        let known = typed
            .iter()
            .filter_map(|(_, n, t)| match self.arena.get(self.arena.resolve(*t)) {
                Ty::Module { vals, .. } => Some((*n, vals.iter().map(|(v, _)| *v).collect())),
                _ => None,
            })
            .collect();
        let outer = std::mem::replace(&mut self.hazard_modules, known);
        let names = Self::module_places(items).into_iter().map(|(n, _)| n).collect();
        let outer_items = std::mem::replace(&mut self.hazard_items, names);
        let hazards = self.module_hazards(items, &lambdas);
        self.hazard_modules = outer;
        self.hazard_items = outer_items;
        hazards?;
        // A `define*`'s type as written, and the type it is checked at first,
        // reading any global: what it reads is then found from its body.
        let star = |i: usize| matches!(items[i], ModItem::Val { infer: true, .. });
        let mut declared = Vec::new();
        for l in lambdas.iter_mut() {
            l.1 = self.resolve_selects(l.1, span)?;
            declared.push(l.1);
            if star(l.3) {
                l.1 = self.with_latent(l.1, &Effect::atom(crate::ast::Atom::Read(crate::ast::Region::Globals))).ok_or_else(|| {
                    FxError::at(self.arena.span_of(l.2), "`define*` finds what a procedure reads: its type is a `subr`")
                })?;
            }
        }
        let base = self.env.len();
        for (k, (n, t, _, i)) in lambdas.iter().enumerate() {
            let bound = if matches!(items[*i], ModItem::Val { .. }) { self.name_nat(*n, *t) } else { *t };
            self.env.push((*n, bound));
            self.known.insert((*n, base + k));
        }
        // The values each item has, at its type, in written order.
        for (i, item) in items.iter().enumerate() {
            if early.contains(&i) {
                continue;
            }
            match item.clone() {
                // Its representation seen only through its own conversions,
                // which stay inside the module.
                ModItem::Abs { name, var, rep, up, down, up_fn, down_fn } => {
                    // A type constructor's representation is a `dlambda` of
                    // its parameters: its conversions are polymorphic in
                    // them, as FX-91's at a higher kind (`crate::kinds`).
                    let (binders, rep) = match self.arena.get(rep).clone() {
                        Ty::Lam { params, body: D::Type(body) } => (params, body),
                        _ => (Vec::new(), rep),
                    };
                    let rep = self.resolve_selects(rep, span)?;
                    let t = if binders.is_empty() {
                        self.arena.ty(Ty::Var(var))
                    } else {
                        let f = self.arena.ty(Ty::Var(var));
                        let args = binders.iter().map(|(v, k)| self.var_d(*v, *k)).collect();
                        self.arena.ty(Ty::App { fun: f, args })
                    };
                    let identity = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: Effect::pure(), params: vec![rep], result: rep });
                    self.check(up_fn, identity)?;
                    self.check(down_fn, identity)?;
                    let up_t = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: Effect::pure(), params: vec![rep], result: t });
                    let down_t = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: Effect::pure(), params: vec![t], result: rep });
                    let (up_t, down_t) = if binders.is_empty() {
                        (up_t, down_t)
                    } else {
                        (
                            self.arena.ty(Ty::Poly { binders: binders.clone(), body: up_t }),
                            self.arena.ty(Ty::Poly { binders, body: down_t }),
                        )
                    };
                    self.env.push((up, up_t));
                    self.env.push((down, down_t));
                    abs.push((name, var));
                }
                ModItem::Desc { name, ty } => descs.push((name, self.resolve_selects(ty, span)?)),
                ModItem::Val { name, .. } if lambdas.iter().any(|(n, _, _, at)| *n == name && *at == i) => {}
                ModItem::Val { name, ty, init, .. } => {
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
                    typed.push((i, name, t));
                }
                ModItem::Rec(_) => {}
            }
        }
        let groups = self.module_groups(&lambdas);
        // Whether each group may not end, and why: found once, for its first
        // member (the group being the same for each of its members).
        let mut ends: Vec<Option<Result<(), String>>> = vec![None; lambdas.len()];
        for k in 0..lambdas.len() {
            let (n, t, init, i) = lambdas[k];
            let group: Vec<(Sym, TyId, ExpId)> = groups[k].iter().map(|g| (lambdas[*g].0, lambdas[*g].1, lambdas[*g].2)).collect();
            if star(i) {
                let found = self.module_define_star(k, &lambdas, &group, &mut ends, groups[k].first().copied(), declared[k], base)?;
                eff = eff.union(&found.1);
                lambdas[k].1 = found.0;
                typed.push((i, n, found.0));
                continue;
            }
            let rdepth = self.recursive.len();
            if let Some(&first) = groups[k].first() {
                if ends[first].is_none() {
                    ends[first] = Some(self.termination(&group));
                }
                if let Some(Err(why)) = &ends[first] {
                    for (m, mt, _) in &group {
                        self.recursive.push((*m, *mt));
                        self.spin_why.push(((*m, *mt), why.clone()));
                    }
                }
            }
            let r = match items[i] {
                ModItem::Rec(_) => self.check(init, t).map_err(|err| self.declared_error(n, t, init, err)),
                _ => self.check(init, t),
            };
            self.recursive.truncate(rdepth);
            eff = eff.union(&r?);
            typed.push((i, n, t));
        }
        typed.sort_by_key(|(i, ..)| *i);
        let vals = typed.into_iter().map(|(_, n, t)| (n, t)).collect();
        Ok((abs, descs, vals, eff))
    }

    /// Typed lambda `k` of a module, a `define*`, of type `declared` as
    /// written, bound at `base + k` (until then at its type reading any
    /// global; while first checked, at `declared`): checked at its type reading any global,
    /// then at the type with the globals its body read, found, its binding
    /// given that type, as a top-level `define*` is. Only a group of one
    /// (itself, if it calls itself), as at the top level, where a `define*`
    /// is in no `define-rec`. Its type found, and the effect.
    #[allow(clippy::too_many_arguments)]
    fn module_define_star(
        &mut self,
        k: usize,
        lambdas: &crate::modorder::Lambdas,
        group: &[(Sym, TyId, ExpId)],
        ends: &mut [Option<Result<(), String>>],
        first: Option<usize>,
        declared: TyId,
        base: usize,
    ) -> R<(TyId, Effect)> {
        let (n, wide, init, _) = lambdas[k];
        if let Some((m, _, _)) = group.iter().find(|(m, _, _)| *m != n) {
            return Err(FxError::at(
                self.arena.span_of(init),
                format!("`define*` `{}` is in a recursive group with `{}`: use `define`", self.interner.name(n), self.interner.name(*m)),
            ));
        }
        let why = first.map(|f| ends[f].get_or_insert_with(|| self.termination(group)).clone());
        let note = |c: &mut Self, t: TyId| {
            if let Some(Err(why)) = &why {
                c.recursive.push((n, t));
                c.spin_why.push(((n, t), why.clone()));
            }
        };
        // Bound at its type as written while it is first checked, as a
        // top-level `define*` is: a call of itself reads nothing more.
        self.env[base + k].1 = declared;
        let rdepth = self.recursive.len();
        note(self, wide);
        let first_check = self.check_declared(n, wide, init);
        self.recursive.truncate(rdepth);
        first_check?;
        let found = self.with_latent(declared, &self.globals_read_by(init)).expect("a subr");
        self.env[base + k].1 = found;
        note(self, found);
        let again = self.check_declared(n, found, init).map_err(|err| {
            let shown = self.show_ty(found);
            FxError::at(err.span, format!("`define*` found `{}` to be a {shown}: {}", self.interner.name(n), err.message))
        });
        self.recursive.truncate(rdepth);
        Ok((found, again?))
    }

    /// `(with m body)`: the body with `m`'s values in scope, by name, at
    /// their types for `m`: those it names, each with its position in `m`
    /// (`Facts::with_vals`), so that a `with` of one of a wide module's
    /// values, as a re-export is, binds one.
    pub(crate) fn synth_with(&mut self, e: ExpId, m: Sym, body: ExpId) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        if self.is_fx_module(m) {
            if self.lookup(m).is_some() {
                return Err(FxError::at(span, "`#%fx` is the standard bindings' module, which nothing else may be"));
            }
            let t = match self.arena.exp_at(body) {
                crate::ast::Exp::Var(n) if self.second_class(*n) && self.operator_at != Some(e) => return Err(self.named_only_to_call(span, *n)),
                crate::ast::Exp::Var(n) => self.standard_type(*n),
                _ => None,
            };
            let Some(t) = t else {
                return Err(FxError::at(span, "`(with #%fx name)` names one standard binding"));
            };
            // As an operator, noted by the application (`synth_app`).
            if self.operator_at != Some(e) {
                self.plain_fx(e);
            }
            return Ok((t, Effect::pure()));
        }
        let Some(mt) = self.lookup(m) else {
            return Err(FxError::at(span, format!("`{}` is not bound", self.interner.name(m))));
        };
        let Ty::Module { vals, .. } = self.arena.get(self.arena.resolve(mt)).clone() else {
            return Err(FxError::at(span, format!("`with` opens a module, and `{}` is a {}", self.interner.name(m), self.show_ty(mt))));
        };
        let free = self.free_vars(body);
        let used: Vec<(usize, (Sym, TyId))> = vals.iter().copied().enumerate().filter(|(_, (n, _))| free.contains(n)).collect();
        self.facts.with_vals.insert(e, used.iter().map(|(i, (n, _))| (*n, *i)).collect());
        let vals: Vec<(Sym, TyId)> = used.into_iter().map(|(_, v)| v).collect();
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
            let kind = self.arena.dvar_kind(*v);
            let w = self.arena.dvar_of(named, kind);
            self.skolems.push(w);
            self.module_vars.insert(w);
            let d = match kind {
                Kind::Type => D::Type(self.arena.ty(Ty::Var(w))),
                _ => {
                    self.abstract_funs.insert(w);
                    D::Fun(self.arena.ty(Ty::Var(w)))
                }
            };
            map.insert(*v, d);
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
        let effects = self.effect_selects_in(t);
        if found.is_empty() && effects.is_empty() {
            return Ok(t);
        }
        // Each effect selected, what its module says it is.
        let mut given: HashMap<DVar, D> = HashMap::new();
        for (v, (m, n)) in effects {
            given.insert(v, D::Effect(self.selected_effect(m, n, span)?));
        }
        let mut sel = HashMap::new();
        for (m, n, node) in found {
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
            self.link_global_select(m, node, to);
            sel.insert((m, n), to);
        }
        let outer = std::mem::replace(&mut self.select_map, sel);
        // Only what leads to a `select` is rebuilt; the rest stays itself.
        let keep = self.select_clean(t, &given);
        let outer_keep = self.subst_keep.replace(keep);
        let r = self.subst_memo(t, &given, &mut HashMap::new());
        self.subst_keep = outer_keep;
        self.select_map = outer;
        self.check_apps(r, span)?;
        Ok(r)
    }

    /// A global module's type, as `select` node `node` names it: that node
    /// from now on, linked to `to`, so that whatever leads to it is not
    /// rebuilt, and is shared, and shown by its name. Not a family, which is
    /// read as the `select` it is; nor a local module's, which may differ by
    /// scope, but for a module's item checked first (`fixed_slots`), bound
    /// once for all of the module it is in. As the FX-26 checker's
    /// `k-link-global-select`.
    fn link_global_select(&mut self, m: Sym, node: TyId, to: TyId) {
        if self.env.iter().rposition(|(x, _)| *x == m).is_some_and(|i| self.global_slots.contains(&i) || self.fixed_slots.contains(&i))
            && !matches!(self.arena.get(to), Ty::Lam { .. })
            && !matches!(self.arena.get(to), Ty::Var(v) if self.arena.dvar_kind(*v) != Kind::Type)
        {
            self.arena.set_link(node, to);
        }
    }

    /// Each `define-type` alias in scope, `(define-type t (select m t))`, of
    /// the global module `m` just bound, linked now to what it names: the
    /// aliases are declared ahead of `m`, and a type naming one shows by its
    /// name from the first, not once some later resolution meets it. As the
    /// FX-26 checker's `k-link-aliases`.
    pub(crate) fn link_aliases(&mut self, m: Sym) {
        let Some(mt) = self.lookup(m) else { return };
        let Ty::Module { abs, descs, .. } = self.arena.get(self.arena.resolve(mt)).clone() else { return };
        let nodes: Vec<(TyId, Sym)> = self
            .dscope
            .iter()
            .filter_map(|(_, d)| match d {
                crate::parse::DScope::Rec(t) => match self.arena.get(*t) {
                    Ty::Select(x, n) if *x == m => Some((self.arena.resolve(*t), *n)),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        for (node, n) in nodes {
            let to = match (abs.iter().find(|(a, _)| *a == n), descs.iter().find(|(d, _)| *d == n)) {
                (Some((_, v)), _) => self.arena.ty(Ty::Var(*v)),
                (None, Some((_, d))) => *d,
                (None, None) => continue,
            };
            self.link_global_select(m, node, to);
        }
    }

    /// The nodes of `t` from which no `select` is reached: none is, nor a
    /// `(select $k t)`, nor an effect variable `given` replaces. Each node a
    /// child of the one above it as `ty_kids` says, the walk the
    /// substitution makes; so what it keeps holds nothing it would change.
    fn select_clean(&self, t: TyId, given: &HashMap<DVar, D>) -> HashSet<TyId> {
        let mut nodes: Vec<TyId> = Vec::new();
        let mut seen: HashSet<TyId> = HashSet::new();
        let mut stack = vec![self.arena.resolve(t)];
        while let Some(n) = stack.pop() {
            if !seen.insert(n) {
                continue;
            }
            nodes.push(n);
            stack.extend(self.ty_kids(n).into_iter().map(|k| self.arena.resolve(k)));
        }
        let names_given = |e: &Effect| e.0.iter().any(|a| matches!(a, Atom::Var(v) if given.contains_key(v)));
        let mut dirty: HashSet<TyId> = nodes
            .iter()
            .copied()
            .filter(|n| match self.arena.get(*n) {
                Ty::Select(..) | Ty::ParamSel(..) => true,
                Ty::Subr { effect, .. } | Ty::PromptTag { effect, .. } | Ty::Composable { effect, .. } => names_given(effect),
                Ty::Lam { body: D::Effect(e), .. } => names_given(e),
                Ty::App { args, .. } | Ty::Named { args, .. } => args.iter().any(|d| matches!(d, D::Effect(e) if names_given(e))),
                _ => false,
            })
            .collect();
        loop {
            let more: Vec<TyId> = nodes
                .iter()
                .copied()
                .filter(|n| !dirty.contains(n) && self.ty_kids(*n).iter().any(|k| dirty.contains(&self.arena.resolve(*k))))
                .collect();
            if more.is_empty() {
                break;
            }
            dirty.extend(more);
        }
        nodes.into_iter().filter(|n| !dirty.contains(n)).collect()
    }

    /// The variable `(select m e)` read as an effect stands for, one for
    /// each, named as written.
    pub(crate) fn effect_select(&mut self, m: Sym, e: Sym) -> DVar {
        if let Some((_, v)) = self.effect_selects.iter().find(|(k, _)| *k == (m, e)) {
            return *v;
        }
        let shown = format!("(select {} {})", self.interner.name(m), self.interner.name(e));
        let v = self.arena.dvar_of(self.interner.intern(&shown), Kind::Effect);
        self.effect_selects.push(((m, e), v));
        v
    }

    /// Module `m`'s effect `e`, as its type says, `m` bound here; or an
    /// error at `span`.
    fn selected_effect(&mut self, m: Sym, e: Sym, span: Span) -> R<Effect> {
        let shown = |c: &Checker| format!("`(select {} {})`", c.interner.name(m), c.interner.name(e));
        let Some(mt) = self.lookup(m) else {
            return Err(FxError::at(span, format!("{}: `{}` is not bound here", shown(self), self.interner.name(m))));
        };
        let Ty::Module { descs, .. } = self.arena.get(self.arena.resolve(mt)).clone() else {
            return Err(FxError::at(span, format!("{}: `{}` is a {}, not a module", shown(self), self.interner.name(m), self.show_ty(mt))));
        };
        match descs.iter().find(|(d, _)| *d == e).and_then(|(_, d)| self.desc_effect(*d)) {
            Some(x) => Ok(x),
            None => Err(FxError::at(span, format!("{}: `{}` has no effect `{}`", shown(self), self.interner.name(m), self.interner.name(e)))),
        }
    }

    /// A module's description of an effect, `(define-effect e E)`'s: a
    /// description function of no parameters (`crate::kinds`) giving it.
    pub(crate) fn effect_desc(&mut self, e: Effect) -> TyId {
        self.arena.ty(Ty::Lam { params: Vec::new(), body: D::Effect(e) })
    }

    /// The effect a module's description `d` is, if it is one.
    pub(crate) fn desc_effect(&self, d: TyId) -> Option<Effect> {
        match self.arena.get(self.arena.resolve(d)) {
            Ty::Lam { params, body: D::Effect(e) } if params.is_empty() => Some(e.clone()),
            _ => None,
        }
    }

    /// The effect variables of `(select m e)`s in `t`, with what each selects.
    fn effect_selects_in(&self, t: TyId) -> Vec<(DVar, (Sym, Sym))> {
        let mut out: Vec<(DVar, (Sym, Sym))> = Vec::new();
        if self.effect_selects.is_empty() {
            return out;
        }
        let note = |e: &Effect, out: &mut Vec<(DVar, (Sym, Sym))>| {
            for a in &e.0 {
                if let Atom::Var(v) = a
                    && let Some((k, _)) = self.effect_selects.iter().find(|(_, w)| w == v)
                    && !out.iter().any(|(w, _)| w == v)
                {
                    out.push((*v, *k));
                }
            }
        };
        let mut stack = vec![t];
        let mut seen = HashSet::new();
        while let Some(t) = stack.pop() {
            let t = self.arena.resolve(t);
            if !seen.insert(t) {
                continue;
            }
            match self.arena.get(t) {
                Ty::Subr { effect, .. } | Ty::PromptTag { effect, .. } | Ty::Composable { effect, .. } => note(effect, &mut out),
                Ty::Lam { body: D::Effect(e), .. } => note(e, &mut out),
                Ty::App { args, .. } | Ty::Named { args, .. } => {
                    for a in args {
                        if let D::Effect(e) = a {
                            note(e, &mut out);
                        }
                    }
                }
                _ => {}
            }
            stack.extend(self.ty_kids(t));
        }
        out
    }

    /// Each description function applied in `t` given what it takes:
    /// checked where a `select` has just said what the function is.
    pub(crate) fn check_apps(&mut self, t: TyId, span: Span) -> R<()> {
        let mut stack = vec![t];
        let mut seen = HashSet::new();
        while let Some(t) = stack.pop() {
            let t = self.arena.resolve(t);
            if !seen.insert(t) {
                continue;
            }
            if let Ty::App { fun, args } = self.arena.get(t).clone() {
                let shown = self.show_ty(fun);
                let parts = self.fun_kind(fun).map(|k| self.arena.arrow_parts(k).map(|(p, r)| (p.to_vec(), r)));
                match parts {
                    Some(None) => return Err(FxError::at(span, format!("`{shown}` is not a description function: it is applied"))),
                    Some(Some((params, result))) => {
                        if params.len() != args.len() {
                            return Err(FxError::at(span, format!("`{shown}` takes {} description(s), and has {}", params.len(), args.len())));
                        }
                        if !matches!(result, Kind::Type | Kind::Data) {
                            return Err(FxError::at(span, format!("`{shown}` gives a description of kind {}, not a type", self.show_kind(result))));
                        }
                        for (i, (d, k)) in args.iter().zip(params).enumerate() {
                            if !self.d_fits(d, k) {
                                return Err(FxError::at(span, format!("`{shown}` takes a {} as description {}", self.show_kind(k), i + 1)));
                            }
                        }
                    }
                    None => {}
                }
            }
            stack.extend(self.ty_kids(t));
        }
        Ok(())
    }

    /// The same, where `params` are about to be bound and so may not be
    /// selected from: a parameter's type naming another is a dependent
    /// type, which waits for M5.
    pub(crate) fn resolve_selects_outside(&mut self, t: TyId, params: &[Sym], span: Span) -> R<TyId> {
        let mut found = Vec::new();
        self.selects_in(t, &mut HashSet::new(), &mut found);
        if let Some((m, n, _)) = found.iter().find(|(m, _, _)| params.contains(m)) {
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

    pub(crate) fn selects_in(&self, t: TyId, seen: &mut HashSet<TyId>, out: &mut Vec<(Sym, Sym, TyId)>) {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return;
        }
        if let Ty::Select(m, n) = self.arena.get(t) {
            out.push((*m, *n, t));
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
            Ty::Base(_) | Ty::Void | Ty::Nil | Ty::False | Ty::Proving { .. } | Ty::Var(_) | Ty::Nat(_) | Ty::Place(_) | Ty::Select(..) | Ty::ParamSel(..) | Ty::Link(_) => Vec::new(),
            Ty::Union(ms) => ms.clone(),
            Ty::Subr { params, result, .. } => params.iter().copied().chain([*result]).collect(),
            Ty::Poly { body, .. } => vec![*body],
            Ty::Ref(a, _) | Ty::Array(a, _) | Ty::ICell(a, _) | Ty::MarkKey(a, _) => vec![*a],
            Ty::Pair(a, b, _, _) => vec![*a, *b],
            Ty::PromptTag { answer, payload, .. } => vec![*answer, *payload],
            Ty::Composable { arg, answer, .. } => vec![*arg, *answer],
            Ty::Product(ps) | Ty::Sum(ps) => ps.iter().map(|(_, x)| *x).collect(),
            Ty::Bloblet { fields, .. } => fields.clone(),
            Ty::Named { args, .. } => args.iter().filter_map(|d| if let D::Type(x) | D::Fun(x) = d { Some(*x) } else { None }).collect(),
            Ty::App { fun, args } => [*fun].into_iter().chain(args.iter().filter_map(|d| if let D::Type(x) | D::Fun(x) = d { Some(*x) } else { None })).collect(),
            Ty::Lam { body: D::Type(x) | D::Fun(x), .. } => vec![*x],
            Ty::Lam { .. } => Vec::new(),
            Ty::NList { elem, .. } => vec![*elem],
            Ty::Module { descs, vals, .. } => descs.iter().chain(vals).map(|(_, x)| *x).collect(),
        }
    }

    /// A module of type `got` made one of type `want`, which has fewer of
    /// its values or the same in another order: each of `want`'s values'
    /// position in `got`, if `got`'s values so chosen fit `want`.
    pub(crate) fn reshape(&mut self, got: TyId, want: TyId) -> Option<Vec<usize>> {
        let (Ty::Module { abs, descs, vals }, Ty::Module { vals: wanted, .. }) =
            (self.arena.get(self.arena.resolve(got)).clone(), self.arena.get(self.arena.resolve(want)).clone())
        else {
            return None;
        };
        let at: Vec<usize> = wanted.iter().map(|(n, _)| vals.iter().position(|(m, _)| m == n)).collect::<Option<_>>()?;
        if at.len() == vals.len() && at.iter().enumerate().all(|(i, k)| i == *k) {
            return None;
        }
        let chosen = at.iter().map(|k| vals[*k]).collect();
        let t = self.arena.ty(Ty::Module { abs, descs, vals: chosen });
        self.subtype(t, want).then_some(at)
    }

    /// A module-typed binding's types, by component name: each abstract
    /// type as named for the binding, each transparent one as it is.
    pub(crate) fn module_types(&mut self, mt: TyId) -> Vec<(Sym, TyId)> {
        match self.arena.get(self.arena.resolve(mt)).clone() {
            Ty::Module { abs, descs, .. } => {
                let mut out: Vec<(Sym, TyId)> = abs.iter().map(|(n, v)| (*n, self.arena.ty(Ty::Var(*v)))).collect();
                out.extend(descs);
                out
            }
            _ => Vec::new(),
        }
    }

    /// `t` with each `(select $k x)` what `map` says it is.
    pub(crate) fn instantiate_params(&mut self, t: TyId, map: &HashMap<(usize, Sym), TyId>) -> TyId {
        if map.is_empty() {
            return t;
        }
        let outer = std::mem::replace(&mut self.param_map, map.clone());
        let r = self.subst(t, &HashMap::new());
        self.param_map = outer;
        r
    }

    fn param_sels(&self, t: TyId, seen: &mut HashSet<TyId>, out: &mut Vec<(usize, Sym)>) {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return;
        }
        if let Ty::ParamSel(k, n) = self.arena.get(t) {
            if !out.contains(&(*k, *n)) {
                out.push((*k, *n));
            }
            return;
        }
        for k in self.ty_kids(t) {
            self.param_sels(k, seen, out);
        }
    }

    /// A dependent procedure's parameter and result types for a call with
    /// `args`: each `(select $k x)` the type `x` of the module the `k`th
    /// argument names. That argument must be a module's name, which gives
    /// its types their identity.
    pub(crate) fn dependent_args(&mut self, params: &[TyId], result: TyId, args: &[ExpId], span: Span) -> R<(Vec<TyId>, TyId)> {
        let mut found = Vec::new();
        let mut seen = HashSet::new();
        for t in params.iter().chain([&result]) {
            self.param_sels(*t, &mut seen, &mut found);
        }
        if found.is_empty() {
            return Ok((params.to_vec(), result));
        }
        let mut map = HashMap::new();
        for (k, x) in found {
            let named = match args.get(k).map(|a| self.arena.exp_at(*a).clone()) {
                Some(crate::ast::Exp::Var(v)) => self.lookup(v).map(|t| (v, t)),
                _ => None,
            };
            let Some((v, mt)) = named else {
                return Err(FxError::at(
                    span,
                    format!("argument {} is a module the procedure's types depend on: give it by name (bind it with `let` first)", k + 1),
                ));
            };
            let Some((_, t)) = self.module_types(mt).into_iter().find(|(n, _)| *n == x) else {
                return Err(FxError::at(span, format!("`{}` has no type `{}`", self.interner.name(v), self.interner.name(x))));
            };
            map.insert((k, x), t);
        }
        let params: Vec<TyId> = params.iter().map(|p| self.instantiate_params(*p, &map)).collect();
        let result = self.instantiate_params(result, &map);
        for t in params.iter().chain([&result]) {
            self.check_apps(*t, span)?;
        }
        Ok((params, result))
    }

    /// Whether `v` was made for a module's abstract type as it was bound.
    pub(crate) fn is_module_var(&self, v: DVar) -> bool {
        self.module_vars.contains(&v)
    }
}
