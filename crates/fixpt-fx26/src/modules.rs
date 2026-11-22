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
use crate::check::{Anchor, Checker, Pick};
use crate::error::{FxError, R};
use fixpt_read::{Span, Sym};
use fixpt_hash::{HashMap, HashSet};

impl Checker {
    /// `(module item …)`: each item checked in the scope of those before
    /// it; the module's type, its abstract types bound in it.
    pub(crate) fn synth_module(&mut self, e: ExpId, items: &[ModItem]) -> R<(TyId, Effect)> {
        // Read from a file: it sees only the standard environment.
        if let Some((path, _, file)) = self.loaded.get(&e).cloned() {
            let outer = self.hidden.replace(((self.standard_len, self.env.len()), (self.standard_dscope, self.dscope.len())));
            let built_in = crate::built_in_module(&path).is_some() as usize;
            self.in_built_in += built_in;
            let r = self.synth_module_here(e, items);
            self.in_built_in -= built_in;
            self.hidden = outer;
            return r.map_err(|err| self.in_loaded(err, file));
        }
        self.synth_module_here(e, items)
    }

    fn synth_module_here(&mut self, e: ExpId, items: &[ModItem]) -> R<(TyId, Effect)> {
        let r = self.synth_module_made(e, items);
        if self.record_types
            && let Ok((t, _)) = &r
        {
            self.facts.module_own.insert(e, *t);
        }
        r
    }

    fn synth_module_made(&mut self, e: ExpId, items: &[ModItem]) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let (depth, named) = (self.env.len(), self.skolems.len());
        let r = self.synth_module_items(items, span);
        // The items' own types, which a later item's may name as that
        // member's (`members_named`).
        let r = r.map(|(abs, descs, vals, eff)| {
            let owned = self.items_own_types(&vals, depth);
            (abs, descs, vals, eff, owned)
        });
        self.truncate_env(depth);
        let r = r.and_then(|(abs, descs, vals, eff, owned)| {
            // The product its items make, one value each (an `include` the
            // module included), before its type is made of it: what the
            // paths of `reshaped` are into.
            if self.record_types {
                let raw = self.arena.ty(Ty::Module { abs: abs.clone(), descs: descs.clone(), vals: vals.clone() });
                self.facts.module_raw.insert(e, raw);
            }
            // A component's module, bound inside, has abstract types no one
            // outside can name.
            let mut inner: Vec<DVar> = self.skolems[named..].to_vec();
            inner.extend(self.anchored(&inner));
            inner.retain(|v| !owned.iter().any(|(w, _, _)| w == v));
            for (n, t) in &vals {
                if let Some(v) = inner.iter().find(|v| self.mentions_var(*t, **v)) {
                    let shown = self.interner.name(self.arena.dvar_name(*v)).to_string();
                    return Err(FxError::at(span, format!("`{}`'s type mentions `{shown}`, which is not known outside the module", self.interner.name(*n))));
                }
            }
            let t = self.module_type(e, span, items, abs, descs, vals)?;
            self.members_named(t, &owned, span).map(|t| (t, eff))
        });
        self.skolems.truncate(named);
        let (t, eff) = r?;
        let eff = self.mask(e, &eff, t);
        Ok((t, eff))
    }

    /// Each value of `vals` of a module being made bound in it, at `depth`
    /// or after, to a module of abstract types (`name_module`): each type's
    /// variable, `base..t`, the item and the type's name; a name of the
    /// checkers' own (`%…`) none. What a later item's type may name as that
    /// member's (`members_named`).
    fn items_own_types(&self, vals: &[(Sym, TyId)], depth: usize) -> Vec<(DVar, Sym, Sym)> {
        let mut out = Vec::new();
        for (x, _) in vals {
            if self.interner.name(*x).starts_with('%') {
                continue;
            }
            let Some(i) = self.env.positions(*x).find(|i| *i >= depth) else { continue };
            if let Ty::Module { abs, .. } = self.arena.get(self.arena.resolve(self.env[i].1)) {
                out.extend(abs.iter().map(|(a, w)| (*w, *x, *a)));
            }
        }
        out
    }

    /// Module type `t`, as made, each value's type that names an item's own
    /// types (`owned`, `items_own_types`) naming them as that member's,
    /// `(select base t)` (`Ty::MemberSel`), by its place in `t`: the
    /// module's type a dependent one, which a binding of it reads as its
    /// paths, `e.base..t` (`docs/research/dependent-moduleof.md`, step 3).
    /// Refused if the item is no earlier value of `t` (hidden, or after),
    /// or a description names one, as a type no one outside knows.
    fn members_named(&mut self, t: TyId, owned: &[(DVar, Sym, Sym)], span: Span) -> R<TyId> {
        if owned.is_empty() {
            return Ok(t);
        }
        let Ty::Module { abs, descs, vals } = self.arena.get(self.arena.resolve(t)).clone() else { return Ok(t) };
        let unknown = |c: &Self, n: Sym, w: DVar| {
            let shown = c.interner.name(c.arena.dvar_name(w)).to_string();
            FxError::at(span, format!("`{}`'s type mentions `{shown}`, which is not known outside the module", c.interner.name(n)))
        };
        for (n, d) in &descs {
            if let Some((w, _, _)) = owned.iter().find(|(w, _, _)| self.mentions_var(*d, *w)) {
                return Err(unknown(self, *n, *w));
            }
        }
        let mut out = Vec::with_capacity(vals.len());
        for (j, (n, ty)) in vals.iter().enumerate() {
            let mut map: HashMap<DVar, D> = HashMap::default();
            for (w, x, a) in owned {
                if !self.mentions_var(*ty, *w) {
                    continue;
                }
                let Some(k) = vals[..j].iter().position(|(m, _)| m == x) else { return Err(unknown(self, *n, *w)) };
                let sel = self.arena.ty(Ty::MemberSel(k, *x, *a));
                map.insert(*w, if self.arena.dvar_kind(*w) == Kind::Type { D::Type(sel) } else { D::Fun(sel) });
            }
            out.push((*n, if map.is_empty() { *ty } else { self.subst(*ty, &map) }));
        }
        Ok(self.arena.ty(Ty::Module { abs, descs, vals: out }))
    }

    /// A module's type, of its abstract types, descriptions and values: an
    /// `extend`'s, of the two it holds; an `include`s' (`with_includes`), of
    /// the modules included; a module's that includes some, of those and its
    /// own. As the FX-26 checker's `k-module-type`.
    fn module_type(&mut self, e: ExpId, span: Span, items: &[ModItem], abs: Vec<(Sym, DVar)>, descs: Vec<(Sym, TyId)>, vals: Vec<(Sym, TyId)>) -> R<TyId> {
        if self.is_extend(items) {
            return self.extended(e, span, &vals);
        }
        let bucket = |c: &Self, n: Sym| {
            let n = c.interner.name(n);
            n.starts_with("%include-") || n.starts_with("%hinclude-")
        };
        if !items.is_empty() && items.iter().all(|it| matches!(it, ModItem::Val { name, .. } if bucket(self, *name))) {
            return self.included(e, span, Vec::new(), Vec::new(), Vec::new(), &vals, None);
        }
        let t = if let Some(k) = vals.iter().position(|(n, _)| self.interner.name(*n) == "%include") {
            let own: Vec<(Sym, TyId)> = vals.iter().enumerate().filter(|(i, _)| *i != k).map(|(_, v)| *v).collect();
            self.included(e, span, abs, descs, own, &vals[k..=k], Some(k))?
        } else {
            self.arena.ty(Ty::Module { abs, descs, vals })
        };
        self.hiding(e, span, t)
    }

    /// Module type `t` without what `(hide item …)` hid (`TODO.md` §69):
    /// each name a `%hidden:name` type marks (the parser's, or `included`'s
    /// for a hidden `include`), the markers too. A hidden abstract type an
    /// exported type mentions is refused, for now (the user's, 2026-10-09);
    /// a hidden abbreviation is in what it abbreviates already. Made of
    /// the values left by position (a reshape, on any it has).
    fn hiding(&mut self, e: ExpId, span: Span, t: TyId) -> R<TyId> {
        let Ty::Module { abs, descs, vals } = self.arena.get(t).clone() else {
            return Ok(t);
        };
        // Types and values marked apart (`%hidden:`, `%hiddenv:`): a type
        // and a value may share a name.
        let marked = |c: &Self, prefix: &str| -> Vec<String> {
            descs.iter().filter_map(|(n, _)| c.interner.name(*n).strip_prefix(prefix).map(str::to_string)).collect()
        };
        let (hidden, hidden_vals) = (marked(self, "%hidden:"), marked(self, "%hiddenv:"));
        if hidden.is_empty() && hidden_vals.is_empty() {
            return Ok(t);
        }
        // As sets of names: a module's hidden includes hide thousands.
        let hidden: HashSet<Sym> = hidden.iter().map(|h| self.interner.intern(h)).collect();
        let hidden_vals: HashSet<Sym> = hidden_vals.iter().map(|h| self.interner.intern(h)).collect();
        let shown = |_: &Self, n: Sym| !hidden.contains(&n);
        let shown_val = |_: &Self, n: Sym| !hidden_vals.contains(&n);
        let marker = |c: &Self, n: Sym| c.interner.name(n).starts_with("%hidden:") || c.interner.name(n).starts_with("%hiddenv:");
        let (kept_abs, gone): (Vec<(Sym, DVar)>, Vec<(Sym, DVar)>) = abs.into_iter().partition(|(n, _)| shown(self, *n));
        let descs: Vec<(Sym, TyId)> = descs.into_iter().filter(|(n, _)| !marker(self, *n) && shown(self, *n)).collect();
        let at: Vec<Pick> = self.facts.reshaped.get(&e).cloned().unwrap_or_else(|| (0..vals.len()).map(Pick::Value).collect());
        let (mut out, mut path) = (Vec::new(), Vec::new());
        for (v, p) in vals.iter().zip(at) {
            if shown_val(self, v.0) {
                out.push(*v);
                path.push(p);
            }
        }
        for (n, t) in out.iter().chain(&descs) {
            if let Some((h, _)) = gone.iter().find(|(_, v)| self.mentions_var(*t, *v)) {
                let (n, h) = (self.interner.name(*n), self.interner.name(*h));
                return Err(FxError::at(span, format!("`{n}`'s type mentions `{h}`, which is hidden in this module: show `{h}`, or hide `{n}` as well")));
            }
        }
        if path.iter().enumerate().any(|(i, p)| *p != Pick::Value(i)) || path.len() != vals.len() {
            self.facts.reshaped.insert(e, path);
        }
        Ok(self.arena.ty(Ty::Module { abs: kept_abs, descs, vals: out }))
    }

    /// The modules `from` included (`TODO.md` §69), their values and types
    /// with `abs`, `descs` and `vals`, the module's own: one bucket, a name
    /// given twice refused. Made of theirs by path, from the modules of
    /// value `at` if it is a module's own `%include` (its values then
    /// after it), else from each of `from`, values `0`, `1`, ….
    #[allow(clippy::too_many_arguments)]
    fn included(&mut self, e: ExpId, span: Span, abs: Vec<(Sym, DVar)>, mut descs: Vec<(Sym, TyId)>, own: Vec<(Sym, TyId)>, from: &[(Sym, TyId)], at: Option<usize>) -> R<TyId> {
        let (mut out, mut path): (Vec<(Sym, TyId)>, Vec<Pick>) = (Vec::new(), Vec::new());
        let mut own_descs = std::mem::take(&mut descs);
        let (mut fresh, mut map) = (Vec::new(), HashMap::default());
        // The names so far, for lookups in constant time: an include of a
        // types file brings hundreds of each.
        let mut desc_at: HashMap<Sym, TyId> = own_descs.iter().map(|(n, t)| (*n, *t)).collect();
        let mut val_names: HashSet<Sym> = own.iter().map(|(n, _)| *n).collect();
        for (k, (name, t)) in from.iter().enumerate() {
            let (ds, vs, taken) = match self.arena.get(self.arena.resolve(*t)).clone() {
                Ty::Module { abs: a, descs, vals } => {
                    let (mut ds, own_abs) = self.abs_taken(&a, &mut map);
                    let taken: Vec<Sym> = own_abs.iter().map(|(n, _)| *n).collect();
                    for (n, _) in &own_abs {
                        if abs.iter().chain(&fresh).any(|(m, _)| m == n) || desc_at.contains_key(n) {
                            return Err(FxError::at(span, format!("`{}` is defined twice in this module", self.interner.name(*n))));
                        }
                    }
                    fresh.extend(own_abs);
                    ds.extend(descs);
                    (ds, vals, taken)
                }
                _ => return Err(FxError::at(span, format!("`include` includes a module, and this is a {}", self.show_ty(*t)))),
            };
            // A hidden `include`'s (`%hinclude-k`): each name marked hidden,
            // for the module's type to leave out (`hiding`).
            let marks: Vec<(Sym, bool)> = if self.interner.name(*name).starts_with("%hinclude-") {
                taken.into_iter().chain(ds.iter().map(|(n, _)| *n)).map(|n| (n, false)).chain(vs.iter().map(|(n, _)| (*n, true))).collect()
            } else {
                Vec::new()
            };
            for d in ds {
                // A type or effect name given twice is one name if it
                // describes the same both times (re-exported, as a types
                // file gives on another's): `TODO.md` §69, the import pass.
                let prior = desc_at.get(&d.0).copied();
                let same = prior.is_some_and(|t| self.arena.resolve(t) == self.arena.resolve(d.1) || (self.subtype(t, d.1) && self.subtype(d.1, t)));
                let twice = (prior.is_some() && !same) || abs.iter().chain(&fresh).any(|(n, _)| *n == d.0);
                if !self.interner.name(d.0).starts_with("%hidden") && twice {
                    return Err(FxError::at(span, format!("`{}` is defined twice in this module", self.interner.name(d.0))));
                }
                if !same {
                    desc_at.entry(d.0).or_insert(d.1);
                    descs.push(d);
                }
            }
            for (j, v) in vs.into_iter().enumerate() {
                if !val_names.insert(v.0) {
                    return Err(FxError::at(span, format!("`{}` is defined twice in this module", self.interner.name(v.0))));
                }
                out.push(v);
                path.push(Pick::Path(at.unwrap_or(k), j));
            }
            for (n, value) in marks {
                let name = self.interner.intern(&format!("{}{}", if value { "%hiddenv:" } else { "%hidden:" }, self.interner.name(n)));
                desc_at.entry(name).or_insert(self.unit);
                descs.push((name, self.unit));
            }
        }
        descs.append(&mut own_descs);
        // The module's own values after the included, by position, past
        // `%include`'s.
        if let Some(k) = at {
            for (i, v) in own.iter().enumerate() {
                out.push(*v);
                path.push(Pick::Value(if i < k { i } else { i + 1 }));
            }
        }
        self.facts.reshaped.insert(e, path);
        self.note_packs(e, &map);
        let (descs, vals) = if map.is_empty() {
            (descs, out)
        } else {
            (descs.iter().map(|(d, x)| (*d, self.subst(*x, &map))).collect(), out.iter().map(|(x, y)| (*x, self.subst(*y, &map))).collect())
        };
        fresh.extend(abs);
        Ok(self.arena.ty(Ty::Module { abs: fresh, descs, vals }))
    }

    /// A module's abstract types `abs`, taken into another (`include`,
    /// `extend`; `TODO.md` §69): a bound module's (`name_module`'s `m..t`)
    /// as descriptions, aliases, so that its values and `m`'s stay one
    /// another's; any other's, a module made where it is taken, the new
    /// module's own, each a fresh variable (`map` from the old), as the
    /// module's own `define-generative`s are: two calls of one functor
    /// share a type, and their types are not one another's.
    pub(crate) fn abs_taken(&mut self, abs: &[(Sym, DVar)], map: &mut HashMap<DVar, D>) -> (Vec<(Sym, TyId)>, Vec<(Sym, DVar)>) {
        let (mut aliases, mut own) = (Vec::new(), Vec::new());
        for (a, v) in abs {
            if self.is_module_var(*v) {
                aliases.push((*a, self.arena.ty(Ty::Var(*v))));
                continue;
            }
            let kind = self.arena.dvar_kind(*v);
            let w = self.arena.dvar_of(*a, kind);
            let d = match kind {
                Kind::Type => D::Type(self.arena.ty(Ty::Var(w))),
                _ => {
                    self.abstract_funs.insert(w);
                    D::Fun(self.arena.ty(Ty::Var(w)))
                }
            };
            map.insert(*v, d);
            own.push((*a, w));
        }
        (aliases, own)
    }

    /// With `record_types`: module `e`'s abstract types taken in from
    /// others (`abs_taken`'s `map`, each module's own to a fresh one), each
    /// fresh one packed with the module's own as its witness
    /// (`NodeFacts::packs`).
    fn note_packs(&mut self, e: ExpId, map: &HashMap<DVar, D>) {
        if !self.record_types {
            return;
        }
        let pairs: Vec<(DVar, DVar)> = map
            .iter()
            .filter_map(|(v, d)| match d {
                D::Type(w) | D::Fun(w) => match self.arena.get(self.arena.resolve(*w)) {
                    Ty::Var(w) => Some((*w, *v)),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        let packs: Vec<(DVar, TyId)> = pairs.into_iter().map(|(w, v)| (w, self.arena.ty(Ty::Var(v)))).collect();
        self.facts.packs.entry(e).or_default().extend(packs);
    }

    /// Whether a module is an `(extend e0 e1)`, as the parser makes one.
    fn is_extend(&self, items: &[ModItem]) -> bool {
        matches!(items, [ModItem::Val { name: a, .. }, ModItem::Val { name: b, .. }]
                 if self.interner.name(*a) == "%extend-0" && self.interner.name(*b) == "%extend-1")
    }

    /// `(extend e0 e1)`, its values `vals` the two modules: one of the values
    /// of both, `e1`'s where both have a name, `e0`'s in its order first and
    /// then `e1`'s others; its types likewise. Made of theirs, by path
    /// (`Pick::Path`). A bound module's abstract types (`m..t`) are its
    /// descriptions, aliases; any other's the new module's own, fresh
    /// (`abs_taken`; FX-91's, for `e1`'s), and one of `e0`'s that `e1`
    /// replaces is refused if what is kept mentions it (`TODO.md` §69). As
    /// the FX-26 checker's `k-extended`.
    fn extended(&mut self, e: ExpId, span: Span, vals: &[(Sym, TyId)]) -> R<TyId> {
        let mut sides = Vec::new();
        let mut map = HashMap::default();
        for (i, (_, t)) in vals.iter().enumerate() {
            match self.arena.get(self.arena.resolve(*t)).clone() {
                Ty::Module { abs, descs, vals } => {
                    let (mut ds, own) = self.abs_taken(&abs, &mut map);
                    ds.extend(descs);
                    sides.push((own, ds, vals));
                }
                _ => {
                    let which = if i == 0 { "first" } else { "second" };
                    return Err(FxError::at(span, format!("`extend` extends a module by a module, and its {which} is a {}", self.show_ty(*t))));
                }
            }
        }
        let (a1, d1, v1) = sides.pop().expect("two");
        let (a0, d0, v0) = sides.pop().expect("two");
        // `e1`'s names, abstract or not, replace `e0`'s.
        let in1 = |n: &Sym| a1.iter().any(|(m, _)| m == n) || d1.iter().any(|(m, _)| m == n);
        let (kept, gone): (Vec<(Sym, DVar)>, Vec<(Sym, DVar)>) = a0.into_iter().partition(|(n, _)| !in1(n));
        let d0: Vec<(Sym, TyId)> = d0.into_iter().filter(|(n, _)| !a1.iter().any(|(m, _)| m == n)).collect();
        let mut descs: Vec<(Sym, TyId)> = d0.iter().map(|(n, t)| *d1.iter().find(|(m, _)| m == n).unwrap_or(&(*n, *t))).collect();
        descs.extend(d1.iter().filter(|(n, _)| !d0.iter().any(|(m, _)| m == n)).copied());
        let (mut out, mut at) = (Vec::new(), Vec::new());
        for (j, (n, t)) in v0.iter().enumerate() {
            match v1.iter().position(|(m, _)| m == n) {
                Some(k) => {
                    out.push(v1[k]);
                    at.push(Pick::Path(1, k));
                }
                None => {
                    out.push((*n, *t));
                    at.push(Pick::Path(0, j));
                }
            }
        }
        for (k, (n, t)) in v1.iter().enumerate() {
            if !v0.iter().any(|(m, _)| m == n) {
                out.push((*n, *t));
                at.push(Pick::Path(1, k));
            }
        }
        self.facts.reshaped.insert(e, at);
        self.note_packs(e, &map);
        let descs: Vec<(Sym, TyId)> = descs.iter().map(|(d, x)| (*d, self.subst(*x, &map))).collect();
        let out: Vec<(Sym, TyId)> = out.iter().map(|(x, y)| (*x, self.subst(*y, &map))).collect();
        for (n, t) in out.iter().chain(&descs) {
            if let Some((h, _)) = gone.iter().find(|(_, v)| self.mentions_var(*t, *v)) {
                let h = self.interner.name(*h);
                return Err(FxError::at(span, format!("`{}`'s type mentions the first module's `{h}`, which the second's `{h}` replaces", self.interner.name(*n))));
            }
        }
        let abs = kept.into_iter().chain(a1).collect();
        Ok(self.arena.ty(Ty::Module { abs, descs, vals: out }))
    }

    /// Item `name`'s type, its value `init` synthesized at `t`, and as it is
    /// bound in the module: a path to a module, `(with m x)`, keeping the
    /// path's types, as a `let` of one does (`module_path_type`), so that an
    /// `include` of `env::m-base` gives `env.m-base..t`, which a parameter's
    /// type gives on (`params_paths_back`); else, a variable's too, whose
    /// types are its binding's already, as `name_nat` names it.
    fn item_bound(&mut self, name: Sym, init: ExpId, t: TyId) -> (TyId, TyId) {
        if matches!(self.arena.exp_at(init), crate::ast::Exp::Var(_)) {
            return (t, self.name_nat(name, t));
        }
        match self.module_path_type(init) {
            Some((k, at)) => {
                let k = self.kept_here(k, at);
                (k, k)
            }
            None => (t, self.name_nat(name, t)),
        }
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
        if let Some(init) = items.iter().find_map(|it| match it {
            ModItem::Val { ty: Some(t), init, .. } if self.arrow_star_tys.contains(t) && !self.is_lambda(*init) => Some(*init),
            _ => None,
        }) {
            return Err(FxError::at(self.arena.span_of(init), "`->*` finds a procedure's effect from its `lambda`: define it as one"));
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
            let (t, bound) = self.item_bound(name, init, t);
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
        let marked: Vec<bool> = lambdas.iter().map(|l| self.arrow_star_tys.contains(&l.1)).collect();
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
        // A `define*` named by an item that is not a typed lambda, checked
        // now, as a value made as the module is: at its type as written,
        // and refused below if found to read more (Heist's, 2026-10-28).
        let mut valued = fixpt_hash::HashSet::default();
        for (i, item) in items.iter().enumerate() {
            if let ModItem::Val { init, .. } = item
                && !lambdas.iter().any(|l| l.3 == i)
            {
                valued.extend(self.free_vars(*init));
            }
        }
        for (k, l) in lambdas.iter().enumerate() {
            if star(l.3) && valued.contains(&l.0) {
                self.env.set_ty(base + k, declared[k]);
            }
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
                    let identity = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: Effect::pure(), params: vec![rep], result: rep, spec: None });
                    self.check(up_fn, identity)?;
                    self.check(down_fn, identity)?;
                    let up_t = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: Effect::pure(), params: vec![rep], result: t, spec: None });
                    let down_t = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: Effect::pure(), params: vec![t], result: rep, spec: None });
                    let (up_t, down_t) = if binders.is_empty() {
                        (up_t, down_t)
                    } else {
                        (
                            self.arena.ty(Ty::Poly { binders: binders.clone(), body: up_t }),
                            self.arena.ty(Ty::Poly { binders, body: down_t }),
                        )
                    };
                    if self.record_types {
                        for (f, t) in [(up_fn, up_t), (down_fn, down_t)] {
                            if let crate::ast::Exp::Lambda { body, .. } = self.arena.exp_at(f) {
                                self.facts.conversions.insert(*body, t);
                            }
                        }
                    }
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
                    self.run_item_does(name, &ie, init)?;
                    eff = eff.union(&ie);
                    let (t, bound) = if ty.is_none() { self.item_bound(name, init, t) } else { (t, self.name_nat(name, t)) };
                    self.env.push((name, bound));
                    typed.push((i, name, t));
                }
                ModItem::Rec(_) => {}
            }
        }
        // Then, for the lambdas, reading any global until found.
        for (k, l) in lambdas.iter().enumerate() {
            if star(l.3) && valued.contains(&l.0) {
                self.env.set_ty(base + k, l.1);
            }
        }
        let groups = self.module_groups(&lambdas);
        // With `->*`, every such lambda's effect found before any lambda is
        // checked, each recursive group with one noted as `define-rec`'s is
        // (`arrow_star_group`).
        // Whether each group may not end, and why: found once, for its first
        // member (the group being the same for each of its members).
        let mut ends: Vec<Option<Result<(), String>>> = vec![None; lambdas.len()];
        let mut settled = Vec::new();
        if marked.contains(&true) {
            let rdepth = self.recursive.len();
            for k in 0..lambdas.len() {
                if groups[k].first() == Some(&k) && groups[k].iter().any(|m| marked[*m]) {
                    let group: Vec<(Sym, TyId, ExpId)> = groups[k].iter().map(|m| (lambdas[*m].0, lambdas[*m].1, lambdas[*m].2)).collect();
                    ends[k] = Some(self.note_termination(&group));
                }
            }
            let all: Vec<(Sym, TyId, ExpId)> = lambdas.iter().map(|l| (l.0, l.1, l.2)).collect();
            let found = self.arrow_star_group(&all, &marked, base, true);
            self.recursive.truncate(rdepth);
            let (found, s) = found?;
            settled = s;
            for (k, (_, t, _)) in found.into_iter().enumerate() {
                if marked[k] {
                    lambdas[k].1 = t;
                    self.env.set_ty(base + k, t);
                }
            }
        }
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
            let rec = matches!(items[i], ModItem::Rec(_));
            let r = match settled.get(k) {
                Some(Some(lt)) => self.arrow_star_settled(init, *lt, t),
                _ => self.check(init, t),
            };
            let r = if rec { r.map_err(|err| self.declared_error(n, t, init, err)) } else { r };
            self.recursive.truncate(rdepth);
            eff = eff.union(&r?);
            typed.push((i, n, t));
        }
        // Each `define*` another item used as a value, at its type as
        // written: refused if found to read more (`k-valued-stars`).
        for (k, l) in lambdas.iter().enumerate() {
            if star(l.3) && valued.contains(&l.0) {
                self.valued_star(l.0, declared[k], l.1, l.2)?;
            }
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
        self.env.set_ty(base + k, declared);
        let rdepth = self.recursive.len();
        note(self, wide);
        let first_check = self.check_declared(n, wide, init);
        self.recursive.truncate(rdepth);
        first_check?;
        let found = self.with_latent(declared, &self.globals_read_by(init)).expect("a subr");
        self.env.set_ty(base + k, found);
        note(self, found);
        let again = self.check_declared(n, found, init).map_err(|err| {
            let shown = self.show_ty(found);
            err.reworded(err.span, format!("`define*` found `{}` to be a {shown}: {}", self.interner.name(n), err.message))
        });
        self.recursive.truncate(rdepth);
        Ok((found, again?))
    }

    /// `(with m body)`: the body with `m`'s values in scope, by name, at
    /// their types for `m`: those it names, each with its position in `m`
    /// (`Facts::with_vals`), so that a `with` of one of a wide module's
    /// values, as a re-export is, binds one.
    pub(crate) fn synth_with(&mut self, e: ExpId, m: Sym, body: ExpId) -> R<(TyId, Effect)> {
        self.with_as(e, m, body, None)
    }

    /// The top level's binding of `n`, at `i` (`toplevel_pos`): its type,
    /// as a test may have narrowed it, a shared global's strengthened.
    pub(crate) fn toplevel_type(&mut self, n: Sym, i: usize) -> TyId {
        let t = self.narrowed.iter().rev().find(|(x, b, _)| *x == n && *b == i).map_or(self.env[i].1, |(_, _, t)| *t);
        if self.shared_globals.contains(&n) { self.strengthened(t) } else { t }
    }

    /// `(with #%toplevel n)`: the top level's `n`, as it is here, whatever
    /// binds `n` between (`typed-macros.md`, item 5): its type, and what
    /// naming it does, as the plain `n` would there (`naming_effect`).
    fn toplevel_ref(&mut self, e: ExpId, m: Sym, body: ExpId) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        if self.lookup(m).is_some() {
            return Err(FxError::at(span, "`#%toplevel` is the top level's module, which nothing else may be"));
        }
        let crate::ast::Exp::Var(n) = *self.arena.exp_at(body) else {
            return Err(FxError::at(span, "`(with #%toplevel name)` names one name of the top level"));
        };
        let shown = self.interner.name(n).to_string();
        if self.second_class(n) && self.operator_at != Some(e) {
            return Err(self.named_only_to_call(span, n));
        }
        let Some(i) = self.toplevel_pos(n) else {
            return Err(FxError::at(span, format!("`{shown}` is not defined at the top level")));
        };
        if let Some((_, why)) = self.broken.get(&n).filter(|(b, _)| *b == i) {
            return Err(FxError::at(span, format!("`{shown}` is broken, {why}: define it again to use it")));
        }
        let t = self.toplevel_type(n, i);
        let mut eff = Effect::pure();
        if self.recursive.contains(&(n, t)) {
            eff.0.insert(crate::ast::Atom::Spin);
        }
        if self.globals_effects && self.global_slots.contains(&i) {
            eff.0.insert(crate::ast::Atom::Read(crate::ast::Region::Global(n)));
        }
        // As an operator, noted by the application (`synth_app`).
        if self.operator_at != Some(e) {
            self.plain_fx(e);
        }
        Ok((t, eff))
    }

    /// `(the (modnames …) exp)`, its type the slot `slot`: `exp`'s type
    /// sealed to the names (`sealed`), the slot linked to it, and `exp`
    /// held to it as `the` holds a value to its type (a module of more
    /// values made into one of these, `expect`'s reshape).
    #[inline(never)]
    pub(crate) fn the_sealed(&mut self, slot: TyId, exp: crate::ast::ExpId) -> R<(TyId, crate::ast::Effect)> {
        let names = self.arena.withs.sealed[&slot].clone();
        let (got, eff) = self.synth(exp)?;
        let sealed = self.sealed(got, &names, self.arena.span_of(exp))?;
        self.arena.set_link(slot, sealed);
        self.expect(exp, got, sealed)?;
        // Checked against it, as `check` would note it.
        if self.record_types {
            self.facts.types.insert(exp, sealed);
        }
        Ok((sealed, eff))
    }

    /// Module type `got` with the names `names` alone (`binding-shapes.md`,
    /// "leaving names out seals"): each as `got` has it, a value named as
    /// a module itself sealed so; each type's and effect's kind as written
    /// (an abstract type `(abs t)`, a transparent one `(desc u)`, an effect
    /// `(eff e)`: the user's, 2026-11-10); an abstract type left out that
    /// what is kept mentions kept hidden, as `restrict` keeps it.
    fn sealed(&mut self, got: TyId, names: &[crate::ast::ShapeMember], span: Span) -> R<TyId> {
        use crate::ast::ShapeMember as Named;
        let Ty::Module { abs, descs, vals } = self.arena.get(self.arena.resolve(got)).clone() else {
            return Err(FxError::at(span, format!("`modnames` names a module's members, and this is a {}", self.show_ty(got))));
        };
        let mut kept = Vec::new();
        let mut inner = Vec::new();
        for n in names {
            let (name, at) = match n {
                Named::Val(x, at, _) | Named::Abs(x, at) | Named::Desc(x, at) | Named::Eff(x, at) => (*x, *at),
            };
            let shown = self.interner.name(name).to_string();
            let is_abs = abs.iter().any(|(m, _)| *m == name);
            let desc = descs.iter().find(|(m, _)| *m == name).map(|(_, d)| self.desc_effect(*d).is_some());
            let is_val = vals.iter().any(|(m, _)| *m == name);
            let said = |c: &Self, w: &str| FxError::at(at, format!("`{shown}` is {w} of {}: `({} {shown})`", c.show_ty(got), match w {
                "an abstract type" => "abs",
                "a transparent type" => "desc",
                _ => "eff",
            }));
            match (n, is_abs, desc, is_val) {
                (Named::Val(_, _, sub), _, _, true) => {
                    if let Some(sub) = sub {
                        inner.push((name, sub.clone(), at));
                    }
                }
                (Named::Abs(..), true, _, _) | (Named::Desc(..), _, Some(false), _) | (Named::Eff(..), _, Some(true), _) => {}
                (Named::Val(..), false, None, false) | (Named::Abs(..) | Named::Desc(..) | Named::Eff(..), false, None, _) => {
                    // (A value named as a type is no type the module gives.)
                    return Err(FxError::at(at, format!("the module gives no `{shown}`")));
                }
                (_, true, _, _) => return Err(said(self, "an abstract type")),
                (_, _, Some(false), _) => return Err(said(self, "a transparent type")),
                (_, _, Some(true), _) => return Err(said(self, "an effect")),
            }
            kept.push(name);
        }
        let descs: Vec<(Sym, TyId)> = descs.into_iter().filter(|(n, _)| kept.contains(n)).collect();
        let mut out_vals = Vec::new();
        for (n, t) in vals.into_iter().filter(|(n, _)| kept.contains(n)) {
            let t = match inner.iter().find(|(m, _, _)| *m == n) {
                // A module inside, its names as written; not sealed to fewer
                // yet, which would make a new product of it inside the one
                // made of this (no reshape reaches inside a value).
                Some((_, sub, at)) => {
                    let s = self.sealed(t, sub, *at)?;
                    let count = |c: &Self, t: TyId| match c.arena.get(c.arena.resolve(t)) {
                        Ty::Module { abs, descs, vals } => abs.len() + descs.len() + vals.len(),
                        _ => 0,
                    };
                    if count(self, s) != count(self, t) {
                        let shown = self.interner.name(n);
                        return Err(FxError::at(*at, format!("`{shown}` gives more than this names of it: a `modnames` seals a module's own names, not yet those of one inside it; name all of `{shown}`'s here, or seal it where it is defined")));
                    }
                    s
                }
                None => t,
            };
            out_vals.push((n, t));
        }
        let mut out = Vec::new();
        for (n, v) in abs {
            if kept.contains(&n) {
                out.push((n, v));
            } else if descs.iter().chain(&out_vals).any(|(_, t)| self.mentions_var(*t, v)) {
                let hidden = format!("%hidden:{}", self.interner.name(n));
                out.push((self.interner.intern(&hidden), v));
            }
        }
        Ok(self.arena.ty(Ty::Module { abs: out, descs, vals: out_vals }))
    }

    /// `(with m body)`: its body synthesized, or checked against `expected`.
    /// Module type `mt`, of `m`, held to the shape the expander read it as
    /// (`binding-shapes.md`): what it gives, by namespace, exactly the
    /// shape's names, so that what the expander took a `with` or an
    /// `include` to bind is what it binds. A name of the checkers' own
    /// (`%…`) is no name a program reads.
    pub(crate) fn shape_held(&self, span: Span, m: Option<Sym>, mt: TyId, shape: &Option<crate::ast::Relied>, used: &[Sym], past: &[Sym]) -> R<()> {
        let Ty::Module { vals, abs, descs } = self.arena.get(self.arena.resolve(mt)) else { return Ok(()) };
        let shown = match m.map(|m| self.interner.name(m)) {
            Some(m) if !m.starts_with('%') => format!("`{m}`"),
            _ => "this module".to_string(),
        };
        // A module whose names the program does not say before it is
        // checked: what opens it cannot know what it binds.
        let Some(shape) = shape else {
            return Err(FxError::at(span, format!("the names {shown} gives are not known before it is checked: give it a type where it is bound, `(the (moduleof …) e)` or a parameter's")));
        };
        let gives_val = |n: &Sym| vals.iter().any(|(v, _)| v == n);
        let gives_desc = |n: &Sym| abs.iter().any(|(v, _)| v == n) || descs.iter().any(|(v, _)| v == n);
        let names = |ns: Vec<&Sym>| ns.iter().map(|n| format!("`{}`", self.interner.name(**n))).collect::<Vec<_>>().join(", ");
        // What the program took to be the module's, it gives; what it took
        // to be bound outside it, and names here, it does not: a value the
        // body uses that the module gives (`used`), a description read past
        // it (`past`).
        let fewer: Vec<&Sym> = shape.vals.iter().filter(|n| !gives_val(n)).chain(shape.descs.iter().filter(|n| !gives_desc(n))).collect();
        let more: Vec<&Sym> = used.iter().filter(|n| !shape.vals.contains(n)).chain(past.iter().filter(|n| gives_desc(n))).collect();
        let mut said = Vec::new();
        if !more.is_empty() {
            said.push(format!("its type gives {}, which the program took to be bound outside it", names(more)));
        }
        if !fewer.is_empty() {
            said.push(format!("its type has no {}", names(fewer)));
        }
        if said.is_empty() {
            return Ok(());
        }
        Err(FxError::at(span, format!("{shown} gives other names than were read from the program before it was checked: {}", said.join(", and "))))
    }

    pub(crate) fn with_as(&mut self, e: ExpId, m: Sym, body: ExpId, expected: Option<TyId>) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        if self.is_toplevel_module(m) {
            return self.toplevel_ref(e, m, body);
        }
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
        if let Some(t) = self.library_type(m, body) {
            self.note_library_use(e, m, body);
            return Ok((t, Effect::pure()));
        }
        let Some(mt) = self.lookup(m) else {
            return Err(FxError::at(span, format!("`{}` is not bound", self.interner.name(m))));
        };
        let Ty::Module { vals, .. } = self.arena.get(self.arena.resolve(mt)).clone() else {
            let msg = match self.interner.name(m) {
                // `extend`'s `(with %extend-0 e1)` (`parse.rs`).
                "%extend-0" => format!("`extend` extends a module by a module, and its first is a {}", self.show_ty(mt)),
                _ => format!("`with` opens a module, and `{}` is a {}", self.path_shown(m), self.show_ty(mt)),
            };
            return Err(FxError::at(span, msg));
        };
        // A macro used in the body by a name the module gives a value of:
        // the program would seem to call the value, and the expander, which
        // cannot know the module's names, made the macro's use of it.
        if let Some(uses) = self.macros.withs.with_uses.get(&span)
            && let Some((n, at)) = uses.iter().find(|(n, _)| vals.iter().any(|(v, _)| v == n))
        {
            let (n, shown) = (self.interner.name(*n), self.interner.name(m));
            return Err(FxError::at(*at, format!("`{n}` is a macro here, and `{shown}` gives a value of that name, which this `with` would seem to call")));
        }
        // A template's `(with m name)`: a value `m` gives, never what `name`
        // is where the macro is used.
        // A path's, `a::b::c` (`TODO.md` §296), the same: of the module
        // before it alone.
        if let Some(&(n, at, path)) = self.macros.withs.projections.get(&span) {
            let whole = self.interner.name(n).to_string();
            let (module, x) = match whole.rsplit_once("::") {
                Some((module, x)) if path => (module.to_string(), self.interner.intern(x)),
                _ => (self.interner.name(m).to_string(), n),
            };
            if !vals.iter().any(|(v, _)| *v == x) {
                let shown = self.interner.name(x);
                return Err(FxError::at(at, if path {
                    format!("`{module}` gives no value `{shown}`, which the path `{whole}` takes from it alone")
                } else {
                    format!("`{module}` gives no value `{shown}`, which a template's `(with {module} {shown})` takes from it alone")
                }));
            }
        }
        let mut free = self.free_vars(body);
        // An include's names are the module's own, bound where `%include`
        // is: one bound since (the item's lambda's parameter) shadows them
        // (`TODO.md` §69).
        if self.interner.name(m) == "%include"
            && let Some(at) = self.env.rpos(m)
        {
            free.retain(|n| self.env.rpos(*n).is_none_or(|i| i < at));
        }
        let used: Vec<(usize, (Sym, TyId))> = vals.iter().copied().enumerate().filter(|(_, (n, _))| free.contains(n)).collect();
        if let Some(shape) = self.arena.withs.opened.get(&e).cloned() {
            let names: Vec<Sym> = used.iter().map(|(_, (n, _))| *n).collect();
            let past = self.arena.withs.read_past.get(&e).cloned().unwrap_or_default();
            self.shape_held(span, Some(m), mt, &shape, &names, &past)?;
        }
        self.facts.with_vals.insert(e, used.iter().map(|(i, (n, _))| (*n, *i)).collect());
        let vals: Vec<(Sym, TyId)> = used.into_iter().map(|(_, v)| v).collect();
        let naming = self.naming_effect(m, mt);
        // Checked, an error at the body is said of the `with`, so that a
        // call's argument's is the argument's (`as_argument`).
        let at = self.arena.span_of(body);
        let (t, be) = self.in_scope(&vals, |c| match expected {
            Some(x) => Ok((x, c.check(body, x).map_err(|err| if err.span == at { err.reworded(span, err.message.clone()) } else { err })?)),
            None => c.synth(body),
        })?;
        let eff = self.mask(e, &naming.union(&be), t);
        Ok((t, eff))
    }

    /// The type of `(with m body)` as the forms of processes and `par` see
    /// it, if `m` is the hidden global of the scheduler's load
    /// (`check::PROCESSES`) and `body` names one of its procedures: the
    /// standard `%processes:` binding's, not the file's own, in which a task
    /// may do anything. Reading the hidden global is no effect: it never
    /// changes.
    pub(crate) fn library_type(&self, m: Sym, body: ExpId) -> Option<TyId> {
        if self.shared_loads.get(crate::check::PROCESSES) != Some(&m) {
            return None;
        }
        let crate::ast::Exp::Var(n) = *self.arena.exp_at(body) else { return None };
        let name = format!("%processes:{}", self.interner.name(n));
        let s = self.interner.get(&name)?;
        self.standard_type(s)
    }

    /// The member `body` names, noted for the compilers as an ordinary
    /// `with`'s are (`Facts::with_vals`).
    fn note_library_use(&mut self, e: ExpId, m: Sym, body: ExpId) {
        let crate::ast::Exp::Var(n) = *self.arena.exp_at(body) else { return };
        let Some(mt) = self.lookup(m) else { return };
        if let Ty::Module { vals, .. } = self.arena.get(self.arena.resolve(mt)) {
            let used: Vec<(Sym, usize)> = vals.iter().enumerate().filter(|(_, (x, _))| *x == n).map(|(i, (x, _))| (*x, i)).collect();
            self.facts.with_vals.insert(e, used);
        }
    }

    /// A load's module type, `t`, as a load gives it: each abstract type a
    /// description of the hidden global's own, so that every binding of a
    /// load of the file, wherever it is, has the same types. A key is one
    /// value, made once (`TODO.md` §68), so what Sheldon's rule takes of
    /// two textually equal `input`s is true of two loads of a file
    /// (`docs/research/derived-signatures.md`, Q2). A maker's modules are
    /// made by applying it, and keep types of their own.
    pub(crate) fn strengthened(&mut self, t: TyId) -> TyId {
        let Ty::Module { abs, descs, vals } = self.arena.get(self.arena.resolve(t)).clone() else { return t };
        if abs.is_empty() {
            return t;
        }
        let mut shown: Vec<(Sym, TyId)> = abs.iter().map(|(n, v)| (*n, self.arena.ty(Ty::Var(*v)))).collect();
        shown.extend(descs);
        self.arena.ty(Ty::Module { abs: Vec::new(), descs: shown, vals })
    }

    /// A module's type, bound to `name`: its abstract types renamed for this
    /// binding, each `name..t`, kept until the binding's scope ends; and,
    /// if it holds a module that has abstract types, an anchor for the
    /// binding (`module_anchors`), which the names of those a path reaches
    /// are made for when it is read (`component`). Any other type as it
    /// is. The binding is the one about to be made, at `env.len()`, as
    /// each caller makes it.
    pub(crate) fn name_module(&mut self, name: Sym, t: TyId) -> TyId {
        let Ty::Module { abs, descs, vals } = self.arena.get(self.arena.resolve(t)).clone() else { return t };
        // A hidden item's (`%extend-0`, …), the module's own making, keeps
        // the names its module has (`TODO.md` §69); a load's hidden global
        // names them for its file, `x.fx..t`, which every binding of a load
        // of it shares (`strengthened`); a path's, by the path.
        let n = self.interner.name(name);
        let n = match (n.strip_prefix("%shared:"), n.strip_prefix("%with:")) {
            (Some(key), _) => key.rsplit('/').next().unwrap_or(key).trim_start_matches("input:").to_string(),
            (_, Some(path)) => path.to_string(),
            _ => n.to_string(),
        };
        let holds = self.holds_abstract(&vals);
        // A dependent module type's members naming earlier ones' types
        // (`Ty::MemberSel`): a binding of no path its own, as a module's own
        // making keeps the names its module has.
        if n.starts_with('%') && !self.named_members(&vals).is_empty() {
            let vals = self.members_closed(&vals);
            return self.arena.ty(Ty::Module { abs, descs, vals });
        }
        if n.starts_with('%') || (abs.is_empty() && !holds) {
            return t;
        }
        let mut map: HashMap<DVar, D> = HashMap::default();
        let mut fresh = Vec::new();
        for (a, v) in &abs {
            let w = self.module_var(&format!("{n}..{}", self.interner.name(*a)), *v);
            self.skolems.push(w);
            map.insert(*v, self.var_desc(w));
            fresh.push((*a, w));
        }
        let descs = descs.iter().map(|(d, x)| (*d, self.subst(*x, &map))).collect();
        let vals: Vec<(Sym, TyId)> = vals.iter().map(|(x, y)| (*x, self.subst(*y, &map))).collect();
        // Bound as long as the binding, as its own names are.
        let anchor = holds.then(|| {
            let anchor = self.arena.dvar_of(self.interner.intern(&n), Kind::Type);
            self.skolems.push(anchor);
            self.module_vars.insert(anchor);
            anchor
        });
        // Each member a later one names, and what that one says of it, the
        // path's from this binding (`m.base..t`), as `component` reads it:
        // every file given this module agrees on them by path.
        let vals = match anchor {
            Some(anchor) => self.members_closed_by(&vals, &mut |c, x, t| c.path_opened(anchor, &format!("{n}.{}", c.interner.name(x)), &[x], t)),
            None => self.members_closed(&vals),
        };
        let named = self.arena.ty(Ty::Module { abs: fresh, descs, vals });
        if let Some(anchor) = anchor {
            let slot = self.env.len();
            self.module_anchors.insert(named, Anchor { anchor, path: n, slot });
        }
        named
    }

    /// A variable of `v`'s kind, `named`, among the module's abstract
    /// types (`module_vars`).
    fn module_var(&mut self, named: &str, v: DVar) -> DVar {
        let named = self.interner.intern(named);
        let kind = self.arena.dvar_kind(v);
        let w = self.arena.dvar_of(named, kind);
        self.module_vars.insert(w);
        if kind != Kind::Type {
            self.abstract_funs.insert(w);
        }
        w
    }

    /// Variable `w` as a description, a type or a description function.
    fn var_desc(&mut self, w: DVar) -> D {
        let t = self.arena.ty(Ty::Var(w));
        if self.arena.dvar_kind(w) == Kind::Type { D::Type(t) } else { D::Fun(t) }
    }

    /// Whether a value of `vals` is a module that has abstract types, or
    /// holds one that has: each type looked at once, however many paths
    /// lead to it.
    fn holds_abstract(&self, vals: &[(Sym, TyId)]) -> bool {
        let mut seen: HashMap<TyId, bool> = HashMap::default();
        vals.iter().any(|(_, t)| self.abstract_within(*t, &mut seen))
    }

    fn abstract_within(&self, t: TyId, seen: &mut HashMap<TyId, bool>) -> bool {
        let t = self.arena.resolve(t);
        if let Some(b) = seen.get(&t) {
            return *b;
        }
        seen.insert(t, false);
        let b = match self.arena.get(t) {
            Ty::Module { abs, vals, .. } => !abs.is_empty() || vals.iter().any(|(_, x)| self.abstract_within(*x, seen)),
            _ => false,
        };
        seen.insert(t, b);
        b
    }

    /// The variables a path from the binding of `anchor` was read at:
    /// bound as long as it, though made later (`component`).
    pub(crate) fn anchored(&self, named: &[DVar]) -> Vec<DVar> {
        named.iter().filter_map(|v| self.anchored_vars.get(v)).flatten().copied().collect()
    }

    /// What a binding of `e` keeps, if `e` is a path to a module, a
    /// variable bound to one or `(with p x)` of a path `p` (as the parser
    /// makes one, `(let ((%with:p p)) (with %with:p x))` for a longer):
    /// its type with its abstract types the ones the path's base was bound
    /// with (`m..t`, `m.x..t`), transparent, so that the binding names the
    /// same types the path does. None for anything else, which a binding
    /// names for itself (`name_module`). With the anchor its paths read on
    /// from, if any, for the binding made of it (`kept_here`).
    pub(crate) fn module_path_type(&mut self, e: ExpId) -> Option<(TyId, Option<(DVar, String)>)> {
        self.path_reached(e)
    }

    /// The module path `e` reaches, if it is one, and the anchor its paths
    /// read on from, if any.
    fn path_reached(&mut self, e: ExpId) -> Option<(TyId, Option<(DVar, String)>)> {
        match self.arena.exp_at(e).clone() {
            crate::ast::Exp::Var(m) => self.path_base(m),
            crate::ast::Exp::With { module, body } => {
                let crate::ast::Exp::Var(x) = *self.arena.exp_at(body) else { return None };
                let (t, at) = self.path_base(module)?;
                self.component(t, at, x)
            }
            crate::ast::Exp::Let { bindings, body } => {
                let [(p, init)] = bindings[..] else { return None };
                let crate::ast::Exp::With { module, body } = *self.arena.exp_at(body) else { return None };
                let crate::ast::Exp::Var(x) = *self.arena.exp_at(body) else { return None };
                if module != p {
                    return None;
                }
                let (t, at) = self.path_reached(init)?;
                self.component(t, at, x)
            }
            _ => None,
        }
    }

    /// Module type `t`, a path's, `at` its anchor, for the binding about
    /// to be made at `env.len()`: a type of its own, anchored there, so
    /// that a path from that binding reads on as from the path.
    pub(crate) fn kept_here(&mut self, t: TyId, at: Option<(DVar, String)>) -> TyId {
        let Some((anchor, path)) = at else { return t };
        let copy = self.arena.get(self.arena.resolve(t)).clone();
        let s = self.arena.ty(copy);
        let slot = self.env.len();
        self.module_anchors.insert(s, Anchor { anchor, path, slot });
        s
    }

    /// Variable `m`'s module type, as a path starts from it, transparent
    /// (`opened`); and the anchor of its binding, if its binding made it
    /// (`name_module`, `kept_here`) and is in scope: an anchor is the
    /// binding's at its slot only while the binding's scope lasts, and a
    /// value of that type bound otherwise (a `with`'s, a module's item) is
    /// a module of that type, not that binding's.
    fn path_base(&mut self, m: Sym) -> Option<(TyId, Option<(DVar, String)>)> {
        if self.is_toplevel_module(m) || self.is_fx_module(m) {
            return None;
        }
        let t = self.lookup(m)?;
        let slot = self.env.rpos(m);
        let at = self.module_anchors.get(&t).filter(|a| Some(a.slot) == slot && self.skolems.contains(&a.anchor)).map(|a| (a.anchor, a.path.clone()));
        let t = if self.shared_globals.contains(&m) { self.strengthened(t) } else { t };
        matches!(self.arena.get(self.arena.resolve(t)), Ty::Module { .. }).then_some(())?;
        Some((self.opened(t)?, at))
    }

    /// Module type `t` of a binding, its abstract types (each a variable a
    /// binding made, `module_vars`) as descriptions: transparent. None if
    /// one is not such a variable (a module's own, unbound).
    fn opened(&mut self, t: TyId) -> Option<TyId> {
        let Ty::Module { abs, .. } = self.arena.get(self.arena.resolve(t)).clone() else { return None };
        if !abs.iter().all(|(_, v)| self.is_module_var(*v)) {
            return None;
        }
        Some(self.strengthened(t))
    }

    /// Value `x` of a module of type `t`, as a path reaches it, `at` the
    /// anchor of the binding the path is from: a module, its abstract
    /// types, if it has any, variables of their own for this path,
    /// `m.x..t`, made the first time the path is read (`module_paths`) and
    /// bound as long as the binding (`anchored_vars`), transparent. A
    /// module's value is the same module wherever it is reached from one
    /// binding, so its abstract types are too; a value of such a type
    /// reached otherwise keeps them abstract. None if `t` gives no module
    /// `x`, or one whose types no binding named.
    fn component(&mut self, t: TyId, at: Option<(DVar, String)>, x: Sym) -> Option<(TyId, Option<(DVar, String)>)> {
        let Ty::Module { vals, .. } = self.arena.get(self.arena.resolve(t)).clone() else { return None };
        let (_, c) = vals.iter().find(|(n, _)| *n == x)?;
        let Ty::Module { abs, descs, vals } = self.arena.get(self.arena.resolve(*c)).clone() else { return None };
        if abs.is_empty() && !self.holds_abstract(&vals) {
            return Some((*c, None));
        }
        let _ = (descs, vals);
        let (anchor, base) = at?;
        let path = format!("{base}.{}", self.interner.name(x));
        // Its members' names from the binding: the base's, and `x`.
        let mut steps = self.path_steps.get(&(anchor, base)).cloned().unwrap_or_default();
        steps.push(x);
        let (opened, _) = self.path_opened(anchor, &path, &steps, *c);
        Some((opened, Some((anchor, path))))
    }

    /// The module type the path `path` of members from module variable
    /// `v` reaches, as `(with (with v a) b)` reads it (`component`): its
    /// abstract types the path's from `v`'s binding.
    pub(crate) fn member_path_type(&mut self, v: Sym, path: &[Sym]) -> Option<TyId> {
        let (mut t, mut at) = self.path_base(v)?;
        for x in path {
            (t, at) = self.component(t, at, *x)?;
        }
        Some(t)
    }

    /// The module type `select`'s `m` names: a variable's as it is bound,
    /// or a path's (`%path:(with p x)`, `WithTables::paths`), its abstract
    /// types its base's (`module_path_type`), found from the base as bound
    /// here.
    pub(crate) fn module_at(&mut self, m: Sym) -> Option<TyId> {
        if !self.arena.withs.paths.contains_key(&m) {
            return self.lookup(m);
        }
        self.select_path(m).map(|(t, _)| t)
    }

    fn select_path(&mut self, m: Sym) -> Option<(TyId, Option<(DVar, String)>)> {
        match self.arena.withs.paths.get(&m).copied() {
            Some((p, x)) => {
                let (t, at) = self.select_path(p)?;
                self.component(t, at, x)
            }
            None => self.path_base(m),
        }
    }

    /// Why `(select m …)`, shown as `shown`, names nothing: `m` unbound, or
    /// a path that reaches no module whose types a binding named.
    fn unselected(&self, shown: &str, m: Sym) -> String {
        match self.arena.withs.paths.get(&m) {
            Some(_) => format!("{shown}: `{}` is no path to a module from a variable bound to one, a module of each step", self.path_shown(m)),
            None => format!("{shown}: `{}` is not bound here", self.interner.name(m)),
        }
    }

    /// `t` with each `(select m n)` in it replaced by what it is: `m`'s
    /// abstract type `n`, as `m` was bound, or its description `n`.
    pub(crate) fn resolve_selects(&mut self, t: TyId, span: Span) -> R<TyId> {
        let mut found = Vec::new();
        self.selects_in(t, &mut Default::default(), &mut found);
        let effects = self.effect_selects_in(t);
        if found.is_empty() && effects.is_empty() {
            return Ok(t);
        }
        // Each effect selected, what its module says it is.
        let mut given: HashMap<DVar, D> = HashMap::default();
        for (v, (m, n)) in effects {
            given.insert(v, D::Effect(self.effect_selected(v, m, n, span)?));
        }
        let mut sel = HashMap::default();
        for (m, n, node) in found {
            let shown = |c: &Checker| format!("`(select {} {})`", c.path_shown(m), c.interner.name(n));
            // A type name in a module with `include`s that nothing else
            // defines (`include_scope`): said of the name, not of the
            // hidden `%include`.
            let included = self.interner.name(m) == "%include";
            let not_included = |c: &Checker| format!("`{}` is not a type, nor one a module included gives", c.interner.name(n));
            let Some(mt) = self.module_at(m) else {
                if included {
                    return Err(FxError::at(span, not_included(self)));
                }
                return Err(FxError::at(span, self.unselected(&shown(self), m)));
            };
            let Ty::Module { abs, descs, .. } = self.arena.get(self.arena.resolve(mt)).clone() else {
                return Err(FxError::at(span, format!("{}: `{}` is a {}, not a module", shown(self), self.path_shown(m), self.show_ty(mt))));
            };
            let to = match (abs.iter().find(|(a, _)| *a == n), descs.iter().find(|(d, _)| *d == n)) {
                (Some((_, v)), _) => self.arena.ty(Ty::Var(*v)),
                (None, Some((_, d))) => *d,
                // A name read in a `with` body that `m` does not give: what
                // it is outside the `with` (`Parser::with_selected`).
                // Applied, `(f d …)`: the application is what it is outside.
                (None, None) if self.arena.withs.with_applied.contains_key(&node) => {
                    let app = self.arena.withs.with_applied[&node];
                    let Some(outer) = self.arena.withs.with_fallback[&node] else {
                        let shown = self.interner.name(n);
                        return Err(FxError::at(span, format!("`{shown}` is not a description function, nor one a module opened by `with` gives")));
                    };
                    let to = self.resolve_selects(outer, span)?;
                    self.arena.set_link(app, to);
                    continue;
                }
                (None, None) if self.arena.withs.with_fallback.contains_key(&node) => match self.arena.withs.with_fallback[&node] {
                    Some(outer) => self.resolve_selects(outer, span)?,
                    None => return Err(FxError::at(span, format!("`{}` is not a type, nor one a module opened by `with` gives", self.interner.name(n)))),
                },
                (None, None) if included => return Err(FxError::at(span, not_included(self))),
                (None, None) => {
                    return Err(FxError::at(span, format!("{}: `{}` has no type `{}`", shown(self), self.path_shown(m), self.interner.name(n))));
                }
            };
            self.link_global_select(m, node, to);
            sel.insert((m, n), to);
        }
        let outer = std::mem::replace(&mut self.select_map, sel);
        // Only what leads to a `select` is rebuilt; the rest stays itself.
        let keep = self.select_clean(t, &given);
        let outer_keep = self.subst_keep.replace(keep);
        let r = self.subst_memo(t, &given, &mut Default::default());
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
        if self.env.rpos(m).is_some_and(|i| self.global_slots.contains(&i) || self.fixed_slots.contains(&i))
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
    fn select_clean(&self, t: TyId, given: &HashMap<DVar, D>) -> crate::ast::TySet {
        let mut nodes: Vec<TyId> = Vec::new();
        let mut seen: crate::ast::TySet = Default::default();
        let mut stack = vec![self.arena.resolve(t)];
        while let Some(n) = stack.pop() {
            if !seen.insert(n) {
                continue;
            }
            nodes.push(n);
            self.each_ty_kid(n, |k| stack.push(self.arena.resolve(k)));
        }
        let names_given = |e: &Effect| e.0.iter().any(|a| matches!(a, Atom::Var(v) if given.contains_key(v)));
        let mut dirty: crate::ast::TySet = nodes
            .iter()
            .copied()
            .filter(|n| match self.arena.get(*n) {
                Ty::Select(..) | Ty::ParamSel(..) | Ty::MemberSel(..) => true,
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
        if let Some((_, v)) = self.effect_selects.iter().find(|(k, v)| *k == (m, e) && !self.with_effect_fallback.contains_key(v)) {
            return *v;
        }
        let shown = format!("(select {} {})", self.interner.name(m), self.interner.name(e));
        let v = self.arena.dvar_of(self.interner.intern(&shown), Kind::Effect);
        self.effect_selects.push(((m, e), v));
        v
    }

    /// What effect variable `v`, for `(select m e)`, is: `m`'s effect `e`;
    /// for a `with` body's name that `m` does not give, what it is outside
    /// the `with` (`Parser::with_effect_selected`), itself resolved.
    fn effect_selected(&mut self, v: DVar, m: Sym, e: Sym, span: Span) -> R<Effect> {
        let Some(outer) = self.with_effect_fallback.get(&v).cloned() else {
            return self.selected_effect(m, e, span);
        };
        let given = self.module_at(m).and_then(|mt| match self.arena.get(self.arena.resolve(mt)).clone() {
            Ty::Module { descs, .. } => descs.iter().find(|(d, _)| *d == e).and_then(|(_, d)| self.desc_effect(*d)),
            _ => None,
        });
        match (given, outer) {
            (Some(x), _) => Ok(x),
            (None, Some(outer)) => {
                let mut out = Effect::pure();
                for a in outer.0 {
                    let w = match a {
                        Atom::Var(w) => self.effect_selects.iter().find(|(_, x)| *x == w).map(|(k, _)| (w, *k)),
                        _ => None,
                    };
                    out = match w {
                        Some((w, (m, n))) => out.union(&self.effect_selected(w, m, n, span)?),
                        None => out.union(&Effect::atom(a)),
                    };
                }
                Ok(out)
            }
            (None, None) => Err(FxError::at(span, format!("`{}` is not an effect, nor one a module opened by `with` gives", self.interner.name(e)))),
        }
    }

    /// Module `m`'s effect `e`, as its type says, `m` bound here; or an
    /// error at `span`.
    pub(crate) fn selected_effect(&mut self, m: Sym, e: Sym, span: Span) -> R<Effect> {
        let shown = |c: &Checker| format!("`(select {} {})`", c.path_shown(m), c.interner.name(e));
        // An effect name in a module with `include`s that nothing else
        // defines (`include_scope`): said of the name.
        let not_included = |c: &Checker| format!("`{}` is not an effect, nor one a module included gives", c.interner.name(e));
        let included = self.interner.name(m) == "%include";
        let Some(mt) = self.module_at(m) else {
            if included {
                return Err(FxError::at(span, not_included(self)));
            }
            return Err(FxError::at(span, self.unselected(&shown(self), m)));
        };
        let Ty::Module { descs, .. } = self.arena.get(self.arena.resolve(mt)).clone() else {
            return Err(FxError::at(span, format!("{}: `{}` is a {}, not a module", shown(self), self.path_shown(m), self.show_ty(mt))));
        };
        match descs.iter().find(|(d, _)| *d == e).and_then(|(_, d)| self.desc_effect(*d)) {
            Some(x) => Ok(x),
            None if included => Err(FxError::at(span, not_included(self))),
            None => Err(FxError::at(span, format!("{}: `{}` has no effect `{}`", shown(self), self.path_shown(m), self.interner.name(e)))),
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
        let mut seen = HashSet::default();
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
            self.each_ty_kid(t, |k| stack.push(k));
        }
        out
    }

    /// Each description function applied in `t` given what it takes:
    /// checked where a `select` has just said what the function is.
    pub(crate) fn check_apps(&mut self, t: TyId, span: Span) -> R<()> {
        let mut stack = vec![t];
        let mut seen = HashSet::default();
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
            self.each_ty_kid(t, |k| stack.push(k));
        }
        Ok(())
    }

    /// The same, where `params` are about to be bound and so may not be
    /// selected from: a parameter's type naming another is a dependent
    /// type, which waits for M5.
    pub(crate) fn resolve_selects_outside(&mut self, t: TyId, params: &[Sym], span: Span) -> R<TyId> {
        let mut found = Vec::new();
        self.selects_in(t, &mut Default::default(), &mut found);
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

    pub(crate) fn selects_in(&self, t: TyId, seen: &mut crate::ast::TySet, out: &mut Vec<(Sym, Sym, TyId)>) {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return;
        }
        if let Ty::Select(m, n) = self.arena.get(t) {
            out.push((*m, *n, t));
            return;
        }
        self.each_ty_kid(t, |k| self.selects_in(k, seen, out));
    }

    /// Whether type variable `v` is somewhere in `t`.
    pub(crate) fn mentions_var(&self, t: TyId, v: DVar) -> bool {
        let mut stack = vec![t];
        let mut seen = HashSet::default();
        while let Some(t) = stack.pop() {
            let t = self.arena.resolve(t);
            if !seen.insert(t) {
                continue;
            }
            if matches!(self.arena.get(t), Ty::Var(w) if *w == v) {
                return true;
            }
            self.each_ty_kid(t, |k| stack.push(k));
        }
        false
    }

    /// The types `t` is made of, one level down.
    pub(crate) fn ty_kids(&self, t: TyId) -> Vec<TyId> {
        let mut out = Vec::new();
        self.each_ty_kid(t, |k| out.push(k));
        out
    }

    /// `f` of each of the types `t` is made of, one level down, in
    /// `ty_kids`'s order: no vector made (`TODO.md` §126: `ty_kids`'
    /// vectors were the commonest of the checker's allocations loading
    /// kayak's compiler).
    pub(crate) fn each_ty_kid(&self, t: TyId, mut f: impl FnMut(TyId)) {
        let arg = |d: &D| if let D::Type(x) | D::Fun(x) = d { Some(*x) } else { None };
        match self.arena.get(self.arena.resolve(t)) {
            Ty::Base(_) | Ty::Void | Ty::Nil | Ty::False | Ty::Var(_) | Ty::Nat(_) | Ty::Place(_) | Ty::Select(..) | Ty::ParamSel(..) | Ty::MemberSel(..) | Ty::Link(_) => {}
            Ty::Union(ms) | Ty::AllOf(ms) | Ty::Bloblet { fields: ms, .. } => ms.iter().copied().for_each(f),
            Ty::Subr { params, result, .. } => params.iter().copied().chain([*result]).for_each(f),
            Ty::Poly { body, .. } => f(*body),
            Ty::Ref(a, _) | Ty::Array(a, _, _) | Ty::ICell(a, _) | Ty::MarkKey(a, _) => f(*a),
            Ty::Pair(a, b, _, _) => [*a, *b].into_iter().for_each(f),
            Ty::PromptTag { answer, payload, .. } => [*answer, *payload].into_iter().for_each(f),
            Ty::Composable { arg, answer, .. } => [*arg, *answer].into_iter().for_each(f),
            Ty::Product(ps) | Ty::Sum(ps) => ps.iter().map(|(_, x)| *x).for_each(f),
            Ty::Named { args, .. } => args.iter().filter_map(arg).for_each(f),
            Ty::App { fun, args } => [*fun].into_iter().chain(args.iter().filter_map(arg)).for_each(f),
            Ty::Lam { body: D::Type(x) | D::Fun(x), .. } => f(*x),
            Ty::Lam { .. } => {}
            Ty::NList { elem, .. } => f(*elem),
            Ty::Module { descs, vals, .. } => descs.iter().chain(vals).map(|(_, x)| *x).for_each(f),
        }
    }

    /// A module of type `got` made one of type `want`, which has fewer of
    /// its values or the same in another order: each of `want`'s values'
    /// position in `got`, if `got`'s values so chosen fit `want`.
    pub(crate) fn reshape(&mut self, got: TyId, want: TyId) -> Option<(Vec<usize>, TyId)> {
        let (Ty::Module { abs, descs, vals }, Ty::Module { vals: wanted, .. }) =
            (self.arena.get(self.arena.resolve(got)).clone(), self.arena.get(self.arena.resolve(want)).clone())
        else {
            return None;
        };
        let at: Vec<usize> = wanted.iter().map(|(n, _)| vals.iter().position(|(m, _)| self.val_fits_name(*m, *n))).collect::<Option<_>>()?;
        if at.len() == vals.len() && at.iter().enumerate().all(|(i, k)| i == *k) {
            return None;
        }
        // Its members' types naming earlier ones' closed first, so that the
        // values chosen name none left behind or moved.
        let vals = self.members_closed(&vals);
        let chosen: Vec<(Sym, TyId)> = at.iter().map(|k| vals[*k]).collect();
        let (abs, descs) = self.left_members_types(abs, descs, &vals, &at, &chosen);
        let t = self.arena.ty(Ty::Module { abs, descs, vals: chosen });
        self.subtype(t, want).then_some((at, t))
    }

    /// The types of a module type `abs` and `descs`, its values `vals`
    /// made `chosen` (those at `at`), with those of each member left out
    /// that one chosen names (a dependent module type's, closed): by their
    /// own names, an abstract one's abstract, a path's that path, so that
    /// the type wanted may say them abstractly, `(moduleof (abs t type) (val
    /// user …t…))`, as it may a module's own (M4). A name the module's own
    /// types have, or two members left out give, is no one's: what it names
    /// is not known (`docs/research/dependent-moduleof.md`, §4.5).
    fn left_members_types(&mut self, mut abs: Vec<(Sym, DVar)>, mut descs: Vec<(Sym, TyId)>, vals: &[(Sym, TyId)], at: &[usize], chosen: &[(Sym, TyId)]) -> (Vec<(Sym, DVar)>, Vec<(Sym, TyId)>) {
        let named = |c: &Self, v: DVar| chosen.iter().any(|(_, t)| c.mentions_var(*t, v));
        // Each, and whether abstract.
        let mut given: Vec<(Sym, DVar, bool)> = Vec::new();
        for (k, (_, t)) in vals.iter().enumerate() {
            if at.contains(&k) {
                continue;
            }
            let Ty::Module { abs: ma, descs: md, .. } = self.arena.get(self.arena.resolve(*t)).clone() else { continue };
            for (n, v) in ma {
                if named(self, v) {
                    given.push((n, v, true));
                }
            }
            for (n, d) in md {
                if let Ty::Var(w) = self.arena.get(self.arena.resolve(d)).clone()
                    && named(self, w)
                {
                    given.push((n, w, false));
                }
            }
        }
        let own = |n: Sym| abs.iter().any(|(m, _)| *m == n) || descs.iter().any(|(m, _)| *m == n);
        let once: Vec<(Sym, DVar, bool)> = given.iter().filter(|(n, _, _)| !own(*n) && given.iter().filter(|(m, _, _)| m == n).count() == 1).copied().collect();
        for (n, v, abstract_) in once {
            if abstract_ {
                abs.push((n, v));
            } else {
                descs.push((n, self.arena.ty(Ty::Var(v))));
            }
        }
        (abs, descs)
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

    /// Of a dependent procedure's module parameters, each `k`th's binding's
    /// `anchor` (`anchors`), the abstract types of each path from it read
    /// so far, `env.m-base..t`, onto `back` as the procedure's type says
    /// them, `(select (with $k m-base) t)` (`Ty::ParamSel`), and onto
    /// `given` as the body has them: so a parameter of a dependent module
    /// type, whose abstract types are its members', gives them as one whose
    /// own they are does.
    pub(crate) fn params_paths_back(&mut self, anchors: &[(usize, DVar)], given: &mut HashMap<crate::check::ParamKey, TyId>, back: &mut HashMap<DVar, D>) {
        for (k, anchor) in anchors {
            for w in self.anchored_vars.get(anchor).cloned().unwrap_or_default() {
                if back.contains_key(&w) {
                    continue;
                }
                let Some((path, a)) = self.path_members.get(&w).cloned() else { continue };
                given.insert((*k, path.clone(), a), self.arena.ty(Ty::Var(w)));
                back.insert(w, self.var_desc_of(*k, path, a, w));
            }
        }
    }

    /// `(select (with $k path…) a)`, a description of `w`'s kind.
    fn var_desc_of(&mut self, k: usize, path: Vec<Sym>, a: Sym, w: DVar) -> D {
        let t = self.arena.ty(Ty::ParamSel(k, path, a));
        if self.arena.dvar_kind(w) == Kind::Type { D::Type(t) } else { D::Fun(t) }
    }

    /// `t` with each `(select $k x)` what `map` says it is.
    pub(crate) fn instantiate_params(&mut self, t: TyId, map: &HashMap<crate::check::ParamKey, TyId>) -> TyId {
        if map.is_empty() {
            return t;
        }
        let outer = std::mem::replace(&mut self.param_map, map.clone());
        let r = self.subst(t, &HashMap::default());
        self.param_map = outer;
        r
    }

    /// `t` with each `(select x n)` of a `moduleof`'s earlier member what
    /// `map` says it is (`Ty::MemberSel`).
    pub(crate) fn instantiate_members(&mut self, t: TyId, map: &HashMap<(usize, Sym), TyId>) -> TyId {
        if map.is_empty() {
            return t;
        }
        let outer = std::mem::replace(&mut self.member_map, map.clone());
        let r = self.subst(t, &HashMap::default());
        self.member_map = outer;
        r
    }

    /// Each earlier member's type `(k, n)` that `t` names (`Ty::MemberSel`).
    pub(crate) fn member_sels(&self, t: TyId, seen: &mut crate::ast::TySet, out: &mut Vec<(usize, Sym)>) {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return;
        }
        if let Ty::MemberSel(k, _, n) = self.arena.get(t) {
            if !out.contains(&(*k, *n)) {
                out.push((*k, *n));
            }
            return;
        }
        self.each_ty_kid(t, |k| self.member_sels(k, seen, out));
    }

    /// Whether a member of `vals` names an earlier one's types.
    pub(crate) fn dependent_vals(&self, vals: &[(Sym, TyId)]) -> bool {
        !self.named_members(vals).is_empty()
    }

    /// The members of `vals` that a later one's type names, by number: a
    /// dependent module type's (`docs/research/dependent-moduleof.md`).
    fn named_members(&self, vals: &[(Sym, TyId)]) -> Vec<usize> {
        let mut found = Vec::new();
        let mut seen = crate::ast::TySet::default();
        for (_, t) in vals {
            self.member_sels(*t, &mut seen, &mut found);
        }
        let mut ks: Vec<usize> = found.into_iter().map(|(k, _)| k).collect();
        ks.sort_unstable();
        ks.dedup();
        ks
    }

    /// Values `vals` of a module type, each member's type naming an earlier
    /// member's closed (`Ty::MemberSel`), in order: member `k`'s, once its
    /// own type is closed, as `open` makes it (its type, and its types by
    /// name). A member named so is `open`'s too, so that what a later one
    /// says of it and what it says of itself are the same types.
    fn members_closed_by(&mut self, vals: &[(Sym, TyId)], open: &mut dyn FnMut(&mut Self, Sym, TyId) -> (TyId, Vec<(Sym, TyId)>)) -> Vec<(Sym, TyId)> {
        let named = self.named_members(vals);
        let mut map: HashMap<(usize, Sym), TyId> = HashMap::default();
        let mut out = Vec::with_capacity(vals.len());
        for (k, (x, t)) in vals.iter().enumerate() {
            let t = self.instantiate_members(*t, &map);
            let t = if named.contains(&k) {
                let (opened, types) = open(self, *x, t);
                for (n, y) in types {
                    map.insert((k, n), y);
                }
                opened
            } else {
                t
            };
            out.push((*x, t));
        }
        out
    }

    /// [`members_closed_by`](Self::members_closed_by) each member's own
    /// types: a written dependent type taken apart where no binding names
    /// it (a comparison's left side, a module's own making).
    pub(crate) fn members_closed(&mut self, vals: &[(Sym, TyId)]) -> Vec<(Sym, TyId)> {
        if self.named_members(vals).is_empty() {
            return vals.to_vec();
        }
        self.members_closed_by(vals, &mut |c, _, t| (t, c.module_types(t)))
    }

    /// `vals` closed by the members of `by`, by number: in a comparison of
    /// `by`'s module type with `vals`'s, a later member's type read with the
    /// earlier members `by`'s (a dependent product's depth). `by` closed.
    pub(crate) fn members_closed_as(&mut self, vals: &[(Sym, TyId)], by: &[(Sym, TyId)]) -> Vec<(Sym, TyId)> {
        let named = self.named_members(vals);
        if named.is_empty() {
            return vals.to_vec();
        }
        let mut map: HashMap<(usize, Sym), TyId> = HashMap::default();
        for k in named {
            if let Some((_, t)) = by.get(k) {
                for (n, y) in self.module_types(*t) {
                    map.insert((k, n), y);
                }
            }
        }
        vals.iter().map(|(x, t)| (*x, self.instantiate_members(*t, &map))).collect()
    }

    /// The variables of path `path` from the binding of `anchor`, for a
    /// module of abstract types `abs`: made the first time it is read, and
    /// bound as long as the binding (`module_paths`, `anchored_vars`).
    /// Its members' names from the binding, `steps`, noted, and each
    /// variable's (`path_members`).
    fn path_made(&mut self, anchor: DVar, path: &str, steps: &[Sym], abs: &[(Sym, DVar)]) -> Vec<DVar> {
        if let Some(ws) = self.module_paths.get(&(anchor, path.to_string())) {
            return ws.clone();
        }
        let ws: Vec<DVar> = abs.iter().map(|(a, v)| self.module_var(&format!("{path}..{}", self.interner.name(*a)), *v)).collect();
        self.path_steps.insert((anchor, path.to_string()), steps.to_vec());
        for ((a, _), w) in abs.iter().zip(&ws) {
            self.path_members.insert(*w, (steps.to_vec(), *a));
        }
        self.anchored_vars.entry(anchor).or_default().extend(ws.iter().copied());
        self.module_paths.insert((anchor, path.to_string()), ws.clone());
        ws
    }

    /// Module type `t`, of the value path `path` reaches from the binding of
    /// `anchor`, its abstract types that path's (`path_made`), transparent:
    /// as [`component`](Self::component) gives it, and its types by name.
    fn path_opened(&mut self, anchor: DVar, path: &str, steps: &[Sym], t: TyId) -> (TyId, Vec<(Sym, TyId)>) {
        let Ty::Module { abs, descs, vals } = self.arena.get(self.arena.resolve(t)).clone() else { return (t, Vec::new()) };
        let made = self.path_made(anchor, path, steps, &abs);
        let mut map: HashMap<DVar, D> = HashMap::default();
        let mut shown = Vec::new();
        for ((a, v), w) in abs.iter().zip(&made) {
            map.insert(*v, self.var_desc(*w));
            shown.push((*a, self.arena.ty(Ty::Var(*w))));
        }
        shown.extend(descs.iter().map(|(d, y)| (*d, self.subst(*y, &map))));
        let vals: Vec<(Sym, TyId)> = vals.iter().map(|(y, z)| (*y, self.subst(*z, &map))).collect();
        let vals = self.members_closed_by(&vals, &mut |c, x, t| {
            let mut deeper = steps.to_vec();
            deeper.push(x);
            c.path_opened(anchor, &format!("{path}.{}", c.interner.name(x)), &deeper, t)
        });
        let opened = self.arena.ty(Ty::Module { abs: Vec::new(), descs: shown.clone(), vals });
        (opened, shown)
    }

    pub(crate) fn param_sels(&self, t: TyId, seen: &mut crate::ast::TySet, out: &mut Vec<crate::check::ParamKey>) {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return;
        }
        if let Ty::ParamSel(k, p, n) = self.arena.get(t) {
            let key = (*k, p.clone(), *n);
            if !out.contains(&key) {
                out.push(key);
            }
            return;
        }
        self.each_ty_kid(t, |k| self.param_sels(k, seen, out));
    }

    /// A dependent procedure's parameter and result types for a call with
    /// `args`: each `(select $k x)` the type `x` of the module the `k`th
    /// argument names. That argument must be a module's name, which gives
    /// its types their identity.
    pub(crate) fn dependent_args(&mut self, params: &[TyId], result: TyId, args: &[ExpId], span: Span) -> R<(Vec<TyId>, TyId)> {
        let mut found = Vec::new();
        let mut seen = crate::ast::TySet::default();
        for t in params.iter().chain([&result]) {
            self.param_sels(*t, &mut seen, &mut found);
        }
        if found.is_empty() {
            return Ok((params.to_vec(), result));
        }
        let mut map = HashMap::default();
        for (k, path, x) in found {
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
            // A member's, `(select (with $k m …) t)`: the module the path
            // from the argument reaches, as `(with v m)` reads it, its
            // abstract types the path's from `v`'s binding.
            let mt = if path.is_empty() { Some(mt) } else { self.member_path_type(v, &path) };
            let shown = self.with_path(self.interner.name(v), &path);
            let Some((_, t)) = mt.and_then(|mt| self.module_types(mt).into_iter().find(|(n, _)| *n == x)) else {
                return Err(FxError::at(span, format!("`{shown}` has no type `{}`", self.interner.name(x))));
            };
            map.insert((k, path, x), t);
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

impl Checker {
    /// An expression among a module's items (`%run-N`, `parse_module_items`)
    /// is run for what it does as the module is made: refused if its effect
    /// `e` only reads, so that it does nothing (`k-run-does`).
    fn run_item_does(&self, name: Sym, e: &Effect, init: ExpId) -> R<()> {
        if self.interner.name(name).starts_with("%run-") && e.0.iter().all(|a| matches!(a, Atom::Read(_))) {
            return Err(FxError::at(
                self.arena.span_of(init),
                "an expression among a module's items is run for what it does as the module is made, and this one only reads: name its value with `define`",
            ));
        }
        Ok(())
    }
}

impl Checker {
    /// `define*` `n`, used as a value by another of its module's items at
    /// its type as written, `declared`: refused if found, `found`, to read
    /// a global that type does not say.
    fn valued_star(&self, n: Sym, declared: TyId, found: TyId, init: ExpId) -> R<()> {
        let latent = |t: TyId| match self.arena.get(self.arena.resolve(t)) {
            Ty::Subr { effect, .. } => effect.clone(),
            _ => Effect::pure(),
        };
        let said = latent(declared);
        let more = Effect(latent(found).0.into_iter().filter(|a| !Effect::atom(*a).within(&said)).collect());
        if more.is_pure() {
            return Ok(());
        }
        Err(FxError::at(
            self.arena.span_of(init),
            format!(
                "`define*` `{}` is a value another item uses as the module is made, at its type as written, and it reads {}: write that in its type",
                self.interner.name(n),
                self.show_effect(&more)
            ),
        ))
    }
}
