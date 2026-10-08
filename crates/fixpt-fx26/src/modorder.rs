//! A module's definitions see each other, as `letrec*`'s (`TODO.md` §37):
//! every name a module defines is in scope in all of it, and its items are
//! made in the order written. A typed lambda's value (a definition's, or a
//! `define-rec` member's) may name any item, earlier or later: it does not
//! run when it is made. Every other item's value runs then, so it may reach
//! only items made before it: those it names, and those named by the
//! lambdas it reaches, followed through them. A module breaking that is
//! refused (`module_hazards`), naming the chain; nothing is reordered.
//! What a value names is its free variables (`free_vars`; a `with` inside
//! not checked yet binds none, unless its module is an earlier item whose
//! value is a module as written, `written_modules`, so that `(define x
//! (with m x))` re-exports `m`'s `x`), followed in the order of the items
//! they name. The FX-26 checker's `k-mod-hazards` (`check-modorder.fx`) is this,
//! step for step.

use crate::ast::{ExpId, ModItem, TyId};
use crate::check::Checker;
use crate::error::{FxError, R};
use fixpt_read::Sym;

/// A module's typed lambdas: name, written type, value, and the item it
/// is written in.
pub(crate) type Lambdas = Vec<(Sym, TyId, ExpId, usize)>;

impl Checker {
    /// The typed lambdas of `items`, in written order: each definition of
    /// a lambda with a written type, and each `define-rec` member.
    pub(crate) fn module_lambdas(&self, items: &[ModItem]) -> Lambdas {
        let mut out = Vec::new();
        for (i, item) in items.iter().enumerate() {
            match item {
                ModItem::Val { name, ty: Some(ty), init, .. } if self.is_lambda(*init) => out.push((*name, *ty, *init, i)),
                ModItem::Rec(bs) => out.extend(bs.iter().map(|(n, t, e)| (*n, *t, *e, i))),
                _ => {}
            }
        }
        out
    }

    /// Each name `items` define, and the item defining it.
    fn module_places(items: &[ModItem]) -> Vec<(Sym, usize)> {
        let mut out = Vec::new();
        for (i, item) in items.iter().enumerate() {
            match item {
                ModItem::Val { name, .. } => out.push((*name, i)),
                ModItem::Rec(bs) => out.extend(bs.iter().map(|(n, _, _)| (*n, i))),
                ModItem::Abs { up, down, .. } => out.extend([(*up, i), (*down, i)]),
                ModItem::Desc { .. } => {}
            }
        }
        out
    }

    /// Each of `items` whose value is a module as written, and its values'
    /// names: a `module` (or a `load-module`'s), under any `plambda`,
    /// `proj`, `lambda` of no parameters or call of none, or an earlier
    /// such item's name. An abstract type's conversions stay inside, so
    /// are not among them. As the FX-26 checker's `k-written-modules`.
    pub(crate) fn written_modules(&self, items: &[ModItem]) -> Vec<(Sym, Vec<Sym>)> {
        let mut out: Vec<(Sym, Vec<Sym>)> = Vec::new();
        for item in items {
            if let ModItem::Val { name, init, .. } = item
                && let Some(ns) = self.written_module(*init, &out)
            {
                out.push((*name, ns));
            }
        }
        out
    }

    /// The items, in order, checked before a module's typed lambdas are
    /// bound: each with no type written whose value is a module as written
    /// (`written_module`) naming no item of the module but earlier such
    /// ones. As the FX-26 checker's `k-early-modules`.
    pub(crate) fn early_modules(&self, items: &[ModItem]) -> Vec<usize> {
        let places = Self::module_places(items);
        let (mut known, mut out): (Vec<(Sym, Vec<Sym>)>, Vec<usize>) = (Vec::new(), Vec::new());
        for (i, item) in items.iter().enumerate() {
            if let ModItem::Val { name, ty: None, init, .. } = item
                && let Some(ns) = self.written_module(*init, &known)
                && self.module_names_in(*init, &places).iter().all(|n| known.iter().any(|(k, _)| k == n))
            {
                known.push((*name, ns));
                out.push(i);
            }
        }
        out
    }

    fn written_module(&self, e: ExpId, known: &[(Sym, Vec<Sym>)]) -> Option<Vec<Sym>> {
        use crate::ast::Exp;
        match self.arena.exp_at(e) {
            Exp::Module(items) => Some(
                items
                    .iter()
                    .flat_map(|it| match it {
                        ModItem::Val { name, .. } => vec![*name],
                        ModItem::Rec(bs) => bs.iter().map(|(n, _, _)| *n).collect(),
                        _ => Vec::new(),
                    })
                    .collect(),
            ),
            Exp::App { fun, args } if args.is_empty() => self.written_module(*fun, known),
            Exp::Lambda { params, body } if params.is_empty() => self.written_module(*body, known),
            Exp::Proj { body, .. } | Exp::PLambda { body, .. } => self.written_module(*body, known),
            Exp::Var(x) => known.iter().find(|(n, _)| n == x).map(|(_, ns)| ns.clone()),
            _ => None,
        }
    }

    /// The names free in `x` that the module defines, in written order.
    fn module_names_in(&self, x: ExpId, places: &[(Sym, usize)]) -> Vec<Sym> {
        let free = self.free_vars(x);
        places.iter().filter(|(n, _)| free.contains(n)).map(|(n, _)| *n).collect()
    }

    /// Refused: an item that is not a typed lambda whose value may reach,
    /// when it is made, an item not made yet (itself included).
    pub(crate) fn module_hazards(&self, items: &[ModItem], lambdas: &Lambdas) -> R<()> {
        let places = Self::module_places(items);
        let place = |n: Sym| places.iter().find(|(m, _)| *m == n).map(|(_, i)| *i);
        let lambda = |n: Sym| lambdas.iter().position(|(m, ..)| *m == n);
        for (i, item) in items.iter().enumerate() {
            let ModItem::Val { name, init, .. } = item else { continue };
            if lambda(*name).is_some_and(|k| lambdas[k].3 == i) {
                continue;
            }
            // Breadth first from the value's names, through lambdas, each
            // name with the one it was reached from.
            let mut seen: Vec<(Sym, Option<usize>)> = Vec::new();
            for n in self.module_names_in(*init, &places) {
                seen.push((n, None));
            }
            let mut k = 0;
            while k < seen.len() {
                let n = seen[k].0;
                let at = place(n).expect("a module's name");
                if at >= i {
                    let mut chain = vec![n];
                    let mut from = seen[k].1;
                    while let Some(f) = from {
                        chain.push(seen[f].0);
                        from = seen[f].1;
                    }
                    chain.reverse();
                    return Err(FxError::at(self.arena.span_of(*init), self.too_soon(*name, &chain)));
                }
                if let Some(l) = lambda(n) {
                    for m in self.module_names_in(lambdas[l].2, &places) {
                        if !seen.iter().any(|(s, _)| *s == m) {
                            seen.push((m, Some(k)));
                        }
                    }
                }
                k += 1;
            }
        }
        Ok(())
    }

    /// What is said of `x`, whose value reaches `chain`'s last name, not
    /// made yet, through the lambdas before it.
    fn too_soon(&self, x: Sym, chain: &[Sym]) -> String {
        let name = |n: &Sym| format!("`{}`", self.interner.name(*n));
        let last = chain.last().expect("a chain");
        let mut s = format!("{} uses {}", name(&x), name(&chain[0]));
        for n in &chain[1..] {
            s.push_str(&format!(", which uses {}", name(n)));
        }
        if *last == x {
            s.push_str(", before it is made");
        } else if chain.len() == 1 {
            s.push_str(", defined after it");
        } else {
            s.push_str(&format!(", defined after {}", name(&x)));
        }
        s
    }

    /// For each of `lambdas`, the lambdas (positions, in written order) of
    /// its recursive group: those it reaches that reach it, by the names
    /// their values hold (its strongly connected component, if that is a
    /// cycle); empty if it is in none.
    pub(crate) fn module_groups(&self, lambdas: &Lambdas) -> Vec<Vec<usize>> {
        let n = lambdas.len();
        let edges: Vec<Vec<usize>> = lambdas
            .iter()
            .map(|(_, _, e, _)| self.free_vars(*e).iter().filter_map(|m| lambdas.iter().position(|(l, ..)| l == m)).collect())
            .collect();
        // Their strongly connected components (Tarjan's), linear in the
        // lambdas and edges; as the FX-26 checker's `k-mod-groups`. A lambda
        // walked and not yet in a component is on the stack.
        struct Walk<'a> {
            edges: &'a [Vec<usize>],
            index: Vec<Option<usize>>,
            low: Vec<usize>,
            comp: Vec<Option<usize>>,
            stack: Vec<usize>,
            count: usize,
            comps: usize,
        }
        fn visit(w: &mut Walk, v: usize) {
            w.index[v] = Some(w.count);
            w.low[v] = w.count;
            w.count += 1;
            w.stack.push(v);
            for &t in w.edges[v].iter() {
                match w.index[t] {
                    None => {
                        visit(w, t);
                        w.low[v] = w.low[v].min(w.low[t]);
                    }
                    Some(i) if w.comp[t].is_none() => w.low[v] = w.low[v].min(i),
                    Some(_) => {}
                }
            }
            if Some(w.low[v]) == w.index[v] {
                while let Some(t) = w.stack.pop() {
                    w.comp[t] = Some(w.comps);
                    if t == v {
                        break;
                    }
                }
                w.comps += 1;
            }
        }
        let mut w = Walk { edges: &edges, index: vec![None; n], low: vec![0; n], comp: vec![None; n], stack: Vec::new(), count: 0, comps: 0 };
        for v in 0..n {
            if w.index[v].is_none() {
                visit(&mut w, v);
            }
        }
        // A lambda's group: its component, if it is on a cycle (it names
        // itself, or another is in its component).
        (0..n)
            .map(|a| {
                let same: Vec<usize> = (0..n).filter(|b| w.comp[*b] == w.comp[a]).collect();
                if same.len() > 1 || edges[a].contains(&a) { same } else { Vec::new() }
            })
            .collect()
    }
}
