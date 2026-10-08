//! Programs: the top level, above the kernel.
//!
//! The kernel is expressions. A program is a sequence of top-level forms, each
//! of which may add to the environment the rest of the program sees:
//!
//! * `(define name type expression)` — `name` is a `type`. When the
//!   expression is a lambda, `name` is in scope in it, so the procedure may
//!   call itself (a one-binding `define-rec`); otherwise it is not.
//! * `(define name expression)` — the type is the expression's own; not
//!   recursive (a top-level `let`).
//! * `(define-rec (name type lambda) …)` — procedures that may call each
//!   other, each name in scope in every lambda (a top-level `letrec`). They
//!   are lambdas, so nothing runs before every one of them exists.
//! * `(define-type name type)` — a type abbreviation, which may mention itself
//!   (a top-level one-binding `dletrec`). Without it, a recursive type such as
//!   a continuation that is its own argument has to be written out in full at
//!   every use.
//! * `(define-effect name effect)` — an effect abbreviation, for the effect
//!   a group of procedures share.
//! * anything else is an expression, checked in the environment so far.

use crate::ast::{Effect, Region, TyId};
use crate::check::{Checked, Checker};
use crate::error::{FxError, R};
use fixpt_read::{FileId, Reader, Span, Sym, Syntax, SyntaxProfile};

/// What one top-level form did.
#[derive(Clone, Debug)]
pub enum Top {
    /// `(define name …)`: `name` is bound to a value of this type, and
    /// computing it has this effect.
    /// `typed` when the type was written; `recursive` when the name is in
    /// scope in its expression, which is then a lambda.
    /// `inferred` when it is a `define*`, whose type's globals were found.
    /// `assigns` when it assigns the global the name has, a redefinition
    /// every use can take (`Checker::top_defining`); else it makes a new
    /// global.
    Define { name: Sym, ty: TyId, effect: Effect, exp: crate::ast::ExpId, typed: bool, inferred: bool, recursive: bool, assigns: bool },
    /// `(define-rec (name type lambda) …)`: each name bound to its lambda;
    /// `assigns` as for `Define`, for all of them.
    DefineRec { bindings: Vec<(Sym, TyId, crate::ast::ExpId)>, assigns: bool },
    /// `(define-type name …)`.
    DefineType { name: Sym, ty: TyId },
    /// `(define-type (name (param kind) …) …)`: a parametric abbreviation.
    DefineTypeFamily { name: Sym },
    /// `(define-generative name rep)`: a new type.
    DefineGenerative { name: Sym },
    /// `(define-effect name …)`: an abbreviation for an effect.
    DefineEffect { name: Sym, effect: Effect },
    /// An expression.
    Exp(Checked),
}

/// A definition checked, as a redefinition finds it: the names it defines,
/// its form, and the globals it uses (its expressions' free variables).
#[derive(Clone, Debug)]
pub struct Definition {
    pub names: Vec<Sym>,
    pub form: Syntax,
    pub uses: Vec<Sym>,
}

/// A form checked at the top level, and what it makes run
/// (`Checker::top_defining`).
#[derive(Clone, Debug)]
pub struct Defining {
    /// What runs, in order: the form's own definition (or anything else it
    /// is), then, if it redefined a name with a type not every use of it can
    /// take, each earlier definition that uses the name and still checks,
    /// defined again. With each, whether it assigns the globals its names
    /// have (a redefinition every use can take) rather than making new ones.
    pub run: Vec<(Top, Syntax)>,
    /// The earlier definitions that no longer check, and why: broken, a use
    /// of one an error, until they are defined again.
    pub broken: Vec<(Vec<Sym>, String)>,
}

fn set_assigns(top: &mut Top, to: bool) {
    if let Top::Define { assigns, .. } | Top::DefineRec { assigns, .. } = top {
        *assigns = to;
    }
}

impl Checker {
    /// `form`, checked as the next top-level form, under redefinition
    /// (`docs/fx26.md`, "Redefinition"), for files and the REPL alike:
    /// a global's uses always refer to what it is now. A definition of a
    /// name already a global, at a type every use can take (each a subtype
    /// of the old), assigns the global. At any other type it makes a new
    /// global, and every earlier definition that uses the name (and every
    /// one that uses those) is checked again, in order: each that checks is
    /// defined again, by the same rule; each that does not is broken. To
    /// keep a value as it was, bind it: `(define d (let ((g g)) …))`.
    pub fn top_defining(&mut self, form: &Syntax) -> R<Defining> {
        let names = self.defined_names(form);
        let olds: Vec<(Sym, TyId)> = names.iter().filter_map(|n| Some((*n, self.global_type(*n)?))).collect();
        let users = if olds.is_empty() || self.defer_reruns { Vec::new() } else { self.users_of(&names) };
        let direct = if olds.is_empty() || !self.defer_reruns { Vec::new() } else { self.direct_users_of(&names) };
        let mut top = self.top(form)?;
        let assigns = !olds.is_empty() && self.fits_old(&top, &olds);
        set_assigns(&mut top, assigns);
        self.record(form, &top);
        let mut done = Defining { run: vec![(top, form.clone())], broken: Vec::new() };
        if olds.is_empty() || assigns {
            return Ok(done);
        }
        if self.defer_reruns {
            for d in direct {
                self.note_outdated(d.names, &names);
            }
            return Ok(done);
        }
        let shown = |c: &Checker, ns: &[Sym]| ns.iter().map(|n| format!("`{}`", c.interner.name(*n))).collect::<Vec<_>>().join(", ");
        for u in users {
            let olds: Vec<(Sym, TyId)> = u.names.iter().filter_map(|n| Some((*n, self.global_type(*n)?))).collect();
            let checked = self.top(&u.form);
            match checked {
                Ok(mut top) => {
                    let assigns = self.fits_old(&top, &olds);
                    set_assigns(&mut top, assigns);
                    self.record(&u.form, &top);
                    done.run.push((top, u.form));
                }
                Err(e) => {
                    let why = format!("since {} was redefined ({})", shown(self, &names), e.message);
                    for n in &u.names {
                        self.break_global(*n, why.clone());
                    }
                    done.broken.push((u.names, e.message));
                }
            }
        }
        Ok(done)
    }

    /// Every top-level form `form` runs under redefinition, in order
    /// (`top_defining`): itself, and the definitions it runs again.
    pub fn top_all(&mut self, form: &Syntax) -> R<Vec<Top>> {
        Ok(self.top_defining(form)?.run.into_iter().map(|(t, _)| t).collect())
    }

    /// What `top_defining` would do with `form`, with nothing changed: for
    /// a driver to decide whether a redefinition that would break
    /// definitions goes ahead.
    pub fn try_defining(&mut self, form: &Syntax) -> R<Defining> {
        let (mark, broken, defs, outdated) = (self.mark(), self.broken.clone(), self.defs.clone(), self.outdated.clone());
        let r = self.top_defining(form);
        self.rollback(mark);
        (self.broken, self.defs, self.outdated) = (broken, defs, outdated);
        r
    }

    /// Defining a global writes it: a procedure stored in global `f` whose
    /// calls read `f` may reach itself through the global, which the
    /// checker's termination reasoning, trusting every procedure of a type
    /// without `spin` to end, has not seen. So it must say `spin`, as a
    /// procedure kept in a ref must (`no_knot`), however it reads `f`: by
    /// calling itself, or something that calls it, or a procedure kept as
    /// it was, `(let ((h h)) …)`. One that stays `pure` binds itself with a
    /// local `letrec`. A `define-rec`'s members read each other so. Reading
    /// `@globals` may read `f` only once `f` is a global: at its first
    /// definition nothing defined before refers to it, and what later does
    /// is a write checked in its turn (`docs/fx26.md`, "Redefinition").
    fn no_reaching_itself(&self, top: &Top, redefining: bool, span: fixpt_read::Span) -> R<()> {
        let group: Vec<(Sym, TyId)> = match top {
            Top::Define { name, ty, .. } => vec![(*name, *ty)],
            Top::DefineRec { bindings, .. } => bindings.iter().map(|(n, t, _)| (*n, *t)).collect(),
            _ => return Ok(()),
        };
        for (n, t) in &group {
            if self.spins(*t) {
                continue;
            }
            let reads = self.latent_globals(*t);
            let name = self.interner.name(*n);
            if let Some((m, _)) = group.iter().find(|(m, _)| reads.contains(&Region::Global(*m))) {
                let m = self.interner.name(*m);
                return Err(FxError::at(
                    span,
                    format!("calling `{name}` reads `{m}`, so `{name}` may reach itself through a global: its type must say `spin` (or, to call itself directly, it binds itself with a local `letrec`)"),
                ));
            }
            if redefining && reads.contains(&Region::Globals) {
                return Err(FxError::at(
                    span,
                    format!("calling `{name}` may read any global, `{name}` too, so `{name}` may reach itself through a global: its type must say `spin`"),
                ));
            }
        }
        Ok(())
    }

    /// The globals calling a value of type `t` reads: its latent effect's,
    /// under any `poly`; none, if it is not a procedure.
    fn latent_globals(&self, t: TyId) -> Vec<Region> {
        let mut t = self.arena.resolve(t);
        while let crate::ast::Ty::Poly { body, .. } = self.arena.get(t) {
            t = self.arena.resolve(*body);
        }
        self.arena.get(t).as_subr().map_or(Vec::new(), |(e, _, _)| e.0.iter().filter_map(|a| a.region().filter(|r| r.is_globals())).collect())
    }

    /// Whether `t` is a procedure whose calls may not end: `spin` in its
    /// latent effect, under any `poly`.
    fn spins(&self, t: TyId) -> bool {
        let mut t = self.arena.resolve(t);
        while let crate::ast::Ty::Poly { body, .. } = self.arena.get(t) {
            t = self.arena.resolve(*body);
        }
        self.arena.get(t).as_subr().is_some_and(|(e, _, _)| e.0.contains(&crate::ast::Atom::Spin))
    }

    /// Whether every name `top` defines has a type the old one's uses can
    /// take.
    fn fits_old(&mut self, top: &Top, olds: &[(Sym, TyId)]) -> bool {
        let news: Vec<(Sym, TyId)> = match top {
            Top::Define { name, ty, .. } => vec![(*name, *ty)],
            Top::DefineRec { bindings, .. } => bindings.iter().map(|(n, t, _)| (*n, *t)).collect(),
            _ => return false,
        };
        olds.iter().all(|(n, t)| news.iter().any(|(m, u)| m == n && self.subtype(*u, *t)))
    }

    /// The names a form defines: `(define name …)`'s, and each of
    /// `(define-rec (name type lambda) …)`'s.
    pub fn defined_names(&self, form: &Syntax) -> Vec<Sym> {
        let Some(items) = form.as_proper_list() else { return Vec::new() };
        match items.first().and_then(|h| h.as_symbol()).map(|h| self.interner.name(h)) {
            Some("define" | "define*") => items.get(1).and_then(|n| n.as_symbol()).into_iter().collect(),
            Some("define-rec") => items[1..].iter().filter_map(|b| b.as_proper_list()?.first()?.as_symbol()).collect(),
            _ => Vec::new(),
        }
    }

    /// The definitions that use `names`, and those that use them, and so
    /// on, oldest first.
    fn users_of(&self, names: &[Sym]) -> Vec<Definition> {
        let mut used: Vec<Sym> = names.to_vec();
        let mut out = Vec::new();
        for d in &self.defs {
            if d.names.iter().any(|n| names.contains(n)) {
                continue;
            }
            if d.uses.iter().any(|u| used.contains(u)) {
                used.extend(d.names.iter().copied());
                out.push(d.clone());
            }
        }
        out
    }

    /// The definitions that use `names` themselves, oldest first: what a
    /// redefinition of them leaves out of date, when re-runs wait
    /// (`defer_reruns`). Those that use these see them as they are.
    fn direct_users_of(&self, names: &[Sym]) -> Vec<Definition> {
        self.defs.iter().filter(|d| !d.names.iter().any(|n| names.contains(n)) && d.uses.iter().any(|u| names.contains(u))).cloned().collect()
    }

    /// The definition of `names` out of date, since `redefined`, which it
    /// uses, were defined again at new globals.
    fn note_outdated(&mut self, names: Vec<Sym>, redefined: &[Sym]) {
        match self.outdated.iter_mut().find(|(ns, _)| *ns == names) {
            Some((_, since)) => since.extend(redefined.iter().filter(|r| !since.contains(r)).collect::<Vec<_>>()),
            None => self.outdated.push((names, redefined.to_vec())),
        }
    }

    /// The definitions out of date (`defer_reruns`), oldest first: each
    /// one's names, the names it uses that were defined again since, and
    /// its form, to run again.
    pub fn outdated(&self) -> Vec<(Vec<Sym>, Vec<Sym>, Syntax)> {
        self.defs
            .iter()
            .filter_map(|d| {
                let (_, since) = self.outdated.iter().find(|(ns, _)| *ns == d.names)?;
                Some((d.names.clone(), since.clone(), d.form.clone()))
            })
            .collect()
    }

    /// `form`, checked as `top`, recorded as the definition of its names now.
    fn record(&mut self, form: &Syntax, top: &Top) {
        let (names, exps): (Vec<Sym>, Vec<crate::ast::ExpId>) = match top {
            Top::Define { name, exp, .. } => (vec![*name], vec![*exp]),
            Top::DefineRec { bindings, .. } => bindings.iter().map(|(n, _, e)| (*n, *e)).unzip(),
            _ => return,
        };
        // Defined again, so up to date.
        self.outdated.retain(|(ns, _)| !ns.iter().any(|n| names.contains(n)));
        let mut uses = Vec::new();
        for e in exps {
            self.free_into(e, &mut Vec::new(), &mut uses);
        }
        uses.retain(|u| !names.contains(u));
        self.defs.retain(|d| !d.names.iter().any(|n| names.contains(n)));
        self.defs.push(Definition { names, form: form.clone(), uses });
    }

    /// Read `text` in FX-26's lexical syntax (`SyntaxProfile::FX26`),
    /// recording spans against `file`.
    pub fn read_in(&mut self, file: FileId, text: &str) -> R<Vec<Syntax>> {
        let mut interner = std::mem::take(&mut self.interner);
        let r = Reader::new(text, file, SyntaxProfile::FX26, &mut interner).read_all();
        self.interner = interner;
        let forms = r.map_err(|e| FxError::at(e.span, e.message))?;
        self.expand_forms(forms)
    }

    /// A module's file (`load-module`) read: its `define-datatype`s
    /// expanded, its `define-generative`s left as they are, a module's own.
    pub(crate) fn read_module_file(&mut self, file: FileId, text: &str) -> R<Vec<Syntax>> {
        let mut interner = std::mem::take(&mut self.interner);
        let r = Reader::new(text, file, SyntaxProfile::FX26, &mut interner).read_all();
        self.interner = interner;
        let forms = r.map_err(|e| FxError::at(e.span, e.message))?;
        let mut out = Vec::new();
        for f in forms {
            self.expand_datatype(f, &mut out)?;
        }
        Ok(out)
    }

    /// What is expanded as it is read (`define-datatype`), for forms read
    /// some other way: by the reader written in FX-26 (`crate::syn`).
    pub fn expand_forms(&mut self, forms: Vec<Syntax>) -> R<Vec<Syntax>> {
        let mut out = Vec::new();
        for f in forms {
            if self.expand_generative(&f, &mut out)? {
                continue;
            }
            self.expand_datatype(f, &mut out)?;
        }
        Ok(out)
    }

    /// `(define-generative head rep)`: the form itself, which the checker
    /// alone reads, and its two conversions, each the identity:
    /// `(define up-name (poly (param …) (subr pure (rep) (name p …))) (lambda (x) x))`
    /// and `down-name` the other way. `false` if `form` is something else.
    fn expand_generative(&mut self, form: &Syntax, out: &mut Vec<Syntax>) -> R<bool> {
        let items = form.as_proper_list().unwrap_or(&[]).to_vec();
        if items.first().and_then(|h| h.as_symbol()).map(|h| self.interner.name(h)) != Some("define-generative") {
            return Ok(false);
        }
        let span = form.span;
        let usage = "`(define-generative name type)` or `(define-generative (name (param kind) …) type)`";
        let [_, head, rep] = &items[..] else {
            return Err(FxError::at(span, usage));
        };
        let (name, params) = match head.as_proper_list() {
            Some([n, ps @ ..]) => (n.clone(), Some(ps.to_vec())),
            _ => (head.clone(), None),
        };
        let Some(n) = name.as_symbol() else {
            return Err(FxError::at(span, usage));
        };
        let n = self.interner.name(n).to_string();
        let mut sym = |s: &str| Syntax::symbol(span, self.interner.intern(s));
        let list = |items: Vec<Syntax>| {
            if items.is_empty() { Syntax::new(span, fixpt_read::Datum::Nil) } else { Syntax::list(span, items) }
        };
        let (define, poly, subr, pure, lambda, x) = (sym("define"), sym("poly"), sym("subr"), sym("pure"), sym("lambda"), sym("x"));
        let (up, down) = (sym(&format!("up-{n}")), sym(&format!("down-{n}")));
        // The binders, variance left out, and the type as it is used.
        let (binders, used) = match &params {
            Some(ps) => {
                let mut bs = Vec::new();
                let mut u = vec![name.clone()];
                for p in ps {
                    match p.as_proper_list() {
                        Some([pn, k, ..]) => {
                            bs.push(list(vec![pn.clone(), k.clone()]));
                            u.push(pn.clone());
                        }
                        _ => return Err(FxError::at(p.span, "a parameter is `(name kind)`, `(name kind +)` or `(name kind -)`")),
                    }
                }
                (Some(bs), list(u))
            }
            None => (None, name.clone()),
        };
        let conv = |from: &Syntax, to: &Syntax| {
            let t = list(vec![subr.clone(), pure.clone(), list(vec![from.clone()]), to.clone()]);
            match &binders {
                Some(bs) => list(vec![poly.clone(), list(bs.clone()), t]),
                None => t,
            }
        };
        let identity = list(vec![lambda.clone(), list(vec![x.clone()]), x.clone()]);
        out.push(form.clone());
        out.push(list(vec![define.clone(), up, conv(rep, &used), identity.clone()]));
        out.push(list(vec![define, down, conv(&used, rep), identity]));
        Ok(true)
    }

    /// FX-91's `(define-datatype name (tag type …) …)`: a sum of products,
    /// each variant's members labelled from 1, and a constructor per tag,
    /// `(tag e …)`. Taken apart with `tagcase`, whose arm `(tag (x …) body)`
    /// names the members. Expanded as it is read, into the forms it stands
    /// for, so every way of running a program sees them.
    ///
    /// `(define-datatype (name (param kind) …) …)` has parameters: a type
    /// family, which its variants may mention with the same parameters, and
    /// constructors polymorphic in them.
    pub(crate) fn expand_datatype(&mut self, form: Syntax, out: &mut Vec<Syntax>) -> R<()> {
        let items = form.as_proper_list().unwrap_or(&[]).to_vec();
        if items.first().and_then(|h| h.as_symbol()).map(|h| self.interner.name(h)) != Some("define-datatype") {
            out.push(form);
            return Ok(());
        }
        let span = form.span;
        let [_, name, variants @ ..] = &items[..] else {
            return Err(FxError::at(span, "`(define-datatype name (tag type …) …)`"));
        };
        // The name, and the parameters, if it has any: `(name (param kind) …)`.
        let (name, family) = match name.as_proper_list() {
            Some([n, ps @ ..]) if n.as_symbol().is_some() => (n.clone(), Some(ps.to_vec())),
            _ => (name.clone(), None),
        };
        let name = &name;
        if name.as_symbol().is_none() || variants.is_empty() {
            return Err(FxError::at(span, "`(define-datatype name (tag type …) …)`"));
        }
        // What the type is called where it is used: `name`, or `(name param …)`.
        let mut used = name.clone();
        if let Some(ps) = &family {
            let mut u = vec![name.clone()];
            for p in ps {
                match p.as_proper_list() {
                    Some([n, _]) if n.as_symbol().is_some() => u.push(n.clone()),
                    _ => return Err(FxError::at(p.span, "a parameter is `(name kind)`")),
                }
            }
            used = Syntax::list(span, u);
        }
        let mut sym = |s: &str| Syntax::symbol(span, self.interner.intern(s));
        let (define_type, define, sumof, productof, subr, pure, lambda, sum, product, poly) = (
            sym("define-type"),
            sym("define"),
            sym("sumof"),
            sym("productof"),
            sym("subr"),
            sym("pure"),
            sym("lambda"),
            sym("sum"),
            sym("product"),
            sym("poly"),
        );
        let int = |n: usize| Syntax::new(span, fixpt_read::Datum::Number(fixpt_read::Num::Int(n as i64)));
        let list = |items: Vec<Syntax>| {
            if items.is_empty() { Syntax::new(span, fixpt_read::Datum::Nil) } else { Syntax::list(span, items) }
        };
        let mut arms = vec![sumof];
        let mut ctors = Vec::new();
        for v in variants {
            let parts = v.as_proper_list().unwrap_or(&[]).to_vec();
            let Some((tag, members)) = parts.split_first().filter(|(t, _)| t.as_symbol().is_some()) else {
                return Err(FxError::at(v.span, "a variant is `(tag type …)`"));
            };
            let mut prod = vec![productof.clone()];
            let mut params = Vec::new();
            let mut fields = vec![product.clone()];
            for (i, m) in members.iter().enumerate() {
                prod.push(list(vec![int(i + 1), m.clone()]));
                let x = Syntax::symbol(span, self.interner.intern(&format!("%x{}", i + 1)));
                params.push(x.clone());
                fields.push(list(vec![int(i + 1), x]));
            }
            arms.push(list(vec![tag.clone(), list(prod)]));
            let mut ty = list(vec![subr.clone(), pure.clone(), list(members.to_vec()), used.clone()]);
            if let Some(ps) = &family {
                ty = list(vec![poly.clone(), list(ps.clone()), ty]);
            }
            // At its variant: no two constructors' bodies at one place, as
            // the compilers tell lambdas apart by where their bodies are.
            let body = Syntax::list(v.span, vec![sum.clone(), tag.clone(), list(fields)]);
            ctors.push(list(vec![define.clone(), tag.clone(), ty, list(vec![lambda.clone(), list(params), body])]));
        }
        let head = match &family {
            Some(ps) => {
                let mut h = vec![name.clone()];
                h.extend(ps.iter().cloned());
                list(h)
            }
            None => name.clone(),
        };
        out.push(list(vec![define_type, head, list(arms)]));
        out.extend(ctors);
        Ok(())
    }

    /// Check one top-level form, keeping what it defines.
    pub fn top(&mut self, form: &Syntax) -> R<Top> {
        let items = form.as_proper_list().unwrap_or(&[]);
        let head = items.first().and_then(|h| h.as_symbol()).map(|h| self.interner.name(h));
        match head {
            Some("define" | "define*" | "define-rec") => {
                let redefining = self.defined_names(form).iter().any(|n| self.global_type(*n).is_some());
                let mark = self.mark();
                let top = match head {
                    Some("define") => self.define(form.span, items, false),
                    Some("define*") => self.define(form.span, items, true),
                    _ => self.define_rec(form.span, items),
                }?;
                if let Err(e) = self.no_reaching_itself(&top, redefining, form.span) {
                    self.rollback(mark);
                    return Err(e);
                }
                Ok(top)
            }
            Some("define-effect") => {
                let [_, name, def] = items else {
                    return Err(FxError::at(form.span, "`(define-effect name effect)`"));
                };
                let name = self.binder_name(name)?;
                let effect = self.parse_effect(def)?;
                self.dscope.push((name, crate::parse::DScope::Eff(effect.clone())));
                Ok(Top::DefineEffect { name, effect })
            }
            Some("define-generative") => {
                let [_, head, rep] = items else {
                    return Err(FxError::at(form.span, "`(define-generative name type)` or `(define-generative (name (param kind) …) type)`"));
                };
                let name = self.define_generative(head, rep)?;
                // Only its own conversions, which follow, see inside it.
                let which = crate::ast::last_id(self.generatives.len(), "generative types");
                for side in ["up-", "down-"] {
                    let n = self.interner.intern(&format!("{side}{}", self.interner.name(name)));
                    self.inside.push((n, which));
                }
                Ok(Top::DefineGenerative { name })
            }
            Some("define-type") => {
                let [_, name, def] = items else {
                    return Err(FxError::at(form.span, "`(define-type name type)`"));
                };
                if let Some([n, params @ ..]) = name.as_proper_list() {
                    let n = self.binder_name(n)?;
                    let params = Syntax::list(name.span, params.to_vec());
                    self.define_type_family(n, &params, def)?;
                    return Ok(Top::DefineTypeFamily { name: n });
                }
                // `(define-type name (dlambda …))`: a name for a description
                // function (`crate::kinds`).
                if def.as_proper_list().and_then(|d| d.first()).and_then(|h| h.as_symbol()).is_some_and(|h| self.interner.name(h) == "dlambda") {
                    let n = self.binder_name(name)?;
                    let f = self.parse_fun(def, None)?;
                    self.dscope.push((n, crate::parse::DScope::Fun(f)));
                    return Ok(Top::DefineTypeFamily { name: n });
                }
                let name = self.binder_name(name)?;
                let ty = self.define_type(name, def, form.span)?;
                Ok(Top::DefineType { name, ty })
            }
            _ => {
                let e = self.parse_exp(form)?;
                let (ty, effect) = self.synth(e)?;
                Ok(Top::Exp(Checked { ty, effect, exp: e }))
            }
        }
    }

    /// Put the binders of every `poly` at the top of `t` in scope for parsing.
    fn bind_signature(&mut self, t: TyId) {
        let mut t = self.arena.resolve(t);
        while let crate::ast::Ty::Poly { binders, body } = self.arena.get(t).clone() {
            for (v, k) in binders {
                let name = self.arena.dvar_name(v);
                self.dscope.push((name, crate::parse::DScope::Var(v, k)));
            }
            t = self.arena.resolve(body);
        }
    }

    fn binder_name(&self, s: &Syntax) -> R<Sym> {
        s.as_symbol().ok_or_else(|| FxError::at(s.span, "expected a name"))
    }

    /// `(define name type init)`, or `(define name init)`. With `infer`,
    /// `(define* name type lambda)`: the globals the procedure reads, which
    /// its type leaves out, are found, precisely, and put in its type's
    /// latent effect.
    fn define(&mut self, span: Span, items: &[Syntax], infer: bool) -> R<Top> {
        match items {
            [_, name, ty, init] => {
                let name = self.binder_name(name)?;
                self.pending_lemma = None;
                let written = ty;
                let ty = self.parse_type(ty)?;
                let ty = self.resolve_selects(ty, written.span)?;
                // Checked as though it said it read any globals; what it
                // reads is then taken from its body.
                let declared = ty;
                let ty = match infer {
                    false => ty,
                    true => self.with_latent(ty, &Effect::atom(crate::ast::Atom::Read(crate::ast::Region::Globals))).ok_or_else(|| {
                        FxError::at(written.span, "`define*` finds what a procedure reads: its type is a `subr`")
                    })?,
                };
                // A `proves` type: a lemma, once the body proves it.
                let lemma = self.pending_lemma.take();
                // A signature's binders are in scope in the definition, which
                // is checked against it: `(define id (poly ((t type)) …)
                // (lambda ((x t)) x))` means what a `plambda` would.
                let depth = self.dscope.len();
                self.bind_signature(ty);
                let e = self.parse_exp(init);
                self.dscope.truncate(depth);
                let e = e?;
                if infer && !self.is_lambda(e) {
                    return Err(FxError::at(self.arena.span_of(e), "`define*` defines a procedure: a `lambda`"));
                }
                // A lambda is in scope in itself, as a `letrec` binding is:
                // making it runs nothing, so nothing sees it unmade. With
                // `define*`, at its type as written: the globals it reads
                // are those of its body, its own name included if it calls
                // itself.
                let recursive = self.is_lambda(e);
                if recursive {
                    self.push_global(name, declared);
                    self.known.insert((name, self.env.len() - 1));
                }
                // A lambda whose every run ends needs no `spin`.
                let rdepth = self.recursive.len();
                if recursive {
                    self.note_termination(&[(name, ty, e)]);
                }
                // A generative type's own `up-` and `down-` see inside it.
                let inside = self.inside.iter().position(|(n, _)| *n == name).map(|i| self.inside.remove(i).1);
                if let Some(g) = inside {
                    self.transparent.push(g);
                }
                let checked = self.check_declared(name, ty, e);
                // With `define*`, the globals the body read, found, are its
                // type's; and it is checked again at that type, bound to it,
                // so that what is kept is a check at the type it has. That
                // check is the one that sees a call of the procedure itself
                // as recursion, so one that fails is the program's: a loop
                // with no `spin`, say.
                let (checked, ty) = match (infer, checked) {
                    (true, Ok(_)) => {
                        let reads = self.globals_read_by(e);
                        let found = self.with_latent(declared, &reads).expect("a subr");
                        let at = self.env.len() - 1;
                        self.env[at].1 = found;
                        self.recursive.truncate(rdepth);
                        self.note_termination(&[(name, found, e)]);
                        let again = self.check_declared(name, found, e).map_err(|err| {
                            let shown = self.show_ty(found);
                            FxError::at(err.span, format!("`define*` found `{}` to be a {shown}: {}", self.interner.name(name), err.message))
                        });
                        (again, found)
                    }
                    (_, c) => (c, ty),
                };
                if inside.is_some() {
                    self.transparent.pop();
                    self.conversions.push((name, ty));
                }
                self.recursive.truncate(rdepth);
                let checked = checked.and_then(|effect| match lemma {
                    Some(l) => {
                        self.check_proof(&l, name, e)?;
                        self.lemmas.push(crate::lemma::Lemma { by: Some((name, ty)), ..l });
                        Ok(effect)
                    }
                    None => Ok(effect),
                });
                match checked {
                    Ok(effect) => {
                        if !recursive {
                            self.push_global(name, ty);
                        }
                        // A list nothing writes: the compilers may make it
                        // once, if it is made of literals.
                        if matches!(self.arena.get(self.arena.resolve(ty)), crate::ast::Ty::Pair(_, _, Region::Frozen(..), _)) {
                            self.facts.frozen_defines.insert(e);
                        }
                        Ok(Top::Define { name, ty, effect, exp: e, typed: true, inferred: infer, recursive, assigns: false })
                    }
                    Err(err) => {
                        if recursive {
                            self.truncate_env(self.env.len() - 1);
                        }
                        Err(err)
                    }
                }
            }
            [_, name, init] => {
                let name = self.binder_name(name)?;
                let e = self.parse_exp(init)?;
                let (ty, effect) = self.synth(e)?;
                if self.is_lambda(e) {
                    self.known.insert((name, self.env.len()));
                }
                self.push_global(name, ty);
                Ok(Top::Define { name, ty, effect, exp: e, typed: false, inferred: false, recursive: false, assigns: false })
            }
            _ => Err(FxError::at(span, "`(define name type expression)` or `(define name expression)`")),
        }
    }

    /// `t`, a `subr` under any `poly`s, with `extra` in its latent effect;
    /// `None` if `t` is not one.
    pub(crate) fn with_latent(&mut self, t: TyId, extra: &Effect) -> Option<TyId> {
        let t = self.arena.resolve(t);
        match self.arena.get(t).clone() {
            crate::ast::Ty::Poly { binders, body } => {
                let body = self.with_latent(body, extra)?;
                Some(self.arena.ty(crate::ast::Ty::Poly { binders, body }))
            }
            crate::ast::Ty::Subr { conv, effect, params, result } => {
                Some(self.arena.ty(crate::ast::Ty::Subr { conv, effect: effect.union(extra), params, result }))
            }
            _ => None,
        }
    }

    /// The globals lambda `e`'s body reads, as checking found it: what a
    /// call of it reads.
    pub(crate) fn globals_read_by(&self, mut e: crate::ast::ExpId) -> Effect {
        use crate::ast::Exp;
        let body = loop {
            match self.arena.exp_at(e) {
                Exp::PLambda { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => e = *body,
                Exp::RLambda { lambda, .. } => e = *lambda,
                Exp::Lambda { body, .. } => break *body,
                _ => return Effect::pure(),
            }
        };
        let found = self.facts.effects.get(&body).cloned().unwrap_or_default();
        Effect(found.0.into_iter().filter(|a| a.region().is_some_and(crate::ast::Region::is_globals)).collect())
    }

    /// `(define-rec (name type lambda) …)`: every name in scope first, then
    /// each lambda checked against its type.
    fn define_rec(&mut self, span: Span, items: &[Syntax]) -> R<Top> {
        let depth = self.env.len();
        let rdepth = self.recursive.len();
        let r = (|| {
            let mut parts = Vec::new();
            for b in &items[1..] {
                let Some([name, ty, init]) = b.as_proper_list() else {
                    return Err(FxError::at(b.span, "a define-rec binding is `(name type lambda)`"));
                };
                let name = self.binder_name(name)?;
                let span = ty.span;
                let ty = self.parse_type(ty)?;
                let ty = self.resolve_selects(ty, span)?;
                self.push_global(name, ty);
                self.known.insert((name, self.env.len() - 1));
                parts.push((name, ty, init.clone()));
            }
            if parts.is_empty() {
                return Err(FxError::at(span, "`(define-rec (name type lambda) …)`"));
            }
            let mut bindings = Vec::new();
            for (name, ty, init) in parts {
                let d = self.dscope.len();
                self.bind_signature(ty);
                let e = self.parse_exp(&init);
                self.dscope.truncate(d);
                let e = e?;
                if !self.is_lambda(e) {
                    return Err(FxError::at(self.arena.span_of(e), crate::check::letrec_not_lambda(self.interner.name(name))));
                }
                bindings.push((name, ty, e));
            }
            // A group whose every run ends needs no `spin`.
            self.note_termination(&bindings);
            for (name, ty, e) in &bindings {
                self.check_declared(*name, *ty, *e)?;
            }
            Ok(Top::DefineRec { bindings, assigns: false })
        })();
        self.recursive.truncate(rdepth);
        if r.is_err() {
            self.truncate_env(depth);
        }
        r
    }

    /// Check `e` against `ty`, the type `name` is declared; an error at `e`
    /// itself says so.
    pub(crate) fn check_declared(&mut self, name: Sym, ty: TyId, e: crate::ast::ExpId) -> R<Effect> {
        self.check(e, ty).map_err(|err| self.declared_error(name, ty, e, err))
    }

    /// Check `form` as [`top`](Self::top) would, then forget it: nothing it
    /// defines stays in scope and nothing it allocated stays in the arena.
    /// What checking-as-you-type needs, since a form half typed is not a form
    /// submitted. The caller restores the interner, which it owns.
    pub fn try_top<T>(&mut self, form: &Syntax, then: impl FnOnce(&mut Checker, R<Top>) -> T) -> T {
        self.scratch(|c| {
            let r = c.top(form);
            then(c, r)
        })
    }

    /// Check a whole program written as text, keeping its definitions, and
    /// return what its last expression checked to.
    pub fn check_program(&mut self, text: &str) -> R<Checked> {
        let forms = self.read_in(FileId(0), text)?;
        let done = self.declare_ahead(&forms)?;
        let mut last = None;
        for (f, done) in forms.iter().zip(done) {
            if done {
                continue;
            }
            if let Top::Exp(c) = self.top(f)? {
                last = Some(c);
            }
        }
        last.ok_or_else(|| FxError::at(Span::new(FileId(0), 0, 0), "the program has no expression"))
    }

    /// The first of a whole program's two passes: every `define-type` and
    /// `define-effect` is processed, so that types can refer to each other in
    /// any order. Values cannot: a definition sees only those before it, and
    /// procedures that call each other are a `define-rec`. Returns, for each
    /// form, whether it is finished with (the abbreviations are). The second
    /// pass is `top` on the rest, in order.
    pub fn declare_ahead(&mut self, forms: &[Syntax]) -> R<Vec<bool>> {
        // Each type abbreviation defined once, by name, is in scope before
        // any is read, so that types may name each other in any order.
        let mut names: Vec<Sym> = Vec::new();
        let mut twice: Vec<Sym> = Vec::new();
        for f in forms {
            let items = f.as_proper_list().unwrap_or(&[]);
            // A description function, `(define-type f (dlambda …))`, is no
            // type to declare: it is read where it is defined.
            let dlambda = |d: &Syntax| d.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol()).is_some_and(|h| self.interner.name(h) == "dlambda");
            if let [h, n, d] = items
                && h.as_symbol().is_some_and(|h| self.interner.name(h) == "define-type")
                && let Some(n) = n.as_symbol()
                && !dlambda(d)
            {
                if names.contains(&n) { twice.push(n) } else { names.push(n) }
            }
        }
        self.ahead.clear();
        self.ahead_filled.clear();
        for n in names.into_iter().filter(|n| !twice.contains(n)) {
            let slot = self.arena.ty(crate::ast::Ty::Link(None));
            self.dscope.push((n, crate::parse::DScope::Rec(slot)));
            self.ahead.push((n, slot));
        }
        let r = self.declare_each(forms);
        self.ahead.clear();
        let filled = std::mem::take(&mut self.ahead_filled);
        let done = r?;
        for (slot, span) in filled {
            self.grounded(slot, span)?;
            self.note_closed(slot);
        }
        Ok(done)
    }

    /// The type names `forms`, checked together as a program's types are,
    /// lack: none if they check; the names whose absence alone stops them,
    /// found by standing an `int` in for each as it is found missing; or
    /// `None` if something else is wrong. Nothing is kept.
    pub fn missing_types(&mut self, forms: &[Syntax]) -> Option<Vec<Sym>> {
        let mut missing: Vec<Sym> = Vec::new();
        for _ in 0..32 {
            let span = forms.first()?.span;
            let mut group: Vec<Syntax> = missing
                .iter()
                .map(|m| {
                    let w = |c: &mut Checker, n: &str| Syntax::symbol(span, c.interner.intern(n));
                    Syntax::list(span, vec![w(self, "define-type"), Syntax::symbol(span, *m), w(self, "int")])
                })
                .collect();
            group.extend(forms.iter().cloned());
            let r = self.scratch(|c| -> R<()> {
                let done = c.declare_ahead(&group)?;
                for (f, d) in group.iter().zip(done) {
                    if !d {
                        c.top(f)?;
                    }
                }
                Ok(())
            });
            let Err(e) = r else { return Some(missing) };
            let name = e.message.strip_prefix('`').and_then(|m| m.strip_suffix("` is not a type"))?;
            let sym = self.interner.intern(name);
            if missing.contains(&sym) {
                return None;
            }
            missing.push(sym);
        }
        None
    }

    fn declare_each(&mut self, forms: &[Syntax]) -> R<Vec<bool>> {
        let mut done = Vec::new();
        for f in forms {
            let items = f.as_proper_list().unwrap_or(&[]);
            let head = items.first().and_then(|h| h.as_symbol()).map(|h| self.interner.name(h).to_string());
            match (head.as_deref(), items) {
                (Some("define-type" | "define-generative" | "define-effect"), _) => {
                    self.top(f)?;
                    done.push(true);
                }
                _ => done.push(false),
            }
        }
        Ok(done)
    }

    /// The names a program may use: every value and every type abbreviation
    /// in scope, innermost last, with shadowed ones left out.
    pub fn value_names(&self) -> Vec<Sym> {
        let mut out: Vec<Sym> = Vec::new();
        for (n, _) in self.env.iter().rev() {
            if !out.contains(n) {
                out.push(*n);
            }
        }
        out
    }

    /// The type a name is bound to, if it is a value.
    pub fn type_of_name(&self, name: Sym) -> Option<TyId> {
        self.env.iter().rev().find(|(n, _)| *n == name).map(|(_, t)| *t)
    }

    /// The type a name abbreviates, if `define-type` bound it.
    pub fn type_named(&self, name: Sym) -> Option<TyId> {
        self.dscope.iter().rev().find_map(|(n, d)| match d {
            crate::parse::DScope::Rec(t) if *n == name => Some(*t),
            _ => None,
        })
    }

    /// Every type abbreviation in scope.
    pub fn type_names(&self) -> Vec<Sym> {
        self.dscope
            .iter()
            .filter(|(_, d)| matches!(d, crate::parse::DScope::Rec(_)))
            .map(|(n, _)| *n)
            .collect()
    }

    /// The base types' names.
    pub fn base_names(&self) -> Vec<Sym> {
        self.base.keys().copied().collect()
    }

    /// Every description name in scope, the innermost binding of each:
    /// its name, what kind of thing it names (`type`, `family`,
    /// `generative`, `effect`, `region`), and its definition shown, for the
    /// REPL's `,apropos` and `,help`.
    pub fn description_entries(&self) -> Vec<(Sym, &'static str, String)> {
        use crate::parse::DScope;
        let mut seen = std::collections::HashSet::new();
        let mut out = Vec::new();
        for (name, d) in self.dscope.iter().rev() {
            if !seen.insert(*name) {
                continue;
            }
            let n = self.interner.name(*name).to_string();
            let entry = match d {
                DScope::Rec(t) => ("type", format!("{n} = {}", self.show_definition(*t))),
                DScope::Abbrev { params, body } => {
                    let ps: Vec<String> = params.iter().map(|(p, k)| format!("({} {})", self.interner.name(*p), self.show_kind(*k))).collect();
                    ("family", format!("({n} {}) = {}", ps.join(" "), fixpt_read::write_syntax(body, &self.interner)))
                }
                DScope::Eff(e) => ("effect", format!("{n} = {}", self.show_effect(e))),
                DScope::Generative(g) => {
                    let family = &self.generatives[*g as usize];
                    let ps: Vec<String> = family
                        .params
                        .iter()
                        .zip(&family.variance)
                        .map(|((v, k), var)| {
                            let mark = match var {
                                crate::ast::Variance::Co => " +",
                                crate::ast::Variance::Contra => " -",
                                crate::ast::Variance::Inv => "",
                            };
                            format!("({} {}{mark})", self.interner.name(self.arena.dvar_name(*v)), self.show_kind(*k))
                        })
                        .collect();
                    let head = if ps.is_empty() { n.clone() } else { format!("({n} {})", ps.join(" ")) };
                    ("generative", format!("{head} = {}", self.show_ty(family.rep)))
                }
                DScope::Fun(t) => ("function", format!("{n} = {}", self.show_ty(*t))),
                DScope::Var(..) | DScope::Region(_) | DScope::SizeVal(_) | DScope::ConvVal(_) => continue,
            };
            out.push((*name, entry.0, entry.1));
        }
        for b in self.base_names() {
            if seen.insert(b) {
                out.push((b, "base type", self.interner.name(b).to_string()));
            }
        }
        out
    }

    /// Run `f`, then forget everything it added to the environment, the
    /// description scope and the arena. The caller restores the interner.
    pub fn scratch<T>(&mut self, f: impl FnOnce(&mut Checker) -> T) -> T {
        let (env, dscope, arena) = (self.env.len(), self.dscope.len(), self.arena.mark());
        let out = f(self);
        self.truncate_env(env);
        self.dscope.truncate(dscope);
        self.facts.forget_from(arena.exps());
        self.arena.reset(arena);
        out
    }

    /// What the argument at `index` (from 1) of the application written
    /// `items` must be, given the operator and the other arguments — as
    /// text, since the type is forgotten with the rest of the scratch work.
    /// A binder nothing has fixed yet shows as its own name.
    pub fn describe_argument(&mut self, items: &[Syntax], index: usize) -> Option<String> {
        self.scratch(|c| {
            let op = c.parse_exp(items.first()?).ok()?;
            let others: Vec<(usize, crate::ast::ExpId)> = items
                .iter()
                .enumerate()
                .skip(1)
                .filter(|(i, _)| *i != index)
                .filter_map(|(i, s)| Some((i - 1, c.parse_exp(s).ok()?)))
                .collect();
            let t = c.argument_want(op, &others, index - 1)?;
            Some(c.show_ty(t))
        })
    }
}

/// The names a hole is read as while the REPL asks what goes there: in an
/// expression, an arm, and a tag. None of them can be written in a program,
/// and they mean nothing unless [`Checker::describe_hole`] set them.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Holes {
    /// The hole itself, where it stands.
    pub exp: Sym,
    /// The body of the `else` arm a hole in arm position becomes.
    pub arm: Sym,
    /// What that `else` arm binds: the tags no arm has taken.
    pub arm_var: Sym,
    /// The tag of `(sum ⟨hole⟩)`.
    pub tag: Sym,
}

/// Replace the first `,help` (or `,?`) in `s` by `hole`; where it was.
fn mark_hole(s: &mut Syntax, interner: &fixpt_read::Interner, hole: Sym) -> Option<Span> {
    use fixpt_read::Datum;
    let Datum::List { items, tail } = &mut s.datum else { return None };
    if let [u, h] = &items[..]
        && tail.is_none()
        && u.as_symbol().is_some_and(|u| interner.name(u) == "unquote")
        && h.as_symbol().is_some_and(|h| matches!(interner.name(h), "help" | "?"))
    {
        s.datum = Datum::Symbol(hole);
        return Some(s.span);
    }
    items.iter_mut().chain(tail.as_deref_mut()).find_map(|i| mark_hole(i, interner, hole))
}

impl Checker {
    /// What goes where the `,help` hole in `form` is, as the grammar and the
    /// types around it say: the type an expression there must have, the tags
    /// an arm or a `sum` there may take, or the shape the form around it
    /// must have. `None` if nothing is known. Nothing is kept.
    ///
    /// `forms` are the same form written more than one way (with fillers
    /// after the hole, or not): the first that reaches the hole answers;
    /// else the narrowest refusal around the hole, of all of them.
    pub fn describe_hole(&mut self, forms: &[Syntax]) -> Option<String> {
        let holes = Holes {
            exp: self.interner.intern("%hole"),
            arm: self.interner.intern("%hole-arm"),
            arm_var: self.interner.intern("%arm"),
            tag: self.interner.intern("%hole-tag"),
        };
        let mut around: Option<FxError> = None;
        for form in forms {
            let mut form = form.clone();
            let Some(at) = mark_hole(&mut form, &self.interner, holes.exp) else { continue };
            self.holes = Some(holes);
            self.hole_hint = None;
            let error = self.try_top(&form, |_, r| r.err());
            self.holes = None;
            if let Some(hint) = self.hole_hint.take() {
                return Some(hint);
            }
            // The shape the form around the hole must have, if what the
            // checker refused is around it.
            // The texts agree up to the hole, so the refusal that starts
            // nearest it is of the innermost form.
            if let Some(e) = error.filter(|e| e.span.start <= at.start && at.end <= e.span.end)
                && around.as_ref().is_none_or(|a| e.span.start > a.span.start)
            {
                around = Some(e);
            }
        }
        around.map(|e| e.message.strip_prefix("expected ").unwrap_or(&e.message).to_string())
    }

    /// If `e` is the hole, say what it must be (`expected`, if checked
    /// against a type) and stop checking there.
    pub(crate) fn at_hole(&mut self, e: crate::ast::ExpId, expected: Option<TyId>) -> R<()> {
        use crate::ast::{Exp, Ty};
        let Some(h) = self.holes else { return Ok(()) };
        let tags = |c: &Checker, vs: &[(Sym, TyId)]| vs.iter().map(|(l, t)| format!("`{}` ({})", c.interner.name(*l), c.show_ty(*t))).collect::<Vec<_>>().join(", ");
        let hint = match self.arena.exp_at(e).clone() {
            Exp::Var(s) if s == h.exp => match expected {
                Some(t) => format!("an expression of type {}", self.show_ty(t)),
                None => "an expression".to_string(),
            },
            Exp::Var(s) if s == h.arm => match self.lookup(h.arm_var).map(|t| self.arena.get(t).clone()) {
                Some(Ty::Sum(rest)) if rest.is_empty() => "nothing: every tag has an arm".to_string(),
                Some(Ty::Sum(rest)) => format!("an arm `(tag name body …)` for {}, or `(else name body …)`", tags(self, &rest)),
                _ => "an arm `(tag name body …)`, or `(else name body …)`".to_string(),
            },
            Exp::Sum(tag, _) if tag == h.tag => match expected.map(|t| self.arena.get(t).clone()) {
                Some(Ty::Sum(vs)) => format!("a tag, then its value: {}", tags(self, &vs)),
                _ => "a tag, then an expression".to_string(),
            },
            _ => return Ok(()),
        };
        self.hole_hint = Some(hint);
        Err(FxError::at(self.arena.span_of(e), "the hole"))
    }
}

/// The words FX-26 reserves: syntax, and the parts of descriptions.
pub const KEYWORDS: &[&str] = &[
    "lambda", "plambda", "proj", "if", "letrec", "let", "begin", "define", "define*", "define-type", "define-generative",
    "subr", "poly", "ref", "pairof", "dletrec", "void", "pure", "maxeff", "read", "write",
    "alloc", "goto", "comefrom", "region", "effect", "type", "prompt", "prompt-tag",
    "composable", "mark-key", "listof", "cond", "case", "else", "and", "or", "let*", "define-effect", "module-parameters", "the",
    "bloblet", "fields", "frozen", "arrayof", "icell", "await", "define-rec", "letrena", "letreap", "rlambda", "quote", "productof", "sumof", "product", "extract", "sum", "tagcase", "module", "moduleof", "with", "select", "load-module",
    "define-datatype", "make-bloblet", "bloblet-ref", "bloblet-set!", "bloblet-freeze", "bloblet-byte",
    "bloblet-set-byte!", "bloblet-bytes", "rmake-bloblet", "dlambda", "=>",
];

