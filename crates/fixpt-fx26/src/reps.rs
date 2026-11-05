//! The Rust checker's types as reps (`docs/research/heap-types.md`,
//! `TODO.md` §202, step 1): each type exported, a rep of it
//! ([`Checker::export_ty`]), and each rep imported, a type of this
//! checker's arena ([`Checker::import_rep`]). What a rep's heads are, and
//! what operands each takes, is said here, after the type syntax:
//!
//! | type | rep |
//! | --- | --- |
//! | `int` | `(base int)` |
//! | `void`, `nil`, `false` | `(void)`, `(nil)`, `(false)` |
//! | `(oneof T …)` | `(oneof T …)` |
//! | a variable | bound (`#n.p`), or a hole |
//! | `(subr C E (P …) Q spec)` | `(subr C E (params P …) Q)`, a spec after if it has one |
//! | `(poly ((x k) …) T)` | `(poly {x …} (binder k distinct [bound]) … T)` |
//! | `(ref T R)` | `(ref T R)` |
//! | `(pairof A B R)` | `(pairof A B R nil?)` |
//! | `(prompt-tag A H D R)` | `(prompt-tag A H D R)` |
//! | `(composable T A D R)` | `(composable T A D R once?)` |
//! | `(mark-key T R)` | `(mark-key T R)` |
//! | `(productof (l T) …)`, `(sumof …)` | `(productof l T …)`, `(sumof l T …)` |
//! | `(narrayof T N R)` | `(narrayof T N R)` |
//! | `(icell T R)`, `(place R)`, `(nat N)` | `(icell T R)`, `(place R)`, `(nat N)` |
//! | `(bloblet (fields T …) R)` | `(bloblet frozen? R T …)` |
//! | a generative type applied | `(named <g type key> d …)` |
//! | `(nlist T N)` | `(nlist T N R)` |
//! | `(moduleof (abs t k) … (desc d T) … (val x T) …)` | `(moduleof {t …} (binder k …) … (descs d T …) (vals x T …))` |
//! | `(select $k t)` | `(param-sel k t)` |
//! | `(dlambda ((x k) …) d)` | `(dlambda {x …} (binder k …) … d)` |
//! | `(f d …)` | `(app f d …)` |
//!
//! Effects are `(&effect atom …)`, a set node, so that equal effects have
//! one rep whatever order this checker keeps them in (a union's members
//! are in the order written); regions,
//! `(heap)`, `(rconst a)`, `(frozen acyclic? [place])`, `(global g)`,
//! `(globals)`, or a variable; sizes, `(finite)` or `(lin k (&terms (term v c) …))`;
//! descriptions, `(d-region R)`, `(d-effect E)`, `(d-type T)`, `(d-size N)`,
//! `(d-conv C)`, `(d-fun F)`; a specification, `(spec {p … r} requires
//! ensures)`, its names its binders', each formula a tree of `(true)`,
//! `(false)`, `(rel op a b)`, `(holds n)`, `(not f)`, `(and f …)`, `(or
//! f …)`, `(implies f g)` over `(lit k)`, `(atom n)`, `(add a b)`, `(sub a
//! b)`, `(mul a b)`.
//!
//! Not yet: an unresolved `(select m t)`, which is never compared. A
//! generative type is a constant keyed, for now, by its name and its place
//! in this checker's table: so within a session; its definition's stamp,
//! which lasts across them, is step 3's.

use crate::ast::{Atom, Conv, DVar, D, EArg, Effect, Kind, Named, Region, Size, Spec, Ty, TyId};
use crate::check::Checker;
use crate::logic::{Expr, Formula};
use fixpt_reps::{Arg, Builder, Const, Node, Rep};
use std::collections::HashMap;

/// A type exported: its rep, and the variables its holes are, in order.
/// The head of a `.fasl`'s definitions' types' rep's root
/// ([`Checker::export_tys`]).
pub const FASL_TYPES: &str = "fasl-types";

pub struct Exported {
    pub rep: Rep,
    pub holes: Vec<DVar>,
}

impl Checker {
    /// Type `t` as a rep; or why not (`reps.rs`, "Not yet").
    pub fn export_ty(&self, t: TyId) -> Result<Exported, String> {
        self.export_with(|ex| ex.ty(t))
    }

    /// A piece of evidence as a rep (`fixpt_reps::fill`): its root an
    /// `evidence` node of one operand, what `d` is, a type, an effect or a
    /// region, as the checker written in FX-26 makes one
    /// (`k-evidence-rep`).
    pub fn export_evidence(&self, d: &crate::ast::D) -> Result<Exported, String> {
        use crate::ast::D;
        self.export_with(|ex| {
            let of = match d {
                D::Type(t) => Arg::Node(ex.ty(*t)?),
                D::Effect(e) => ex.effect(e)?,
                D::Region(r) => ex.region(*r),
                _ => return Err("evidence of neither a type, an effect nor a region".into()),
            };
            Ok(ex.b.add(fixpt_reps::fill::EVIDENCE, &[], vec![of]))
        })
    }

    /// Types `ts` as one rep, its root a `fasl-types` node of each, in order:
    /// what they share there once (a `.fasl`'s definitions' types,
    /// `docs/research/heap-types.md`, step 5).
    pub fn export_tys(&self, ts: &[TyId]) -> Result<Exported, String> {
        self.export_with(|ex| {
            let args = ts.iter().map(|t| ex.ty(*t).map(Arg::Node)).collect::<Result<Vec<_>, _>>()?;
            Ok(ex.b.add(FASL_TYPES, &[], args))
        })
    }

    fn export_with(&self, root: impl FnOnce(&mut Ex) -> Result<u32, String>) -> Result<Exported, String> {
        let mut ex = Ex { c: self, b: Builder::new(), memo: HashMap::new(), gendefs: HashMap::new(), scope: Vec::new(), holes: HashMap::new(), hole_vars: Vec::new() };
        let root = root(&mut ex)?;
        let Ex { b, hole_vars, .. } = ex;
        let finished = b.finish(root)?;
        let mut holes = vec![DVar(0); finished.rep.holes.len()];
        for (k, at) in finished.holes.iter().enumerate() {
            if let Some(at) = at {
                holes[*at as usize] = hole_vars[k];
            }
        }
        Ok(Exported { rep: finished.rep, holes })
    }

    /// Rep `rep` as a type of this checker's arena, its holes the variables
    /// `holes`; or why not: a head or an operand it does not know, or a
    /// constant not of this checker.
    /// Each type of a rep [`export_tys`](Checker::export_tys) made, in order:
    /// its holes none, the generative types it names this checker's (none
    /// made).
    pub fn import_reps(&mut self, rep: &Rep) -> Result<Vec<TyId>, String> {
        let n = rep.nodes.first().map_or(0, |r| r.args.len());
        (0..n).map(|i| self.import_rep_part(rep, i, &[])).collect()
    }

    /// The root's operand `i` of a rep [`export_tys`](Checker::export_tys)
    /// made, the type of each `(j, t)` of `seeds` given: the root's operand
    /// `j` is `t` (an abbreviation's own type, where the rep has it), so that
    /// what has it is that type, as a type written naming it is.
    pub fn import_rep_part(&mut self, rep: &Rep, i: usize, seeds: &[(usize, TyId)]) -> Result<TyId, String> {
        let root = &rep.nodes[rep.root() as usize];
        if rep.name(root.head) != FASL_TYPES || !rep.holes.is_empty() {
            return Err("not a `.fasl`'s types".into());
        }
        let gens: HashMap<u64, u32> = (0..self.generatives.len() as u32).map(|w| (generative_key(self, w), w)).collect();
        let before = self.generatives.len();
        let mut im = Im { c: self, rep, holes: &[], gens, done: vec![None; rep.nodes.len()], links: vec![None; rep.nodes.len()], busy: vec![false; rep.nodes.len()], bound: HashMap::new() };
        for (j, t) in seeds {
            let k = Im::child(*root.args.get(*j).ok_or("a seed past the rep's types")?)?;
            im.done[k as usize] = Some(*t);
        }
        let t = Im::child(*root.args.get(i).ok_or("no such type in the rep")?).and_then(|k| im.ty(k));
        if self.generatives.len() != before {
            self.generatives.truncate(before);
            return Err("it names a generative type not here".into());
        }
        t
    }

    /// A rep, its holes none, as a description: an effect if it is evidence
    /// of one (`fixpt_reps::fill::part`), else the type it is or is evidence
    /// of; as the checker written in FX-26's `k-rep-desc`.
    pub fn import_desc(&mut self, rep: &Rep) -> Result<crate::ast::D, String> {
        use crate::ast::D;
        let root = &rep.nodes[rep.root() as usize];
        if rep.name(root.head) != fixpt_reps::fill::EVIDENCE {
            return self.import_rep(rep, &[]).map(D::Type);
        }
        let gens: HashMap<u64, u32> = (0..self.generatives.len() as u32).map(|w| (generative_key(self, w), w)).collect();
        let a = *root.args.first().ok_or("evidence of nothing")?;
        let mut im = Im { c: self, rep, holes: &[], gens, done: vec![None; rep.nodes.len()], links: vec![None; rep.nodes.len()], busy: vec![false; rep.nodes.len()], bound: HashMap::new() };
        let k = Im::child(a)?;
        if rep.name(rep.nodes[k as usize].head) == "effect" {
            im.effect(a).map(D::Effect)
        } else {
            im.ty(k).map(D::Type)
        }
    }

    pub fn import_rep(&mut self, rep: &Rep, holes: &[DVar]) -> Result<TyId, String> {
        if holes.len() != rep.holes.len() {
            return Err(format!("{} holes, {} variables given", rep.holes.len(), holes.len()));
        }
        let gens: HashMap<u64, u32> = (0..self.generatives.len() as u32).map(|w| (generative_key(self, w), w)).collect();
        let mut im = Im { c: self, rep, holes, gens, done: vec![None; rep.nodes.len()], links: vec![None; rep.nodes.len()], busy: vec![false; rep.nodes.len()], bound: HashMap::new() };
        im.ty(0)
    }
}

impl Checker {
    /// Type `t` printed whole, no abbreviation naming any part of it: what
    /// it is, whatever node it is (an abbreviation is found by the node
    /// for some types, `same_ty`), for comparing a type with its rep's
    /// import.
    pub fn show_ty_expanded(&mut self, t: TyId) -> String {
        let named = std::mem::take(&mut self.closed_named);
        let was = self.print_expanded.replace(true);
        let shown = self.show_ty(t);
        self.print_expanded.set(was);
        self.closed_named = named;
        shown
    }
}

/// A generative type's key (`reps.rs`, "Not yet"): its name and its place.
fn generative_key(c: &Checker, which: u32) -> u64 {
    fixpt_reps::generative_key(c.interner.name(c.generatives[which as usize].name), which)
}

fn kind_name(k: Kind) -> &'static str {
    match k {
        Kind::Region => "region",
        Kind::Place => "place",
        Kind::Effect => "effect",
        Kind::Type => "type",
        Kind::Data => "data",
        Kind::Sendable => "sendable",
        Kind::Flat => "flat",
        Kind::Size => "size",
        Kind::Conv => "conv",
        Kind::Arrow(_) => "=>",
    }
}

struct Ex<'c> {
    c: &'c Checker,
    b: Builder,
    memo: HashMap<TyId, u32>,
    /// Each generative type's definition's slot, once made (`gendef`).
    gendefs: HashMap<u32, u32>,
    /// The variables bound where the walk is, outermost first: each its
    /// binder's slot and place.
    scope: Vec<(DVar, u32, u32)>,
    holes: HashMap<DVar, Arg>,
    hole_vars: Vec<DVar>,
}

impl Ex<'_> {
    fn node(&mut self, head: &str, args: Vec<Arg>) -> Arg {
        Arg::Node(self.b.add(head, &[], args))
    }

    fn sym(&mut self, s: fixpt_read::Sym) -> Arg {
        let i = self.b.name(self.c.interner.name(s));
        Arg::Sym(i)
    }

    /// Variable `v`: bound, by its binder; else a hole, one for it.
    fn var(&mut self, v: DVar) -> Arg {
        if let Some(&(_, binder, pos)) = self.scope.iter().rev().find(|(w, _, _)| *w == v) {
            return Arg::Bound { binder, pos };
        }
        if let Some(&h) = self.holes.get(&v) {
            return h;
        }
        let h = self.b.hole(self.c.interner.name(self.c.arena.dvar_name(v)));
        self.holes.insert(v, h);
        self.hole_vars.push(v);
        h
    }

    fn kind(&mut self, k: Kind) -> Arg {
        match self.c.arena.arrow_parts(k) {
            Some((params, result)) => {
                let (params, result) = (params.to_vec(), result);
                let mut args: Vec<Arg> = params.iter().map(|p| self.kind(*p)).collect();
                args.push(self.kind(result));
                self.node("=>", args)
            }
            None => self.node(kind_name(k), vec![]),
        }
    }

    /// Binders `bs`, bound by node `slot`, in scope; their nodes.
    fn binders(&mut self, slot: u32, bs: &[(DVar, Kind)]) -> Vec<Arg> {
        for (pos, (v, _)) in bs.iter().enumerate() {
            self.scope.push((*v, slot, pos as u32));
        }
        bs.iter()
            .map(|(v, k)| {
                let kind = self.kind(*k);
                let mut args = vec![kind, Arg::Flag(self.c.arena.is_distinct(*v))];
                if let Some(b) = self.c.arena.bound(*v) {
                    args.push(self.region(b));
                }
                self.node("binder", args)
            })
            .collect()
    }

    /// Generative type `which`'s definition, for a checker that has not
    /// got it to make it (`heap-types.md`, §206): `(gendef {params}
    /// binder… (variances v…) rep)`, its parameters bound as a `poly`'s,
    /// each variance `+`, `-` or `=`, and its representation; once for
    /// each, so a recursive one's representation names it again.
    fn gendef(&mut self, which: u32) -> Result<u32, String> {
        if let Some(&slot) = self.gendefs.get(&which) {
            return Ok(slot);
        }
        let slot = self.b.reserve();
        self.gendefs.insert(which, slot);
        let g = &self.c.generatives[which as usize];
        let (params, variance, rep) = (g.params.clone(), g.variance.clone(), g.rep);
        let names = self.names_of(&params);
        let mark = self.scope.len();
        let mut args = self.binders(slot, &params);
        let vs = variance
            .iter()
            .map(|v| {
                let s = match v {
                    crate::ast::Variance::Co => "+",
                    crate::ast::Variance::Contra => "-",
                    crate::ast::Variance::Inv => "=",
                };
                Arg::Sym(self.b.name(s))
            })
            .collect();
        args.push(self.node("variances", vs));
        args.push(Arg::Node(self.ty(rep)?));
        self.scope.truncate(mark);
        let names: Vec<&str> = names.iter().map(String::as_str).collect();
        self.b.fill(slot, "gendef", &names, args);
        Ok(slot)
    }

    fn names_of(&self, bs: &[(DVar, Kind)]) -> Vec<String> {
        bs.iter().map(|(v, _)| self.c.interner.name(self.c.arena.dvar_name(*v)).to_string()).collect()
    }

    fn region(&mut self, r: Region) -> Arg {
        match r {
            Region::Var(v) => self.var(v),
            Region::Const(s) => {
                let s = self.sym(s);
                self.node("rconst", vec![s])
            }
            Region::Frozen(p, acyclic) => {
                let mut args = vec![Arg::Flag(acyclic)];
                if let Some(p) = p {
                    args.push(self.var(p));
                }
                self.node("frozen", args)
            }
            Region::Heap => self.node("heap", vec![]),
            Region::Global(g) => {
                let g = self.sym(g);
                self.node("global", vec![g])
            }
            Region::Globals => self.node("globals", vec![]),
        }
    }

    /// Effect `e`: a set node of its atoms, whose order the rep's canonical
    /// form makes (`fixpt_reps`'s sets), not this process's numbers.
    fn effect(&mut self, e: &Effect) -> Result<Arg, String> {
        let mut atoms = Vec::new();
        for a in &e.0 {
            let arg = match *a {
                Atom::Read(r) | Atom::Write(r) | Atom::Alloc(r) | Atom::Goto(r) | Atom::Comefrom(r) | Atom::Await(r) | Atom::Init(r) | Atom::Send(r) | Atom::Receive(r) => {
                    let head = match a {
                        Atom::Read(_) => "read",
                        Atom::Write(_) => "write",
                        Atom::Alloc(_) => "alloc",
                        Atom::Goto(_) => "goto",
                        Atom::Comefrom(_) => "comefrom",
                        Atom::Await(_) => "await",
                        Atom::Init(_) => "init",
                        Atom::Send(_) => "send",
                        _ => "receive",
                    };
                    let region = self.region(r);
                    self.node(head, vec![region])
                }
                Atom::Spin => self.node("spin", vec![]),
                Atom::Io(k) => {
                    let n = self.b.name(k.name());
                    self.node("io", vec![Arg::Sym(n)])
                }
                Atom::Nondet => self.node("nondet", vec![]),
                Atom::Stage => self.node("stage", vec![]),
                Atom::Var(v) => self.var(v),
                Atom::App(n) => {
                    let (head, args) = self.c.arena.effect_apps.parts(n);
                    let mut out = vec![self.var(head)];
                    for x in &args {
                        out.push(self.earg(x)?);
                    }
                    self.node("eapp", out)
                }
            };
            atoms.push(arg);
        }
        Ok(Arg::Node(self.b.add_set("effect", atoms)))
    }

    fn earg(&mut self, x: &EArg) -> Result<Arg, String> {
        Ok(match x {
            EArg::Region(r) => {
                let r = self.region(*r);
                self.node("e-region", vec![r])
            }
            EArg::Effect(e) => {
                let e = self.effect(e)?;
                self.node("e-effect", vec![e])
            }
            EArg::Size(s) => {
                let s = self.size(s);
                self.node("e-size", vec![s])
            }
            EArg::Conv(c) => {
                let c = self.conv(*c);
                self.node("e-conv", vec![c])
            }
        })
    }

    fn size(&mut self, s: &Size) -> Arg {
        match s {
            Size::Finite => self.node("finite", vec![]),
            Size::Lin { k, terms } => {
                let ts: Vec<Arg> = terms
                    .iter()
                    .map(|(v, c)| {
                        let v = self.var(*v);
                        self.node("term", vec![v, Arg::Int(*c)])
                    })
                    .collect();
                let ts = Arg::Node(self.b.add_set("terms", ts));
                self.node("lin", vec![Arg::Int(*k), ts])
            }
        }
    }

    fn conv(&mut self, c: Conv) -> Arg {
        match c {
            Conv::Cellular => self.node("cellular", vec![]),
            Conv::Native => self.node("native", vec![]),
            Conv::Fx => self.node("fx", vec![]),
            Conv::Var(v) => self.var(v),
        }
    }

    fn d(&mut self, d: &D) -> Result<Arg, String> {
        Ok(match d {
            D::Region(r) => {
                let r = self.region(*r);
                self.node("d-region", vec![r])
            }
            D::Effect(e) => {
                let e = self.effect(e)?;
                self.node("d-effect", vec![e])
            }
            D::Type(t) => {
                let t = self.ty(*t)?;
                self.node("d-type", vec![Arg::Node(t)])
            }
            D::Size(s) => {
                let s = self.size(s);
                self.node("d-size", vec![s])
            }
            D::Conv(c) => {
                let c = self.conv(*c);
                self.node("d-conv", vec![c])
            }
            D::Fun(t) => {
                let t = self.ty(*t)?;
                self.node("d-fun", vec![Arg::Node(t)])
            }
        })
    }

    fn parts(&mut self, ps: &[(fixpt_read::Sym, TyId)]) -> Result<Vec<Arg>, String> {
        let mut args = Vec::new();
        for (l, t) in ps {
            args.push(self.sym(*l));
            args.push(Arg::Node(self.ty(*t)?));
        }
        Ok(args)
    }

    fn spec(&mut self, s: &Spec) -> Result<Arg, String> {
        let req = self.formula(&s.requires)?;
        let ens = self.formula(&s.ensures)?;
        let name = |n: &Option<fixpt_read::Sym>| n.map_or(String::new(), |n| self.c.interner.name(n).to_string());
        let mut names: Vec<String> = s.params.iter().map(name).collect();
        names.push(name(&s.result));
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        Ok(Arg::Node(self.b.add("spec", &refs, vec![req, ens])))
    }

    fn formula(&mut self, f: &Formula<Named>) -> Result<Arg, String> {
        Ok(match f {
            Formula::True => self.node("true", vec![]),
            Formula::False => self.node("false", vec![]),
            Formula::Rel(op, a, b) => {
                let op = self.b.name(&format!("{op:?}").to_lowercase());
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                self.node("rel", vec![Arg::Sym(op), a, b])
            }
            Formula::Holds(n) => {
                let n = self.named(n)?;
                self.node("holds", vec![n])
            }
            Formula::Not(g) => {
                let g = self.formula(g)?;
                self.node("not", vec![g])
            }
            Formula::And(gs) | Formula::Or(gs) => {
                let head = if matches!(f, Formula::And(_)) { "and" } else { "or" };
                let args = gs.iter().map(|g| self.formula(g)).collect::<Result<_, _>>()?;
                self.node(head, args)
            }
            Formula::Implies(a, b) => {
                let (a, b) = (self.formula(a)?, self.formula(b)?);
                self.node("implies", vec![a, b])
            }
        })
    }

    fn expr(&mut self, e: &Expr<Named>) -> Result<Arg, String> {
        Ok(match e {
            Expr::Atom(n) => {
                let n = self.named(n)?;
                self.node("atom", vec![n])
            }
            Expr::Lit(k) => self.node("lit", vec![Arg::Int(*k)]),
            Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => {
                let head = match e {
                    Expr::Add(..) => "add",
                    Expr::Sub(..) => "sub",
                    _ => "mul",
                };
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                self.node(head, vec![a, b])
            }
        })
    }

    fn named(&mut self, n: &Named) -> Result<Arg, String> {
        let int = |i: usize| Arg::Int(i as i64);
        Ok(match n {
            Named::Param(i) => self.node("param", vec![int(*i)]),
            Named::Result => self.node("result", vec![]),
            Named::Length(i) => self.node("length", vec![int(*i)]),
            Named::Shape(i, j) => self.node("shape", vec![int(*i), int(*j)]),
            Named::Acyclic(i) => self.node("acyclic", vec![int(*i)]),
            Named::Nat(i) => self.node("nat", vec![int(*i)]),
            Named::LengthIs(i, j) => self.node("length-is", vec![int(*i), int(*j)]),
            Named::Call(f, args) => {
                let mut out = vec![self.sym(*f)];
                for a in args.iter() {
                    out.push(self.expr(a)?);
                }
                self.node("call", out)
            }
        })
    }

    /// Type `t`'s node.
    fn ty(&mut self, t: TyId) -> Result<u32, String> {
        let t = self.c.arena.resolve(t);
        if let Some(&slot) = self.memo.get(&t) {
            return Ok(slot);
        }
        let slot = self.b.reserve();
        self.memo.insert(t, slot);
        let ty = self.c.arena.get(t).clone();
        let (head, binders, args): (&str, Vec<String>, Vec<Arg>) = match ty {
            Ty::Base(s) => ("base", vec![], vec![self.sym(s)]),
            Ty::Void => ("void", vec![], vec![]),
            Ty::Nil => ("nil", vec![], vec![]),
            Ty::False => ("false", vec![], vec![]),
            Ty::Union(ms) => ("oneof", vec![], ms.iter().map(|m| self.ty(*m).map(Arg::Node)).collect::<Result<_, _>>()?),
            Ty::AllOf(ms) => ("allof", vec![], ms.iter().map(|m| self.ty(*m).map(Arg::Node)).collect::<Result<_, _>>()?),
            Ty::Var(v) => {
                // A variable standing as a type: as the `var` node over it.
                let v = self.var(v);
                ("var", vec![], vec![v])
            }
            Ty::Subr { conv, effect, params, result, spec } => {
                let conv = self.conv(conv);
                let effect = self.effect(&effect)?;
                let ps = params.iter().map(|p| self.ty(*p).map(Arg::Node)).collect::<Result<_, _>>()?;
                let ps = self.node("params", ps);
                let mut args = vec![conv, effect, ps, Arg::Node(self.ty(result)?)];
                if let Some(s) = spec {
                    args.push(self.spec(&s)?);
                }
                ("subr", vec![], args)
            }
            Ty::Poly { binders, body } => {
                let names = self.names_of(&binders);
                let mark = self.scope.len();
                let mut args = self.binders(slot, &binders);
                args.push(Arg::Node(self.ty(body)?));
                self.scope.truncate(mark);
                ("poly", names, args)
            }
            Ty::Ref(a, r) => ("ref", vec![], vec![Arg::Node(self.ty(a)?), self.region(r)]),
            Ty::Pair(a, b, r, nil) => ("pairof", vec![], vec![Arg::Node(self.ty(a)?), Arg::Node(self.ty(b)?), self.region(r), Arg::Flag(nil)]),
            Ty::PromptTag { answer, payload, effect, region } => {
                let (a, h) = (self.ty(answer)?, self.ty(payload)?);
                ("prompt-tag", vec![], vec![Arg::Node(a), Arg::Node(h), self.effect(&effect)?, self.region(region)])
            }
            Ty::Composable { arg, answer, effect, region, once } => {
                let (x, a) = (self.ty(arg)?, self.ty(answer)?);
                ("composable", vec![], vec![Arg::Node(x), Arg::Node(a), self.effect(&effect)?, self.region(region), Arg::Flag(once)])
            }
            Ty::MarkKey(a, r) => ("mark-key", vec![], vec![Arg::Node(self.ty(a)?), self.region(r)]),
            Ty::Product(ps) => ("productof", vec![], self.parts(&ps)?),
            Ty::Sum(ps) => ("sumof", vec![], self.parts(&ps)?),
            Ty::Array(a, n, r) => ("narrayof", vec![], vec![Arg::Node(self.ty(a)?), self.size(&n), self.region(r)]),
            Ty::ICell(a, r) => ("icell", vec![], vec![Arg::Node(self.ty(a)?), self.region(r)]),
            Ty::Place(r) => ("place", vec![], vec![self.region(r)]),
            Ty::Nat(n) => ("nat", vec![], vec![self.size(&n)]),
            Ty::Bloblet { fields, frozen, region } => {
                let mut args = vec![Arg::Flag(frozen), self.region(region)];
                for f in fields {
                    args.push(Arg::Node(self.ty(f)?));
                }
                ("bloblet", vec![], args)
            }
            Ty::Link(_) => return Err("a type not yet made (an empty link)".into()),
            Ty::Named { which, args } => {
                let g = &self.c.generatives[which as usize];
                let kind = if g.params.is_empty() { "type".to_string() } else { format!("generative/{}", g.params.len()) };
                let c = self.b.konst(Const { key: generative_key(self.c, which), name: self.c.interner.name(g.name).to_string(), kind });
                let def = self.gendef(which)?;
                let mut out = vec![c, Arg::Node(def)];
                for d in &args {
                    out.push(self.d(d)?);
                }
                ("named", vec![], out)
            }
            Ty::NList { elem, size, region } => ("nlist", vec![], vec![Arg::Node(self.ty(elem)?), self.size(&size), self.region(region)]),
            Ty::Module { abs, descs, vals } => {
                let bs: Vec<(DVar, Kind)> = abs.iter().map(|(_, v)| (*v, self.c.arena.dvar_kind_known(*v).unwrap_or(Kind::Type))).collect();
                let names = abs.iter().map(|(n, _)| self.c.interner.name(*n).to_string()).collect();
                let mark = self.scope.len();
                let mut args = self.binders(slot, &bs);
                let ds = self.parts(&descs)?;
                args.push(self.node("descs", ds));
                let vs = self.parts(&vals)?;
                args.push(self.node("vals", vs));
                self.scope.truncate(mark);
                ("moduleof", names, args)
            }
            Ty::Select(..) => return Err("an unresolved `select`, which is never compared".into()),
            Ty::ParamSel(k, n) => ("param-sel", vec![], vec![Arg::Int(k as i64), self.sym(n)]),
            Ty::Lam { params, body } => {
                let names = self.names_of(&params);
                let mark = self.scope.len();
                let mut args = self.binders(slot, &params);
                args.push(self.d(&body)?);
                self.scope.truncate(mark);
                ("dlambda", names, args)
            }
            Ty::App { fun, args } => {
                let mut out = vec![Arg::Node(self.ty(fun)?)];
                for d in &args {
                    out.push(self.d(d)?);
                }
                ("app", vec![], out)
            }
        };
        let refs: Vec<&str> = binders.iter().map(String::as_str).collect();
        // A union's members in the order written (`union_of` keeps it), not
        // a set: two orders of one union are two reps, which costs a cache
        // missed, never an answer, and prints as the program wrote it.
        self.b.fill(slot, head, &refs, args);
        Ok(slot)
    }
}

struct Im<'c, 'r> {
    c: &'c mut Checker,
    rep: &'r Rep,
    holes: &'r [DVar],
    gens: HashMap<u64, u32>,
    /// Each node's type, once made.
    done: Vec<Option<TyId>>,
    /// A node met again while it is being made (a cycle): the link that
    /// stands for it, filled once it is made.
    links: Vec<Option<TyId>>,
    busy: Vec<bool>,
    /// Each bound variable, by its binder's node and place.
    bound: HashMap<(u32, u32), DVar>,
}

impl Im<'_, '_> {
    fn node(&self, k: u32) -> &Node {
        &self.rep.nodes[k as usize]
    }
    fn head(&self, k: u32) -> &str {
        self.rep.name(self.node(k).head)
    }
    fn sym(&mut self, a: Arg) -> Result<fixpt_read::Sym, String> {
        match a {
            Arg::Sym(i) => Ok(self.c.interner.intern(self.rep.name(i))),
            other => Err(format!("a name expected, {other:?}")),
        }
    }
    fn child(a: Arg) -> Result<u32, String> {
        match a {
            Arg::Node(i) => Ok(i),
            other => Err(format!("a node expected, {other:?}")),
        }
    }
    fn flag(a: Arg) -> Result<bool, String> {
        match a {
            Arg::Flag(b) => Ok(b),
            other => Err(format!("a flag expected, {other:?}")),
        }
    }
    fn int(a: Arg) -> Result<i64, String> {
        match a {
            Arg::Int(k) => Ok(k),
            other => Err(format!("an integer expected, {other:?}")),
        }
    }

    fn var(&self, a: Arg) -> Result<DVar, String> {
        match a {
            Arg::Bound { binder, pos } => self.bound.get(&(binder, pos)).copied().ok_or_else(|| format!("variable {binder}.{pos} not bound")),
            Arg::Hole(i) => Ok(self.holes[i as usize]),
            other => Err(format!("a variable expected, {other:?}")),
        }
    }

    fn kind(&mut self, a: Arg) -> Result<Kind, String> {
        let k = Self::child(a)?;
        let args = self.node(k).args.clone();
        Ok(match self.head(k) {
            "region" => Kind::Region,
            "place" => Kind::Place,
            "effect" => Kind::Effect,
            "type" => Kind::Type,
            "data" => Kind::Data,
            "sendable" => Kind::Sendable,
            "flat" => Kind::Flat,
            "size" => Kind::Size,
            "conv" => Kind::Conv,
            "=>" => {
                let mut ks = args.iter().map(|x| self.kind(*x)).collect::<Result<Vec<_>, _>>()?;
                let result = ks.pop().ok_or("an arrow kind of no result")?;
                self.c.arena.arrow(ks, result)
            }
            other => return Err(format!("no kind `{other}`")),
        })
    }

    /// Node `k`'s binders made variables, bound; their kinds.
    /// A generative type this checker has not got, made from its
    /// definition, node `def` (`Ex::gendef`), under constant `c`'s key, so
    /// that every use of it in the rep is the one type.
    fn generative(&mut self, c: u32, def: u32) -> Result<u32, String> {
        let node = self.node(def).clone();
        let n = node.binders.len();
        let params = self.binders(def, n)?;
        let variances = self.node(Self::child(*node.args.get(n).ok_or("a generative type of no variances")?)?).args.clone();
        let variance = variances
            .iter()
            .map(|v| match *v {
                Arg::Sym(s) => match self.rep.name(s) {
                    "+" => Ok(crate::ast::Variance::Co),
                    "-" => Ok(crate::ast::Variance::Contra),
                    "=" => Ok(crate::ast::Variance::Inv),
                    other => Err(format!("a variance `{other}`")),
                },
                other => Err(format!("a variance expected, {other:?}")),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let k = &self.rep.consts[c as usize];
        let (key, name) = (k.key, self.c.interner.intern(&k.name));
        let which = self.c.generatives.len() as u32;
        let slot = self.c.arena.ty(Ty::Link(None));
        self.c.generatives.push(crate::check::Generative { name, params, variance, rep: slot });
        self.gens.insert(key, which);
        let rep = self.ty(Self::child(*node.args.get(n + 1).ok_or("a generative type of no representation")?)?)?;
        self.c.arena.set_link(slot, rep);
        Ok(which)
    }

    fn binders(&mut self, k: u32, n: usize) -> Result<Vec<(DVar, Kind)>, String> {
        let node = self.node(k).clone();
        if node.binders.len() != n || node.args.len() < n {
            return Err(format!("node {k}: {} binders, {n} wanted", node.binders.len()));
        }
        let mut out = Vec::new();
        // The variables first, then their kinds and bounds, which may name
        // each other.
        for (pos, &b) in node.binders.iter().enumerate() {
            let name = self.c.interner.intern(self.rep.name(b));
            let bk = Self::child(node.args[pos])?;
            let kind = self.kind(self.node(bk).args.first().copied().ok_or("a binder of no kind")?)?;
            let v = self.c.arena.dvar_of(name, kind);
            self.bound.insert((k, pos as u32), v);
            out.push((v, kind));
        }
        for (pos, (v, _)) in out.iter().enumerate() {
            let bk = Self::child(node.args[pos])?;
            let args = self.node(bk).args.clone();
            if args.get(1).copied().map(Self::flag).transpose()?.unwrap_or(false) {
                self.c.arena.set_distinct(*v);
            }
            if let Some(r) = args.get(2) {
                let r = self.region(*r)?;
                self.c.arena.set_bound(*v, r);
            }
        }
        Ok(out)
    }

    fn region(&mut self, a: Arg) -> Result<Region, String> {
        if matches!(a, Arg::Bound { .. } | Arg::Hole(_)) {
            return Ok(Region::Var(self.var(a)?));
        }
        let k = Self::child(a)?;
        let args = self.node(k).args.clone();
        Ok(match self.head(k) {
            "rconst" => Region::Const(self.sym(args[0])?),
            "frozen" => Region::Frozen(args.get(1).map(|p| self.var(*p)).transpose()?, Self::flag(args[0])?),
            "heap" => Region::Heap,
            "global" => Region::Global(self.sym(args[0])?),
            "globals" => Region::Globals,
            other => return Err(format!("no region `{other}`")),
        })
    }

    fn effect(&mut self, a: Arg) -> Result<Effect, String> {
        let k = Self::child(a)?;
        if self.head(k) != "effect" {
            return Err(format!("an effect expected, `{}`", self.head(k)));
        }
        let mut e = Effect::pure();
        for x in self.node(k).args.clone() {
            if matches!(x, Arg::Bound { .. } | Arg::Hole(_)) {
                e.0.insert(Atom::Var(self.var(x)?));
                continue;
            }
            let n = Self::child(x)?;
            let args = self.node(n).args.clone();
            let atom = match self.head(n) {
                "read" => Atom::Read(self.region(args[0])?),
                "write" => Atom::Write(self.region(args[0])?),
                "alloc" => Atom::Alloc(self.region(args[0])?),
                "goto" => Atom::Goto(self.region(args[0])?),
                "comefrom" => Atom::Comefrom(self.region(args[0])?),
                "await" => Atom::Await(self.region(args[0])?),
                "init" => Atom::Init(self.region(args[0])?),
                "send" => Atom::Send(self.region(args[0])?),
                "receive" => Atom::Receive(self.region(args[0])?),
                "spin" => Atom::Spin,
                "io" => {
                    let Arg::Sym(i) = args[0] else { return Err("an I/O kind expected".into()) };
                    Atom::Io(crate::ast::IoKind::named(self.rep.name(i)).ok_or("no such I/O kind")?)
                }
                "nondet" => Atom::Nondet,
                "stage" => Atom::Stage,
                "eapp" => {
                    let head = self.var(args[0])?;
                    let eargs = args[1..].iter().map(|x| self.earg(*x)).collect::<Result<Vec<_>, _>>()?;
                    self.c.arena.effect_apps.atom(head, eargs)
                }
                other => return Err(format!("no atom `{other}`")),
            };
            e.0.insert(atom);
        }
        Ok(e)
    }

    fn earg(&mut self, a: Arg) -> Result<EArg, String> {
        let k = Self::child(a)?;
        let x = *self.node(k).args.first().ok_or("an effect's argument of nothing")?;
        Ok(match self.head(k) {
            "e-region" => EArg::Region(self.region(x)?),
            "e-effect" => EArg::Effect(self.effect(x)?),
            "e-size" => EArg::Size(self.size(x)?),
            "e-conv" => EArg::Conv(self.conv(x)?),
            other => return Err(format!("no effect argument `{other}`")),
        })
    }

    fn size(&mut self, a: Arg) -> Result<Size, String> {
        let k = Self::child(a)?;
        let args = self.node(k).args.clone();
        Ok(match self.head(k) {
            "finite" => Size::Finite,
            "lin" => {
                let c0 = Self::int(args[0])?;
                let ts = Self::child(*args.get(1).ok_or("a size of no terms")?)?;
                let mut terms = Vec::new();
                for t in self.node(ts).args.clone() {
                    let parts = self.node(Self::child(t)?).args.clone();
                    terms.push((self.var(parts[0])?, Self::int(*parts.get(1).ok_or("a term of no coefficient")?)?));
                }
                terms.sort_by_key(|(v, _)| *v);
                Size::Lin { k: c0, terms }
            }
            other => return Err(format!("no size `{other}`")),
        })
    }

    fn conv(&mut self, a: Arg) -> Result<Conv, String> {
        if matches!(a, Arg::Bound { .. } | Arg::Hole(_)) {
            return Ok(Conv::Var(self.var(a)?));
        }
        let k = Self::child(a)?;
        Ok(match self.head(k) {
            "cellular" => Conv::Cellular,
            "native" => Conv::Native,
            "fx" => Conv::Fx,
            other => return Err(format!("no convention `{other}`")),
        })
    }

    fn d(&mut self, a: Arg) -> Result<D, String> {
        let k = Self::child(a)?;
        let x = *self.node(k).args.first().ok_or("a description of nothing")?;
        Ok(match self.head(k) {
            "d-region" => D::Region(self.region(x)?),
            "d-effect" => D::Effect(self.effect(x)?),
            "d-type" => D::Type(self.ty(Self::child(x)?)?),
            "d-size" => D::Size(self.size(x)?),
            "d-conv" => D::Conv(self.conv(x)?),
            "d-fun" => D::Fun(self.ty(Self::child(x)?)?),
            other => return Err(format!("no description `{other}`")),
        })
    }

    fn parts(&mut self, args: &[Arg]) -> Result<Vec<(fixpt_read::Sym, TyId)>, String> {
        args.chunks(2)
            .map(|p| {
                let l = self.sym(p[0])?;
                let t = self.ty(Self::child(*p.get(1).ok_or("a label of no type")?)?)?;
                Ok((l, t))
            })
            .collect()
    }

    fn spec(&mut self, k: u32) -> Result<Spec, String> {
        let node = self.node(k).clone();
        let names: Vec<Option<fixpt_read::Sym>> = node.binders.iter().map(|&b| Some(self.rep.name(b)).filter(|n| !n.is_empty()).map(|n| self.c.interner.intern(n))).collect();
        let (result, params) = names.split_last().ok_or("a spec of no names")?;
        Ok(Spec {
            params: params.to_vec(),
            result: *result,
            requires: self.formula(node.args[0])?,
            ensures: self.formula(node.args[1])?,
        })
    }

    fn formula(&mut self, a: Arg) -> Result<Formula<Named>, String> {
        let k = Self::child(a)?;
        let args = self.node(k).args.clone();
        Ok(match self.head(k) {
            "true" => Formula::True,
            "false" => Formula::False,
            "rel" => {
                let Arg::Sym(op) = args[0] else { return Err("a relation expected".into()) };
                let op = match self.rep.name(op) {
                    "lt" => crate::ast::Rel::Lt,
                    "le" => crate::ast::Rel::Le,
                    "eq" => crate::ast::Rel::Eq,
                    "ne" => crate::ast::Rel::Ne,
                    other => return Err(format!("no relation `{other}`")),
                };
                Formula::Rel(op, self.expr(args[1])?, self.expr(args[2])?)
            }
            "holds" => Formula::Holds(self.named(args[0])?),
            "not" => Formula::Not(Box::new(self.formula(args[0])?)),
            "and" => Formula::And(args.iter().map(|x| self.formula(*x)).collect::<Result<_, _>>()?),
            "or" => Formula::Or(args.iter().map(|x| self.formula(*x)).collect::<Result<_, _>>()?),
            "implies" => Formula::Implies(Box::new(self.formula(args[0])?), Box::new(self.formula(args[1])?)),
            other => return Err(format!("no formula `{other}`")),
        })
    }

    fn expr(&mut self, a: Arg) -> Result<Expr<Named>, String> {
        let k = Self::child(a)?;
        let args = self.node(k).args.clone();
        Ok(match self.head(k) {
            "atom" => Expr::Atom(self.named(args[0])?),
            "lit" => Expr::Lit(Self::int(args[0])?),
            "add" => Expr::Add(Box::new(self.expr(args[0])?), Box::new(self.expr(args[1])?)),
            "sub" => Expr::Sub(Box::new(self.expr(args[0])?), Box::new(self.expr(args[1])?)),
            "mul" => Expr::Mul(Box::new(self.expr(args[0])?), Box::new(self.expr(args[1])?)),
            other => return Err(format!("no expression `{other}`")),
        })
    }

    fn named(&mut self, a: Arg) -> Result<Named, String> {
        let k = Self::child(a)?;
        let args = self.node(k).args.clone();
        let at = |i: usize| -> Result<usize, String> { Self::int(*args.get(i).ok_or("an operand missing")?).map(|v| v as usize) };
        Ok(match self.head(k) {
            "param" => Named::Param(at(0)?),
            "result" => Named::Result,
            "length" => Named::Length(at(0)?),
            "shape" => Named::Shape(at(0)?, at(1)?),
            "acyclic" => Named::Acyclic(at(0)?),
            "nat" => Named::Nat(at(0)?),
            "length-is" => Named::LengthIs(at(0)?, at(1)?),
            "call" => {
                let f = self.sym(args[0])?;
                let es = args[1..].iter().map(|x| self.expr(*x)).collect::<Result<Vec<_>, _>>()?;
                Named::Call(f, std::rc::Rc::new(es))
            }
            other => return Err(format!("no name `{other}`")),
        })
    }

    /// Node `k`'s type.
    fn ty(&mut self, k: u32) -> Result<TyId, String> {
        if let Some(t) = self.done[k as usize] {
            return Ok(t);
        }
        if self.busy[k as usize] {
            // A cycle: a link for it now, filled when it is made.
            let link = *self.links[k as usize].get_or_insert_with(|| self.c.arena.ty(Ty::Link(None)));
            return Ok(link);
        }
        self.busy[k as usize] = true;
        let node = self.node(k).clone();
        let args = node.args.clone();
        let arg = |i: usize| -> Result<Arg, String> { args.get(i).copied().ok_or_else(|| format!("node {k}: operand {i} missing")) };
        let ty = match self.head(k).to_string().as_str() {
            "base" => Ty::Base(self.sym(arg(0)?)?),
            "void" => Ty::Void,
            "nil" => Ty::Nil,
            "false" => Ty::False,
            "oneof" | "union" | "anyof" => Ty::Union(args.iter().map(|x| self.ty(Self::child(*x)?)).collect::<Result<_, _>>()?),
            "allof" => Ty::AllOf(args.iter().map(|x| self.ty(Self::child(*x)?)).collect::<Result<_, _>>()?),
            "var" => Ty::Var(self.var(arg(0)?)?),
            "subr" => {
                let conv = self.conv(arg(0)?)?;
                let effect = self.effect(arg(1)?)?;
                let ps = Self::child(arg(2)?)?;
                let params = self.node(ps).args.clone().iter().map(|x| self.ty(Self::child(*x)?)).collect::<Result<_, _>>()?;
                let result = self.ty(Self::child(arg(3)?)?)?;
                let spec = match args.get(4) {
                    Some(s) => Some(std::rc::Rc::new(self.spec(Self::child(*s)?)?)),
                    None => None,
                };
                Ty::Subr { conv, effect, params, result, spec }
            }
            "poly" => {
                let n = node.binders.len();
                let binders = self.binders(k, n)?;
                let body = self.ty(Self::child(arg(n)?)?)?;
                Ty::Poly { binders, body }
            }
            "ref" => Ty::Ref(self.ty(Self::child(arg(0)?)?)?, self.region(arg(1)?)?),
            "pairof" => Ty::Pair(self.ty(Self::child(arg(0)?)?)?, self.ty(Self::child(arg(1)?)?)?, self.region(arg(2)?)?, Self::flag(arg(3)?)?),
            "prompt-tag" => Ty::PromptTag {
                answer: self.ty(Self::child(arg(0)?)?)?,
                payload: self.ty(Self::child(arg(1)?)?)?,
                effect: self.effect(arg(2)?)?,
                region: self.region(arg(3)?)?,
            },
            "composable" => Ty::Composable {
                arg: self.ty(Self::child(arg(0)?)?)?,
                answer: self.ty(Self::child(arg(1)?)?)?,
                effect: self.effect(arg(2)?)?,
                region: self.region(arg(3)?)?,
                once: Self::flag(arg(4)?)?,
            },
            "mark-key" => Ty::MarkKey(self.ty(Self::child(arg(0)?)?)?, self.region(arg(1)?)?),
            "productof" => Ty::Product(self.parts(&args)?),
            "sumof" => Ty::Sum(self.parts(&args)?),
            "narrayof" => Ty::Array(self.ty(Self::child(arg(0)?)?)?, self.size(arg(1)?)?, self.region(arg(2)?)?),
            "icell" => Ty::ICell(self.ty(Self::child(arg(0)?)?)?, self.region(arg(1)?)?),
            "place" => Ty::Place(self.region(arg(0)?)?),
            "nat" => Ty::Nat(self.size(arg(0)?)?),
            "bloblet" => {
                let frozen = Self::flag(arg(0)?)?;
                let region = self.region(arg(1)?)?;
                let fields = args[2..].iter().map(|x| self.ty(Self::child(*x)?)).collect::<Result<_, _>>()?;
                Ty::Bloblet { fields, frozen, region }
            }
            "named" => {
                let Arg::Const(c) = arg(0)? else { return Err("a generative type expected".into()) };
                let key = self.rep.consts[c as usize].key;
                let which = match self.gens.get(&key) {
                    Some(&w) => w,
                    None => self.generative(c, Self::child(arg(1)?)?)?,
                };
                let ds = args[2..].iter().map(|x| self.d(*x)).collect::<Result<_, _>>()?;
                Ty::Named { which, args: ds }
            }
            "nlist" => Ty::NList { elem: self.ty(Self::child(arg(0)?)?)?, size: self.size(arg(1)?)?, region: self.region(arg(2)?)? },
            "moduleof" => {
                let n = node.binders.len();
                let bs = self.binders(k, n)?;
                let abs = node.binders.iter().zip(&bs).map(|(&l, (v, _))| (self.c.interner.intern(self.rep.name(l)), *v)).collect();
                let descs = self.node(Self::child(arg(n)?)?).args.clone();
                let descs = self.parts(&descs)?;
                let vals = self.node(Self::child(arg(n + 1)?)?).args.clone();
                let vals = self.parts(&vals)?;
                Ty::Module { abs, descs, vals }
            }
            "param-sel" => Ty::ParamSel(Self::int(arg(0)?)? as usize, self.sym(arg(1)?)?),
            "dlambda" => {
                let n = node.binders.len();
                let params = self.binders(k, n)?;
                let body = self.d(arg(n)?)?;
                Ty::Lam { params, body }
            }
            "app" => {
                let fun = self.ty(Self::child(arg(0)?)?)?;
                let ds = args[1..].iter().map(|x| self.d(*x)).collect::<Result<_, _>>()?;
                Ty::App { fun, args: ds }
            }
            other => return Err(format!("no type `{other}`")),
        };
        // A base type is the standard environment's own, as its name read
        // makes it: rules that know one by its id (`self.int`) take it.
        let standard = match &ty {
            Ty::Base(s) => self.c.base.get(s).copied(),
            _ => None,
        };
        let t = standard.unwrap_or_else(|| self.c.arena.ty(ty));
        let t = match self.links[k as usize] {
            Some(link) => {
                self.c.arena.set_link(link, t);
                link
            }
            None => t,
        };
        self.busy[k as usize] = false;
        self.done[k as usize] = Some(t);
        Ok(t)
    }
}
