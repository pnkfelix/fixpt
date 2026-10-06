//! The middle phase's procedure table (`docs/research/compiler-middle-phase.md`,
//! step 2): before a top-level form is compiled, each lambda it makes, and
//! each `letrec`'s lifting, decided by a walk of its own: what a lambda's
//! closure captures, its own name, and whether a `letrec` is lifted, with
//! the names each member then takes first. The walk keeps the stack
//! compiler's scoping, arm for arm, in environments whose places are only
//! their kinds (a slot, a free value, a sibling not made yet, a loop, a
//! lifted procedure); the decisions are the compiler's own (`captured`,
//! `lift_plan`, `loops_only`). Lambdas only register code compiles (an
//! inlined body, a specialized copy) are not in it: their context is not
//! the tree's (step 3).

use super::{Compiler, Env, Lift, Loc};
use crate::ast::{ArmBind, Exp, ExpId, ModItem};
use fixpt_heap::Value;
use fixpt_read::Sym;
use std::collections::HashMap;

/// A lambda as the walk decided it: its parameters, the name it is bound to
/// in its `letrec` or module, and the names its closure captures, in order.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Planned {
    pub params: Vec<Sym>,
    pub own: Option<Sym>,
    pub fv: Vec<Sym>,
}

/// A form's procedures, by where their bodies are and their parameters (the
/// lambdas a form expands to, a `define-datatype`'s constructors, share its
/// place; their parameters tell them apart); and each `letrec`'s lifting, by
/// where it is (as `lifted` keeps it): the names each member takes first, or
/// none if it is not lifted. As the FX-26 compiler's `c-plan-procs`, whose
/// trees, frozen data, have no identity to key by.
#[derive(Default)]
pub(crate) struct Plan {
    pub procs: HashMap<((u32, u32, u32), Vec<Sym>), Planned>,
    pub lifts: HashMap<(u32, u32, u32), Option<Vec<Vec<Sym>>>>,
    /// Each call of a global, by where it is (step 3): what register code
    /// may do with it.
    pub calls: HashMap<(u32, u32, u32), Called>,
    /// The bodies its calls inline, each planned as register code compiles
    /// it there (3b), by `inlines`'s index: once for every call of it here,
    /// what it decides depending on the callee and the path to it, not on
    /// the call.
    pub inlined: HashMap<usize, Plan>,
}

/// A call of a global, as planned: the small procedure it may be inlined
/// as (`inlines`'s index), and the procedure it may be specialized as with
/// the lambda argument (`specials`'s index, and the lambda).
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct Called {
    pub inline: Option<usize>,
    pub special: Option<(usize, ExpId)>,
}

/// A slot, as the walk's environments say where a name is: only its kind
/// counts.
const SLOT: Loc = Loc::Slot(0);

impl Compiler<'_> {
    fn span_key(&self, x: ExpId) -> (u32, u32, u32) {
        let s = self.c.arena.span_of(x);
        (s.file.0, s.start, s.end)
    }

    /// The plan of top-level form `x`, compiled next, in no environment.
    /// The lifted procedures it would make are counted as the compile will
    /// make them, and forgotten after.
    pub(crate) fn plan_top(&mut self, x: ExpId) -> Plan {
        let mut plan = Plan::default();
        let lifts = self.lifts.len();
        self.plan_exp(x, &Vec::new(), false, &mut plan);
        self.lifts.truncate(lifts);
        plan
    }

    fn plan_exps(&mut self, xs: &[ExpId], e: &Env, plan: &mut Plan) {
        for x in xs {
            self.plan_exp(*x, e, false, plan);
        }
    }

    /// As `exp`: a conversion or a reshaping compiles the value as it is,
    /// not in tail position.
    fn plan_exp(&mut self, x: ExpId, e: &Env, tail: bool, plan: &mut Plan) {
        let tail = tail && self.c.facts.conversion_code(x).is_none() && !self.c.facts.reshaped.contains_key(&x);
        match self.c.arena.exp_at(x).clone() {
            Exp::Var(_) | Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => {}
            Exp::Lambda { params, body } => {
                let ps: Vec<Sym> = params.iter().map(|(n, _)| *n).collect();
                self.plan_lambda(&ps, body, e, None, plan);
            }
            Exp::RLambda { region, lambda } => {
                self.plan_exp(region, e, false, plan);
                let Exp::Lambda { params, body } = self.c.arena.exp_at(lambda).clone() else { return };
                let ps: Vec<Sym> = params.iter().map(|(n, _)| *n).collect();
                self.plan_lambda(&ps, body, e, None, plan);
            }
            Exp::App { fun, args } if let Some((ps, lbody)) = self.applied_lambda(fun, args.len()) => {
                let bindings: Vec<(Sym, ExpId)> = ps.into_iter().zip(args.iter().copied()).collect();
                self.plan_let(&bindings, lbody, e, tail, plan);
            }
            Exp::App { fun, args } => {
                self.plan_call(x, fun, &args, e, plan);
                self.plan_exps(&args, e, plan);
                // A standard operation's name, or a lifted procedure's, is
                // not compiled as a value.
                let compiled = match self.c.arena.exp_at(fun) {
                    Exp::Var(n) => !matches!(self.where_is(e, *n), None | Some(Loc::Lifted(_))),
                    _ => true,
                };
                if compiled {
                    self.plan_exp(fun, e, false, plan);
                }
            }
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => {
                self.plan_exp(body, e, tail, plan)
            }
            Exp::LetRegion { form, region, body } => {
                if form.enter().is_none() {
                    return self.plan_exp(body, e, tail, plan);
                }
                let mut inner = e.clone();
                inner.push((self.c.arena.dvar_name(region), SLOT));
                self.plan_exp(body, &inner, false, plan);
            }
            Exp::If { test, then, els } => {
                self.plan_exp(test, e, false, plan);
                self.plan_exp(then, e, tail, plan);
                self.plan_exp(els, e, tail, plan);
            }
            Exp::Let { bindings, body } => self.plan_let(&bindings, body, e, tail, plan),
            Exp::Letrec { bindings, body } => {
                let key = self.span_key(x);
                match self.lift_plan(&bindings, body, e, tail) {
                    Some((lams, added)) => {
                        // Each member's closure counted, as `lift` makes them.
                        let mut ks = Vec::new();
                        for a in &added {
                            self.lifts.push(Lift { closure: Value::FALSE, added: a.clone() });
                            ks.push(self.lifts.len() - 1);
                        }
                        plan.lifts.insert(key, Some(added.clone()));
                        let mut known: Env = e.iter().filter(|(_, l)| matches!(l, Loc::Lifted(_))).copied().collect();
                        known.extend(bindings.iter().zip(&ks).map(|((g, _, _), k)| (*g, Loc::Lifted(*k))));
                        for (i, (name, _, _)) in bindings.iter().enumerate() {
                            let (ps, lbody) = &lams[i];
                            let mut all = added[i].clone();
                            all.extend(ps.iter().copied());
                            let own = self.loops_only(*lbody, *name, ps.len(), true).then_some(*name);
                            self.plan_lambda(&all, *lbody, &known, own, plan);
                        }
                        let mut inner = e.clone();
                        inner.extend(bindings.iter().zip(&ks).map(|((g, _, _), k)| (*g, Loc::Lifted(*k))));
                        self.plan_exp(body, &inner, tail, plan);
                    }
                    None => {
                        plan.lifts.insert(key, None);
                        for (i, (name, _, init)) in bindings.iter().enumerate() {
                            let Some((ps, lbody, region)) = self.lambda_of(*init) else { continue };
                            let mut own = e.clone();
                            for (k, (g, _, _)) in bindings.iter().enumerate() {
                                let loops = k == i && self.loops_only(lbody, *g, ps.len(), true);
                                own.push((*g, if loops { Loc::Loop } else { Loc::Pending(0) }));
                            }
                            if let Some(r) = region {
                                self.plan_exp(r, &own, false, plan);
                            }
                            self.plan_lambda(&ps, lbody, &own, Some(*name), plan);
                        }
                        let mut inner = e.clone();
                        inner.extend(bindings.iter().map(|(g, _, _)| (*g, SLOT)));
                        self.plan_exp(body, &inner, tail, plan);
                    }
                }
            }
            Exp::Module(items) => self.plan_module(&items, e, plan),
            Exp::With { module: _, body } => {
                let names = self.c.facts.with_vals.get(&x).cloned().unwrap_or_default();
                let mut inner = e.clone();
                inner.extend(names.iter().map(|n| (*n, SLOT)));
                self.plan_exp(body, &inner, tail, plan);
            }
            Exp::Begin(items) => {
                if let Some((last, rest)) = items.split_last() {
                    self.plan_exps(rest, e, plan);
                    self.plan_exp(*last, e, tail, plan);
                }
            }
            Exp::Prompt { tag, body, handler } => {
                self.plan_exp(tag, e, false, plan);
                self.plan_exp(handler, e, false, plan);
                self.plan_lambda(&[], body, e, None, plan);
            }
            Exp::Bloblet { args, .. } => self.plan_exps(&args, e, plan),
            Exp::Product(fields) => {
                for (_, f) in fields {
                    self.plan_exp(f, e, false, plan);
                }
            }
            Exp::Extract(p, _) => self.plan_exp(p, e, false, plan),
            Exp::Sum(_, v) => self.plan_exp(v, e, false, plan),
            Exp::TagCase { scrutinee, arms, els } => {
                self.plan_exp(scrutinee, e, false, plan);
                for arm in &arms {
                    let mut bound = e.clone();
                    match &arm.bind {
                        ArmBind::Value(x) => bound.push((*x, SLOT)),
                        ArmBind::Fields(xs) => bound.extend(xs.iter().map(|x| (*x, SLOT))),
                    }
                    self.plan_exp(arm.body, &bound, tail, plan);
                }
                if let Some((y, body)) = els {
                    let mut inner = e.clone();
                    inner.push((y, SLOT));
                    self.plan_exp(body, &inner, tail, plan);
                }
            }
        }
    }

    /// A call of a global (step 3), as `r_inlined` and `r_specialized` see
    /// it: the small procedure of its name and arity, if one may be inlined;
    /// the procedure of its name and arity that may be specialized, if the
    /// argument at its parameter is a lambda small enough, taking as many
    /// arguments as it is called with.
    fn plan_call(&mut self, x: ExpId, fun: ExpId, args: &[ExpId], e: &Env, plan: &mut Plan) {
        let Exp::Var(name) = *self.c.arena.exp_at(fun) else { return };
        if !matches!(self.where_is(e, name), Some(Loc::Global(_))) {
            return;
        }
        let n = args.len();
        // Not a body being inlined on the way here (`r_inlined`'s guard).
        let inline = self.inlines.iter().position(|i| i.name == name && i.params.len() == n).filter(|_| !self.plan_inlining.contains(&name));
        let special = self.specials.iter().position(|s| s.name == name && s.params.len() == n).and_then(|k| {
            let lam = args[self.specials[k].param];
            match self.c.arena.exp_at(lam) {
                Exp::Lambda { params, body } if params.len() == self.specials[k].arity && self.inline_room(*body, super::INLINE_LIMIT) >= 0 => Some((k, lam)),
                _ => None,
            }
        });
        plan.calls.insert(self.span_key(x), Called { inline, special });
        if let Some(k) = inline
            && !plan.inlined.contains_key(&k)
        {
            let sub = self.plan_inlined(k, name);
            plan.inlined.insert(k, sub);
        }
    }

    /// The body of `inlines[k]`, `name`'s, planned as `r_inline` compiles it:
    /// its parameters local, in the globals it saw, `name` not inlined in
    /// it again. (An inlined body makes no closure: `inline_room`.)
    fn plan_inlined(&mut self, k: usize, name: Sym) -> Plan {
        let (body, genv_len) = (self.inlines[k].body, self.inlines[k].genv_len);
        let env: Env = self.inlines[k].params.iter().map(|p| (*p, SLOT)).collect();
        let mut sub = Plan::default();
        let outer = self.genv_limit.replace(genv_len);
        self.plan_inlining.push(name);
        self.plan_exp(body, &env, false, &mut sub);
        self.plan_inlining.pop();
        self.genv_limit = outer;
        sub
    }

    /// The plan of where register code is now: the form's, or, inside an
    /// inlined body, that body's there, along the path to it.
    fn plan_here(&self) -> Option<&Plan> {
        let mut p = self.plan.as_ref()?;
        for k in &self.inlining_ks {
            p = p.inlined.get(k)?;
        }
        Some(p)
    }

    /// Call `x` as the plan decided it, where its call sites are the plan's:
    /// in a planned lambda's own register code, outside any inlined body
    /// or copy; a call of no global, none planned, as neither. None
    /// elsewhere, where register code decides.
    pub(crate) fn planned_call(&self, x: ExpId) -> Option<Called> {
        if !self.r_in_plan || self.spec.is_some() {
            return None;
        }
        let plan = self.plan_here()?;
        Some(plan.calls.get(&self.span_key(x)).copied().unwrap_or(Called { inline: None, special: None }))
    }

    /// In shadow (`FIXPT_PLAN_CHECK`), a call register code decides, in a
    /// planned lambda's twin outside any inlined body or copy, against the
    /// plan.
    pub(crate) fn plan_check_call(&mut self, x: ExpId, got: Called) {
        if !self.r_in_plan || self.spec.is_some() {
            return;
        }
        let Some(plan) = self.plan_here() else {
            let msg = format!("call at {:?}: no plan along {:?}", self.span_key(x), self.inlining_ks);
            self.plan_mismatches.push(msg);
            return;
        };
        let key = self.span_key(x);
        let planned = plan.calls.get(&key).copied().unwrap_or(Called { inline: None, special: None });
        self.plan_checks += 1;
        if planned != got {
            let msg = format!("call at {key:?}: planned {planned:?}, decided {got:?}");
            self.plan_mismatches.push(msg);
        }
    }

    fn plan_let(&mut self, bindings: &[(Sym, ExpId)], body: ExpId, e: &Env, tail: bool, plan: &mut Plan) {
        let mut inner = e.clone();
        for (n, init) in bindings {
            self.plan_exp(*init, e, false, plan);
            inner.push((*n, SLOT));
        }
        self.plan_exp(body, &inner, tail, plan);
    }

    /// As `exp`'s module: each item made in order, a lambda naming an item
    /// not made yet capturing it as a `letrec`'s sibling is.
    fn plan_module(&mut self, items: &[ModItem], e: &Env, plan: &mut Plan) {
        let lambdas = self.c.module_lambdas(items);
        let is_lambda = |n: Sym, i: usize| lambdas.iter().any(|(m, _, _, at)| *m == n && *at == i);
        let mut slots: Vec<(Sym, usize)> = Vec::new();
        for item in items {
            match item {
                ModItem::Desc { .. } => {}
                ModItem::Abs { up, down, .. } => slots.extend([(*up, 0), (*down, 0)]),
                ModItem::Val { name, .. } => slots.push((*name, 0)),
                ModItem::Rec(group) => slots.extend(group.iter().map(|(n, _, _)| (*n, 0))),
            }
        }
        let (mut inner, mut made) = (e.clone(), 0);
        for (i, item) in items.iter().enumerate() {
            let made_here: Vec<(Sym, ExpId)> = match item {
                ModItem::Desc { .. } => Vec::new(),
                ModItem::Abs { up, down, up_fn, down_fn, .. } => vec![(*up, *up_fn), (*down, *down_fn)],
                ModItem::Val { name, init, .. } => vec![(*name, *init)],
                ModItem::Rec(group) => group.iter().map(|(n, _, x)| (*n, *x)).collect(),
            };
            for (n, x) in made_here {
                let later: Vec<(Sym, usize)> = slots[made..].to_vec();
                if is_lambda(n, i) && self.names_any(x, &later) {
                    if let Some((ps, lbody, region)) = self.lambda_of(x) {
                        let mut own = inner.clone();
                        for (m, _) in &later {
                            let loops = *m == n && self.loops_only(lbody, n, ps.len(), true);
                            own.push((*m, if loops { Loc::Loop } else { Loc::Pending(0) }));
                        }
                        if let Some(r) = region {
                            self.plan_exp(r, &own, false, plan);
                        }
                        self.plan_lambda(&ps, lbody, &own, Some(n), plan);
                    }
                } else {
                    self.plan_exp(x, &inner, false, plan);
                }
                inner.push((n, SLOT));
                made += 1;
            }
        }
    }

    /// As `lambda_word_in`: what its closure captures in `e`, then its body,
    /// in the environment its word has, in tail position.
    fn plan_lambda(&mut self, params: &[Sym], body: ExpId, e: &Env, own: Option<Sym>, plan: &mut Plan) {
        let fv = self.captured(params, body, e);
        plan.procs.insert((self.span_key(body), params.to_vec()), Planned { params: params.to_vec(), own, fv: fv.clone() });
        let own = own.filter(|f| !params.contains(f));
        // Lifted procedures are known everywhere inside: they are constants.
        let mut inner: Env = e.iter().filter(|(_, l)| matches!(l, Loc::Lifted(_))).copied().collect();
        if let Some(f) = own.filter(|f| !fv.contains(f)) {
            inner.push((f, Loc::Loop));
        }
        inner.extend(params.iter().map(|p| (*p, SLOT)));
        inner.extend(fv.iter().enumerate().map(|(i, n)| (*n, Loc::Free(i))));
        self.plan_exp(body, &inner, true, plan);
    }

    /// What the lambda of `body` captures, as the plan says, in the stack
    /// code's own walk; none in register code's, or a lambda not planned.
    pub(crate) fn planned_fv(&self, params: &[Sym], body: ExpId) -> Option<Vec<Sym>> {
        if self.twin_depth > 0 || self.spec.is_some() {
            return None;
        }
        self.plan.as_ref()?.procs.get(&(self.span_key(body), params.to_vec())).map(|p| p.fv.clone())
    }

    /// Whether the `letrec` `x` is lifted, as the plan says (the names each
    /// member takes first, if so), in the stack code's own walk; none (not
    /// planned) in register code's.
    pub(crate) fn planned_lift(&self, x: ExpId) -> Option<Option<Vec<Vec<Sym>>>> {
        if self.twin_depth > 0 || self.spec.is_some() {
            return None;
        }
        self.plan.as_ref()?.lifts.get(&self.span_key(x)).cloned()
    }

    /// A lifted `letrec`'s members' parameters and bodies (each is a plain
    /// lambda: `lift_plan` said so).
    pub(crate) fn lift_lambdas(&self, bindings: &[(Sym, crate::ast::TyId, ExpId)]) -> Vec<(Vec<Sym>, ExpId)> {
        bindings
            .iter()
            .filter_map(|(_, _, init)| self.lambda_of(*init).map(|(ps, body, _)| (ps, body)))
            .collect()
    }

    /// In shadow (`FIXPT_PLAN_CHECK`), a lambda the stack code compiles, as
    /// it decided it, against the plan: a difference noted.
    pub(crate) fn plan_check_lambda(&mut self, params: &[Sym], body: ExpId, own: Option<Sym>, fv: &[Sym]) {
        if self.twin_depth > 0 || self.spec.is_some() {
            return;
        }
        let Some(plan) = &self.plan else { return };
        self.plan_checks += 1;
        let key = (self.span_key(body), params.to_vec());
        let got = Planned { params: params.to_vec(), own, fv: fv.to_vec() };
        match plan.procs.get(&key) {
            Some(p) if *p == got => {}
            planned => {
                let msg = format!("lambda at {key:?}: planned {planned:?}, compiled {got:?}");
                self.plan_mismatches.push(msg);
            }
        }
    }

    /// The same for a `letrec`'s lifting.
    pub(crate) fn plan_check_lift(&mut self, x: ExpId, added: Option<&Vec<Vec<Sym>>>) {
        if self.twin_depth > 0 || self.spec.is_some() {
            return;
        }
        let Some(plan) = &self.plan else { return };
        self.plan_checks += 1;
        let key = self.span_key(x);
        let planned = plan.lifts.get(&key);
        if planned.map(|p| p.as_ref()) != Some(added) {
            let msg = format!("letrec at {key:?}: planned {planned:?}, compiled {added:?}");
            self.plan_mismatches.push(msg);
        }
    }
}
