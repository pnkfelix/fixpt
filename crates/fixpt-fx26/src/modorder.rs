//! A module's typed lambda definitions see their own names (`TODO.md`
//! §37), as a typed `define` of a lambda does at the top level: otherwise a
//! module's definitions are in order, each seeing those before it, and
//! procedures that call each other are a `define-rec`. The parser makes each
//! typed lambda definition whose value names itself a `define-rec` of one,
//! which the checkers, the lowering, the compilers and the evaluator all
//! know: its calls of itself direct, checked to end as a `define-rec`'s
//! members are. One that does not name itself stays a definition (and may
//! be inlined where a re-export of it is called, `DONE.md` §38). Names are
//! free names, syntactically; a `with` binds none of them, as the parser
//! does not know a module's names. The FX-26 parser's `module-own-names`
//! (`parser-modules.fx`) is this, step for step.

use crate::ast::{Exp, ExpId, ModItem};
use crate::check::Checker;
use fixpt_read::Sym;

impl Checker {
    /// `items`, each typed lambda definition naming itself a `define-rec`
    /// of one, as the module says above.
    pub(crate) fn module_own_names(&self, items: Vec<ModItem>) -> Vec<ModItem> {
        items
            .into_iter()
            .map(|item| match item {
                ModItem::Val { name, ty: Some(ty), init } if self.is_lambda(init) && self.names_itself(name, init) => {
                    ModItem::Rec(vec![(name, ty, init)])
                }
                other => other,
            })
            .collect()
    }

    /// Whether `name` is free in `init`.
    fn names_itself(&self, name: Sym, init: ExpId) -> bool {
        let mut out = Vec::new();
        self.free_names(init, &mut Vec::new(), &mut out);
        out.contains(&name)
    }

    /// The names free in `x`, in the order first met, syntactically: a
    /// `lambda`, `let`, `letrec` and `tagcase` arm bind theirs; a `with`
    /// binds none (its module's names are not known here), its module's
    /// name being one of them; a module inside binds all its items' names.
    pub(crate) fn free_names(&self, x: ExpId, bound: &mut Vec<Sym>, out: &mut Vec<Sym>) {
        let depth = bound.len();
        match self.arena.exp_at(x).clone() {
            Exp::Var(n) => {
                if !bound.contains(&n) && !out.contains(&n) {
                    out.push(n);
                }
            }
            Exp::Lambda { params, body } => {
                bound.extend(params.iter().map(|(n, _)| *n));
                self.free_names(body, bound, out);
            }
            Exp::App { fun, args } => {
                self.free_names(fun, bound, out);
                for a in args {
                    self.free_names(a, bound, out);
                }
            }
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::LetRegion { body, .. } => self.free_names(body, bound, out),
            Exp::The { exp, .. } | Exp::Convention { exp, .. } => self.free_names(exp, bound, out),
            Exp::RLambda { region, lambda } => {
                self.free_names(region, bound, out);
                self.free_names(lambda, bound, out);
            }
            Exp::If { test, then, els } => {
                for e in [test, then, els] {
                    self.free_names(e, bound, out);
                }
            }
            Exp::Letrec { bindings, body } => {
                bound.extend(bindings.iter().map(|(n, _, _)| *n));
                for (_, _, e) in &bindings {
                    self.free_names(*e, bound, out);
                }
                self.free_names(body, bound, out);
            }
            Exp::Let { bindings, body } => {
                for (_, e) in &bindings {
                    self.free_names(*e, bound, out);
                }
                bound.extend(bindings.iter().map(|(n, _)| *n));
                self.free_names(body, bound, out);
            }
            Exp::Begin(es) => {
                for e in es {
                    self.free_names(e, bound, out);
                }
            }
            Exp::Prompt { tag, body, handler } => {
                for e in [tag, body, handler] {
                    self.free_names(e, bound, out);
                }
            }
            Exp::Bloblet { args, .. } => {
                for e in args {
                    self.free_names(e, bound, out);
                }
            }
            Exp::Product(fs) => {
                for (_, e) in fs {
                    self.free_names(e, bound, out);
                }
            }
            Exp::Extract(p, _) => self.free_names(p, bound, out),
            Exp::Sum(_, v) => self.free_names(v, bound, out),
            Exp::TagCase { scrutinee, arms, els } => {
                self.free_names(scrutinee, bound, out);
                for arm in &arms {
                    let d = bound.len();
                    bound.extend(arm.names());
                    self.free_names(arm.body, bound, out);
                    bound.truncate(d);
                }
                if let Some((y, e)) = els {
                    bound.push(y);
                    self.free_names(e, bound, out);
                }
            }
            Exp::Module(items) => {
                for item in &items {
                    match item {
                        ModItem::Val { name, .. } => bound.push(*name),
                        ModItem::Rec(bs) => bound.extend(bs.iter().map(|(n, _, _)| *n)),
                        ModItem::Abs { up, down, .. } => bound.extend([*up, *down]),
                        ModItem::Desc { .. } => {}
                    }
                }
                for item in &items {
                    match item {
                        ModItem::Val { init, .. } => self.free_names(*init, bound, out),
                        ModItem::Rec(bs) => {
                            for (_, _, e) in bs {
                                self.free_names(*e, bound, out);
                            }
                        }
                        ModItem::Abs { up_fn, down_fn, .. } => {
                            self.free_names(*up_fn, bound, out);
                            self.free_names(*down_fn, bound, out);
                        }
                        ModItem::Desc { .. } => {}
                    }
                }
            }
            Exp::With { module, body } => {
                if !bound.contains(&module) && !out.contains(&module) {
                    out.push(module);
                }
                self.free_names(body, bound, out);
            }
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => {}
        }
        bound.truncate(depth);
    }
}
