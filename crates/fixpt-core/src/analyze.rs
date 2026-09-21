//! The analysis pass: reference and assignment marks, and free-variable sets.
//!
//! One pass, run once after expansion, filling the side tables the engines
//! need:
//!
//! * `VarInfo::referenced` / `VarInfo::assigned` — the compiler boxes exactly
//!   the assigned variables (assignment conversion) and can drop bindings that
//!   are neither.
//! * `LambdaInfo::free` — the closure's capture layout, in a fixed order, so
//!   the compiler can emit flat closures and index captures in O(1).
//!
//! Free sets are computed bottom-up with memoisation: an inner lambda's free
//! set is computed once and then contributes to its enclosing lambda, so the
//! whole pass is linear in program size rather than quadratic in nesting depth.

use crate::ir::{LambdaId, Node, NodeId, Program, VarId};
use std::collections::HashSet;

pub fn analyze(program: &mut Program) {
    let mut a = Analysis {
        free_of_lambda: vec![None; program.lambdas.len()],
        referenced: HashSet::new(),
        assigned: HashSet::new(),
    };

    // Free variables of the top-level body, with nothing bound outside it.
    let mut top = FreeSet::default();
    a.walk(program, program.body, &mut HashSet::new(), &mut top);

    for (i, f) in a.free_of_lambda.iter().enumerate() {
        program.lambdas[i].free = f.clone().unwrap_or_default().order;
    }
    for (i, v) in program.vars.iter_mut().enumerate() {
        let id = VarId(i as u32);
        v.referenced = a.referenced.contains(&id);
        v.assigned = a.assigned.contains(&id);
    }
}

/// Free variables in first-appearance order. The order is part of the contract:
/// it is the capture layout, so it must be deterministic, which rules out
/// iterating a `HashSet`.
#[derive(Default, Clone)]
struct FreeSet {
    order: Vec<VarId>,
    seen: HashSet<VarId>,
}

impl FreeSet {
    fn add(&mut self, v: VarId) {
        if self.seen.insert(v) {
            self.order.push(v);
        }
    }
}

struct Analysis {
    free_of_lambda: Vec<Option<FreeSet>>,
    referenced: HashSet<VarId>,
    assigned: HashSet<VarId>,
}

impl Analysis {
    fn use_var(&mut self, v: VarId, bound: &HashSet<VarId>, free: &mut FreeSet) {
        self.referenced.insert(v);
        if !bound.contains(&v) {
            free.add(v);
        }
    }

    fn walk(
        &mut self,
        program: &Program,
        id: NodeId,
        bound: &mut HashSet<VarId>,
        free: &mut FreeSet,
    ) {
        match program.node(id).clone() {
            Node::Const(_) | Node::GlobalRef(_) => {}
            Node::Ref(v) => self.use_var(v, bound, free),
            Node::Set(v, e) => {
                self.assigned.insert(v);
                // An assignment is also a use: a `set!` of a variable from an
                // enclosing scope still has to capture it.
                self.use_var(v, bound, free);
                self.walk(program, e, bound, free);
            }
            Node::GlobalSet(_, e) => self.walk(program, e, bound, free),
            Node::If(a, b, c) => {
                self.walk(program, a, bound, free);
                self.walk(program, b, bound, free);
                self.walk(program, c, bound, free);
            }
            Node::Seq(items) => {
                for n in items.iter() {
                    self.walk(program, *n, bound, free);
                }
            }
            Node::Let { vars, inits, body } => {
                // Initialisers are outside the scope of the bindings.
                for n in inits.iter() {
                    self.walk(program, *n, bound, free);
                }
                let added = extend(bound, &vars);
                self.walk(program, body, bound, free);
                retract(bound, &added);
            }
            Node::Fix { vars, inits, body } => {
                // …but in `letrec*` they are inside it.
                let added = extend(bound, &vars);
                for n in inits.iter() {
                    self.walk(program, *n, bound, free);
                }
                self.walk(program, body, bound, free);
                retract(bound, &added);
            }
            Node::Lambda(l) => {
                let inner = self.lambda_free(program, l);
                // Whatever the inner lambda leaves free is used here, and is
                // free here too unless this scope binds it.
                for v in inner.order.iter() {
                    self.use_var(*v, bound, free);
                }
            }
            Node::App { rator, rands } => {
                self.walk(program, rator, bound, free);
                for n in rands.iter() {
                    self.walk(program, *n, bound, free);
                }
            }
            Node::PrimCall { rands, .. } => {
                for n in rands.iter() {
                    self.walk(program, *n, bound, free);
                }
            }
        }
    }

    fn lambda_free(&mut self, program: &Program, l: LambdaId) -> FreeSet {
        if let Some(f) = &self.free_of_lambda[l.index()] {
            return f.clone();
        }
        let info = program.lambda(l);
        let mut bound: HashSet<VarId> = info.params.iter().copied().collect();
        if let Some(r) = info.rest {
            bound.insert(r);
        }
        let mut free = FreeSet::default();
        // Guard against a cycle in a malformed program rather than recursing
        // forever; a well-formed one never revisits a lambda.
        self.free_of_lambda[l.index()] = Some(FreeSet::default());
        self.walk(program, info.body, &mut bound, &mut free);
        self.free_of_lambda[l.index()] = Some(free.clone());
        free
    }
}

fn extend(bound: &mut HashSet<VarId>, vars: &[VarId]) -> Vec<VarId> {
    let mut added = Vec::new();
    for v in vars {
        if bound.insert(*v) {
            added.push(*v);
        }
    }
    added
}

fn retract(bound: &mut HashSet<VarId>, added: &[VarId]) {
    for v in added {
        bound.remove(v);
    }
}
