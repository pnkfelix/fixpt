//! Assignment conversion.
//!
//! A flat closure *copies* the values it captures, so a variable that is both
//! captured and assigned would end up with two independent copies — the
//! closure's and the defining frame's — and `set!` through one would not be
//! seen by the other. Boxing fixes it: the binding holds a one-slot mutable
//! cell, both parties capture the same cell, and `set!` writes through it.
//!
//! Only variables that are actually assigned are boxed, which is why
//! [`analyze`](crate::analyze) computes `VarInfo::assigned` first. Everything
//! else stays in a register.
//!
//! This pass runs for the **compiler only**. The AST engine uses chained
//! environment frames, where a captured variable is already shared by
//! construction, so boxing there would be pure overhead.

use crate::ir::{Builder, LambdaInfo, Node, NodeId, Program, VarId};
use fixpt_read::Span;
use std::collections::HashSet;

/// Rewrite `program` so that every assigned variable is boxed.
///
/// Boxes are expressed as [`Node::PrimCall`] rather than as new IR nodes, so
/// the grammar stays the size it was. `PrimCall` and not a call through a
/// global: routing through `%box-ref` as a *variable* would mean a program that
/// rebinds that name could break every `set!` in the image.
pub fn convert(program: &Program, prim: BoxPrims) -> Program {
    let mut boxed: HashSet<VarId> = program
        .vars
        .iter()
        .enumerate()
        .filter(|(_, v)| v.assigned)
        .map(|(i, _)| VarId(i as u32))
        .collect();
    let captured = fix_captured(program);
    boxed.extend(captured.iter().copied());
    if boxed.is_empty() {
        return clone_program(program);
    }
    let mut c = Converter {
        program,
        boxed,
        prologue: captured,
        b: Builder::new(),
        prim,
    };
    // Lambdas are registered before bodies are converted, so a recursive
    // reference finds its target.
    let lambda_ids: Vec<_> = (0..program.lambdas.len())
        .map(|i| {
            let info = program.lambda(crate::ir::LambdaId(i as u32));
            c.b.lambda(LambdaInfo {
                name: info.name,
                params: info.params.clone(),
                rest: info.rest,
                body: NodeId(0),
                span: info.span,
                free: info.free.clone(),
            })
        })
        .collect();
    for (i, info) in program.vars.iter().enumerate() {
        let v = c.b.var(info.name, info.span);
        debug_assert_eq!(v, VarId(i as u32), "variable ids must be preserved");
    }
    for (i, id) in lambda_ids.iter().enumerate() {
        let info = program.lambda(crate::ir::LambdaId(i as u32)).clone();
        let body = c.convert(info.body);
        // A boxed parameter is boxed on entry, since its value arrives in a
        // register.
        let body = c.box_params(&info, body);
        c.b.set_lambda_body(*id, body);
    }
    let body = c.convert(program.body);
    let mut out = c.b.finish(body);
    for (i, v) in program.vars.iter().enumerate() {
        out.vars[i].assigned = v.assigned;
        out.vars[i].referenced = v.referenced;
    }
    out
}

/// Primitive indices for `%make-box`, `%box-ref` and `%box-set!`.
///
/// Passed in rather than looked up here, because the primitive table lives in
/// the runtime crate and the IR deliberately does not depend on it.
#[derive(Copy, Clone, Debug)]
pub struct BoxPrims {
    pub make: u16,
    pub get: u16,
    pub set: u16,
}

/// `letrec*`-bound variables that a closure inside the same `letrec*`'s
/// initialisers captures.
///
/// These have to be boxed too, and the reason has nothing to do with `set!`.
/// A flat closure captures values, but a recursive binding's value does not
/// exist yet when its own closure is built: in
/// `(letrec ((f (lambda (n) (f (- n 1))))) …)` the closure for `f` would
/// capture `f`'s slot while it is still unbound. Boxing it means the closure
/// captures the cell instead, and `letrec*`'s store fills it in before anyone
/// calls it — which is precisely the sharing the chained-environment engine
/// gets for free.
///
/// Only the captured ones: `(letrec ((x 5)) (+ x 1))` keeps `x` in a register.
///
/// A sharper compiler would patch the closures' capture slots after building
/// them all and avoid the indirection on every recursive call. That is a real
/// optimisation to make later; it is not needed for correctness.
fn fix_captured(program: &Program) -> HashSet<VarId> {
    let mut out = HashSet::new();
    for id in 0..program.nodes.len() {
        let Node::Fix { vars, inits, .. } = program.node(NodeId(id as u32)) else {
            continue;
        };
        let bound: HashSet<VarId> = vars.iter().copied().collect();
        let mut captured = HashSet::new();
        for init in inits.iter() {
            collect_captures(program, *init, &mut captured);
        }
        if bound.is_disjoint(&captured) {
            continue;
        }
        // The whole group, not only the captured members: see
        // `fix_with_prologue` for why splitting it would reorder user code.
        out.extend(bound);
    }
    out
}

/// Variables captured by any lambda occurring within `id`.
///
/// Only the outermost lambdas need visiting: `analyze` has already propagated
/// a nested lambda's free variables outward into its enclosing lambda's set.
fn collect_captures(program: &Program, id: NodeId, out: &mut HashSet<VarId>) {
    match program.node(id) {
        Node::Lambda(l) => out.extend(program.lambda(*l).free.iter().copied()),
        Node::Const(_) | Node::Ref(_) | Node::GlobalRef(_) => {}
        Node::Set(_, e) | Node::GlobalSet(_, e) => collect_captures(program, *e, out),
        Node::If(a, b, c) => {
            collect_captures(program, *a, out);
            collect_captures(program, *b, out);
            collect_captures(program, *c, out);
        }
        Node::Seq(items) => {
            for n in items.iter() {
                collect_captures(program, *n, out);
            }
        }
        Node::Let { inits, body, .. } | Node::Fix { inits, body, .. } => {
            for n in inits.iter() {
                collect_captures(program, *n, out);
            }
            collect_captures(program, *body, out);
        }
        Node::App { rator, rands } => {
            collect_captures(program, *rator, out);
            for n in rands.iter() {
                collect_captures(program, *n, out);
            }
        }
        Node::PrimCall { rands, .. } => {
            for n in rands.iter() {
                collect_captures(program, *n, out);
            }
        }
    }
}

struct Converter<'a> {
    program: &'a Program,
    boxed: HashSet<VarId>,
    /// The subset of `boxed` whose `letrec*` group must use the prologue form.
    prologue: HashSet<VarId>,
    b: Builder,
    prim: BoxPrims,
}

impl Converter<'_> {
    /// `letrec*` whose own initialisers capture one of its bindings.
    ///
    /// Boxing the binding is not enough on its own: the box has to exist before
    /// any initialiser runs, or the closure that captures it captures an empty
    /// slot. So every binding in the group is bound to a fresh box holding
    /// [`Value::UNBOUND`], and the real initialisers move into the body as
    /// assignments:
    ///
    /// ```text
    /// (letrec ((v₀ e₀) … (vₙ e₀)) body)
    ///   ⇒ (letrec ((v₀ (box unbound)) … (vₙ (box unbound)))
    ///        (box-set! v₀ e₀) … (box-set! vₙ eₙ)
    ///        body)
    /// ```
    ///
    /// *Every* binding, not just the captured ones: the initialisers are
    /// arbitrary expressions and `letrec*` runs them left to right, so moving
    /// only some of them would reorder user code. FX-91's own test suite reads
    /// an earlier binding from a later initialiser, which makes that order a
    /// conformance requirement rather than a nicety.
    ///
    /// The boxes start unbound rather than unspecified so that reading a
    /// binding before its initialiser has run is still an error, exactly as in
    /// the engine whose environment slots start unbound.
    fn fix_with_prologue(
        &mut self,
        span: Span,
        vars: &[VarId],
        inits: &[NodeId],
        body: NodeId,
    ) -> NodeId {
        let unbound = self.b.constant(fixpt_heap::Value::UNBOUND);
        let mut fresh = Vec::with_capacity(vars.len());
        for _ in vars {
            let u = self.b.node(span, Node::Const(unbound));
            fresh.push(self.call(span, self.prim.make, vec![u]));
        }
        let mut seq = Vec::with_capacity(inits.len() + 1);
        for (v, init) in vars.iter().zip(inits.iter()) {
            let value = self.convert(*init);
            let cell = self.b.node(span, Node::Ref(*v));
            seq.push(self.call(span, self.prim.set, vec![cell, value]));
        }
        seq.push(self.convert(body));
        let body = self.b.node(span, Node::Seq(seq.into_boxed_slice()));
        self.b.node(
            span,
            Node::Fix {
                vars: vars.to_vec().into_boxed_slice(),
                inits: fresh.into_boxed_slice(),
                body,
            },
        )
    }

    fn call(&mut self, span: Span, prim: u16, args: Vec<NodeId>) -> NodeId {
        self.b.node(
            span,
            Node::PrimCall {
                prim,
                rands: args.into_boxed_slice(),
            },
        )
    }

    /// Wrap a body so that each boxed parameter is re-bound to a box holding
    /// its incoming value.
    fn box_params(&mut self, info: &LambdaInfo, body: NodeId) -> NodeId {
        let mut targets: Vec<VarId> = info.params.to_vec();
        if let Some(r) = info.rest {
            targets.push(r);
        }
        targets.retain(|v| self.boxed.contains(v));
        if targets.is_empty() {
            return body;
        }
        let span = info.span;
        let mut seq = Vec::with_capacity(targets.len() + 1);
        for v in targets {
            let read = self.b.node(span, Node::Ref(v));
            let boxed = self.call(span, self.prim.make, vec![read]);
            seq.push(self.b.node(span, Node::Set(v, boxed)));
        }
        seq.push(body);
        self.b.node(span, Node::Seq(seq.into_boxed_slice()))
    }

    fn convert(&mut self, id: NodeId) -> NodeId {
        let span = self.program.span(id);
        match self.program.node(id).clone() {
            Node::Const(c) => {
                let v = self.program.constant(c);
                let c = self.b.constant(v);
                self.b.node(span, Node::Const(c))
            }
            Node::Ref(v) => {
                let r = self.b.node(span, Node::Ref(v));
                if self.boxed.contains(&v) {
                    self.call(span, self.prim.get, vec![r])
                } else {
                    r
                }
            }
            Node::Set(v, e) => {
                let value = self.convert(e);
                if self.boxed.contains(&v) {
                    let cell = self.b.node(span, Node::Ref(v));
                    self.call(span, self.prim.set, vec![cell, value])
                } else {
                    self.b.node(span, Node::Set(v, value))
                }
            }
            Node::GlobalRef(g) => self.b.node(span, Node::GlobalRef(g)),
            Node::GlobalSet(g, e) => {
                let value = self.convert(e);
                self.b.node(span, Node::GlobalSet(g, value))
            }
            Node::If(a, b, c) => {
                let a = self.convert(a);
                let b = self.convert(b);
                let c = self.convert(c);
                self.b.node(span, Node::If(a, b, c))
            }
            Node::Seq(items) => {
                let items: Vec<NodeId> = items.iter().map(|n| self.convert(*n)).collect();
                self.b.node(span, Node::Seq(items.into_boxed_slice()))
            }
            Node::Let { vars, inits, body } => {
                let inits: Vec<NodeId> = inits
                    .iter()
                    .zip(vars.iter())
                    .map(|(n, v)| {
                        let init = self.convert(*n);
                        if self.boxed.contains(v) {
                            self.call(span, self.prim.make, vec![init])
                        } else {
                            init
                        }
                    })
                    .collect();
                let body = self.convert(body);
                self.b.node(
                    span,
                    Node::Let {
                        vars,
                        inits: inits.into_boxed_slice(),
                        body,
                    },
                )
            }
            Node::Fix { vars, inits, body } => {
                if vars.iter().any(|v| self.prologue.contains(v)) {
                    return self.fix_with_prologue(span, &vars, &inits, body);
                }
                // No initialiser captures anything here, so a box can simply
                // be made *from* the value, as in `let`.
                let inits: Vec<NodeId> = inits
                    .iter()
                    .zip(vars.iter())
                    .map(|(n, v)| {
                        let init = self.convert(*n);
                        if self.boxed.contains(v) {
                            self.call(span, self.prim.make, vec![init])
                        } else {
                            init
                        }
                    })
                    .collect();
                let body = self.convert(body);
                self.b.node(
                    span,
                    Node::Fix {
                        vars,
                        inits: inits.into_boxed_slice(),
                        body,
                    },
                )
            }
            Node::Lambda(l) => self.b.node(span, Node::Lambda(l)),
            Node::App { rator, rands } => {
                let rator = self.convert(rator);
                let rands: Vec<NodeId> = rands.iter().map(|n| self.convert(*n)).collect();
                self.b.node(
                    span,
                    Node::App {
                        rator,
                        rands: rands.into_boxed_slice(),
                    },
                )
            }
            Node::PrimCall { prim, rands } => {
                let rands: Vec<NodeId> = rands.iter().map(|n| self.convert(*n)).collect();
                self.b.node(
                    span,
                    Node::PrimCall {
                        prim,
                        rands: rands.into_boxed_slice(),
                    },
                )
            }
        }
    }
}

fn clone_program(p: &Program) -> Program {
    Program {
        nodes: p.nodes.clone(),
        spans: p.spans.clone(),
        vars: p.vars.clone(),
        lambdas: p.lambdas.clone(),
        consts: p.consts.clone(),
        body: p.body,
    }
}
