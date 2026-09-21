//! The Core IR: what every front end produces and every engine consumes.
//!
//! Scheme, FX-87 and FX-91 all funnel through this. That is the whole economy
//! of the design — the FX front ends are front ends, exactly as `erase.lisp`
//! and `code.scm` were front ends onto Scheme, so they inherit the
//! interpreter, the compiler, heap dumping and single-binary builds without
//! any of it being written twice.
//!
//! # Shape
//!
//! An arena of nodes indexed by [`NodeId`], not a tree of boxes. Larceny's
//! `pass1`/`pass2` annotate lambda nodes in place with their reference,
//! assignment and free-variable sets; an arena is how you do that in Rust
//! without either interior mutability or rebuilding the tree on every pass.
//! Analyses live in dense side tables keyed by the same indices.
//!
//! The grammar is deliberately small — closer to Larceny's `pass1` output than
//! to Scheme:
//!
//! ```text
//! E ::= Const | Ref | GlobalRef | Set | GlobalSet
//!     | If | Seq | Let | Fix | Lambda | App | PrimCall
//! ```
//!
//! Everything else (`cond`, `case`, `do`, named `let`, `when`, `and`, …) is
//! gone by the time it gets here, having been expanded by the front end.
//!
//! # Constants and the collector
//!
//! Quoted data are real heap values, so they must be traced. They live in
//! [`Program::consts`], an ordinary `Vec<Value>` that the engine hands to
//! [`Heap::collect`](fixpt_heap::Heap::collect) as part of its root set at
//! every safepoint. Keeping them in a Rust `Vec` rather than a heap vector
//! means adding a constant never reallocates anything on the heap, and the
//! rooting is visible at the call site instead of hidden.

use fixpt_heap::Value;
use fixpt_read::{Span, Sym};

macro_rules! index_type {
    ($(#[$m:meta])* $name:ident) => {
        $(#[$m])*
        #[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
        pub struct $name(pub u32);
        impl $name {
            #[inline]
            pub const fn index(self) -> usize { self.0 as usize }
        }
    };
}

index_type!(
    /// A node in [`Program::nodes`].
    NodeId
);
index_type!(
    /// A lexical variable in [`Program::vars`]. Unique after alpha-renaming:
    /// no two binders anywhere in a program share one.
    VarId
);
index_type!(
    /// A lambda in [`Program::lambdas`].
    LambdaId
);
index_type!(
    /// An entry in [`Program::consts`].
    ConstId
);
index_type!(
    /// A global variable slot in the heap's global array. Resolved once, at
    /// expansion time, so a global reference is an array index rather than a
    /// symbol lookup.
    GlobalId
);

#[derive(Clone, Debug)]
pub struct VarInfo {
    pub name: Sym,
    pub span: Span,
    /// Assigned with `set!` anywhere. Drives assignment conversion: only these
    /// need to be boxed, so ordinary variables stay in registers.
    pub assigned: bool,
    /// Referenced anywhere. An unreferenced, unassigned binding can be dropped.
    pub referenced: bool,
}

#[derive(Clone, Debug)]
pub struct LambdaInfo {
    /// For error messages and for naming the closure in a backtrace.
    pub name: Option<Sym>,
    pub params: Vec<VarId>,
    /// `Some` for `(lambda (a b . rest) …)` and `(lambda args …)`.
    pub rest: Option<VarId>,
    pub body: NodeId,
    pub span: Span,
    /// Free variables, in a fixed order. Filled by analysis; the compiler uses
    /// it as the closure's capture layout.
    pub free: Vec<VarId>,
}

impl LambdaInfo {
    pub fn arity_min(&self) -> usize {
        self.params.len()
    }
    pub fn accepts(&self, n: usize) -> bool {
        if self.rest.is_some() { n >= self.params.len() } else { n == self.params.len() }
    }
}

#[derive(Clone, Debug)]
pub enum Node {
    Const(ConstId),
    Ref(VarId),
    GlobalRef(GlobalId),
    Set(VarId, NodeId),
    GlobalSet(GlobalId, NodeId),
    If(NodeId, NodeId, NodeId),
    /// Always at least two elements; a one-element `begin` collapses.
    Seq(Box<[NodeId]>),
    /// Parallel binding. `vars` and `inits` are the same length.
    Let { vars: Box<[VarId]>, inits: Box<[NodeId]>, body: NodeId },
    /// `letrec*`: bindings are visible in every initialiser, and initialisers
    /// run left to right.
    ///
    /// Left-to-right is not an arbitrary choice. R7RS leaves `letrec`'s
    /// evaluation order unspecified and actively guards against use before
    /// initialisation, but FX-91's own test suite depends on the sequential
    /// reading — `tests.fx`'s Peano numbers have `one`'s initialiser read the
    /// already-computed `zero` — which is how T and other period
    /// implementations expanded it. Since `code.scm` emits `letrec` for every
    /// `module`, honouring that order is a conformance requirement, not a
    /// liberty.
    Fix { vars: Box<[VarId]>, inits: Box<[NodeId]>, body: NodeId },
    Lambda(LambdaId),
    App { rator: NodeId, rands: Box<[NodeId]> },
    /// A call to a known primitive, with the indirection through a global
    /// removed. Produced by a pass, never by a front end directly.
    PrimCall { prim: u16, rands: Box<[NodeId]> },
}

/// A complete unit of compiled code: the arena, its side tables, its constants
/// and its entry point.
pub struct Program {
    pub nodes: Vec<Node>,
    /// Parallel to `nodes`.
    pub spans: Vec<Span>,
    pub vars: Vec<VarInfo>,
    pub lambdas: Vec<LambdaInfo>,
    /// Quoted data and literals. **Traced**: pass `&mut program.consts` to the
    /// collector at every safepoint.
    pub consts: Vec<Value>,
    pub body: NodeId,
}

impl Program {
    /// A program with nothing in it. Not runnable — `body` points at no node —
    /// but useful as a placeholder while an arena is being moved between
    /// owners.
    pub fn empty() -> Program {
        Program {
            nodes: Vec::new(),
            spans: Vec::new(),
            vars: Vec::new(),
            lambdas: Vec::new(),
            consts: Vec::new(),
            body: NodeId(0),
        }
    }

    #[inline]
    pub fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id.index()]
    }
    #[inline]
    pub fn span(&self, id: NodeId) -> Span {
        self.spans[id.index()]
    }
    #[inline]
    pub fn var(&self, id: VarId) -> &VarInfo {
        &self.vars[id.index()]
    }
    #[inline]
    pub fn lambda(&self, id: LambdaId) -> &LambdaInfo {
        &self.lambdas[id.index()]
    }
    #[inline]
    pub fn constant(&self, id: ConstId) -> Value {
        self.consts[id.index()]
    }

    /// The root slice the engine must include at every safepoint.
    pub fn const_roots(&mut self) -> &mut [Value] {
        &mut self.consts
    }
}

/// Incremental construction of a [`Program`].
///
/// Front ends build through this rather than assembling the vectors directly,
/// so that node/span parallelism and variable uniqueness are structural rather
/// than a convention each front end has to remember.
pub struct Builder {
    nodes: Vec<Node>,
    spans: Vec<Span>,
    vars: Vec<VarInfo>,
    lambdas: Vec<LambdaInfo>,
    consts: Vec<Value>,
}

impl Builder {
    /// Resume building on top of an existing program. A REPL expands each new
    /// form into the *same* arena, because closures made by earlier forms refer
    /// to lambdas and constants by index — a fresh arena per input would leave
    /// them dangling.
    pub fn from_program(p: Program) -> Builder {
        Builder {
            nodes: p.nodes,
            spans: p.spans,
            vars: p.vars,
            lambdas: p.lambdas,
            consts: p.consts,
        }
    }

    pub fn new() -> Builder {
        Builder {
            nodes: Vec::new(),
            spans: Vec::new(),
            vars: Vec::new(),
            lambdas: Vec::new(),
            consts: Vec::new(),
        }
    }

    pub fn node(&mut self, span: Span, node: Node) -> NodeId {
        self.nodes.push(node);
        self.spans.push(span);
        NodeId(self.nodes.len() as u32 - 1)
    }

    pub fn var(&mut self, name: Sym, span: Span) -> VarId {
        self.vars.push(VarInfo { name, span, assigned: false, referenced: false });
        VarId(self.vars.len() as u32 - 1)
    }

    pub fn lambda(&mut self, info: LambdaInfo) -> LambdaId {
        self.lambdas.push(info);
        LambdaId(self.lambdas.len() as u32 - 1)
    }

    /// Intern a constant. Identical `Value`s share an entry, which is what
    /// makes repeated `(quote x)` of the same datum `eq?`.
    pub fn constant(&mut self, v: Value) -> ConstId {
        if let Some(i) = self.consts.iter().position(|c| *c == v) {
            return ConstId(i as u32);
        }
        self.consts.push(v);
        ConstId(self.consts.len() as u32 - 1)
    }

    /// Patch a lambda's body once it has been built — lambdas are registered
    /// before their bodies are expanded so that a recursive reference can name
    /// them.
    pub fn set_lambda_body(&mut self, id: LambdaId, body: NodeId) {
        self.lambdas[id.index()].body = body;
    }

    pub fn var_info_mut(&mut self, id: VarId) -> &mut VarInfo {
        &mut self.vars[id.index()]
    }

    pub fn finish(self, body: NodeId) -> Program {
        Program {
            nodes: self.nodes,
            spans: self.spans,
            vars: self.vars,
            lambdas: self.lambdas,
            consts: self.consts,
            body,
        }
    }
}

impl Default for Builder {
    fn default() -> Builder {
        Builder::new()
    }
}
