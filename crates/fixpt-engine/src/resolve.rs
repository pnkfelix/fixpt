//! Lexical addressing for the AST interpreter.
//!
//! The Core IR is alpha-renamed but not addressed: a `Ref` names a [`VarId`],
//! not a location. This pass walks the tree once and records, for each `Ref`
//! and `Set` node, the `(depth, index)` of the variable in the environment
//! chain the interpreter will have built at that point.
//!
//! Keying by *node* rather than by variable is what makes this correct: the
//! same variable is at different depths at different use sites, and each node
//! occupies exactly one position in the tree.
//!
//! The chain walk this enables is O(lexical depth), not O(1) — that is the
//! honest cost of an environment-chain interpreter, and it is one of the real
//! differences between the two engines. The bytecode compiler in `vm` builds
//! flat closures instead and gets O(1).

use fixpt_core::ir::{LambdaId, Node, NodeId, Program, VarId};

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Addr {
    pub depth: u32,
    pub index: u32,
}

pub struct Addressing {
    /// Indexed by `NodeId`. `None` for nodes that are not variable references.
    addr: Vec<Option<Addr>>,
}

impl Addressing {
    pub fn empty() -> Addressing {
        Addressing { addr: Vec::new() }
    }

    pub fn get(&self, n: NodeId) -> Addr {
        self.addr[n.index()].expect("a Ref or Set node must have been addressed")
    }
}

pub fn resolve(program: &Program) -> Addressing {
    let mut r = Resolver { addr: vec![None; program.nodes.len()], scopes: Vec::new() };
    r.walk(program, program.body);
    // A lambda reachable only through a constant or never walked would leave
    // holes; walking every lambda directly closes them.
    for i in 0..program.lambdas.len() {
        r.walk_lambda(program, LambdaId(i as u32));
    }
    Addressing { addr: r.addr }
}

struct Resolver {
    addr: Vec<Option<Addr>>,
    scopes: Vec<Vec<VarId>>,
}

impl Resolver {
    fn lookup(&self, v: VarId) -> Option<Addr> {
        for (back, scope) in self.scopes.iter().rev().enumerate() {
            if let Some(i) = scope.iter().position(|x| *x == v) {
                return Some(Addr { depth: back as u32, index: i as u32 });
            }
        }
        None
    }

    fn record(&mut self, node: NodeId, v: VarId) {
        // A variable with no binding scope can only come from a malformed
        // program; leaving the slot `None` makes that a clear panic at the use
        // site rather than a silently wrong address.
        if let Some(a) = self.lookup(v) {
            self.addr[node.index()] = Some(a);
        }
    }

    fn walk_lambda(&mut self, program: &Program, id: LambdaId) {
        let info = program.lambda(id);
        let mut scope = info.params.clone();
        if let Some(r) = info.rest {
            scope.push(r);
        }
        self.scopes.push(scope);
        self.walk(program, info.body);
        self.scopes.pop();
    }

    fn walk(&mut self, program: &Program, id: NodeId) {
        match program.node(id) {
            Node::Const(_) | Node::GlobalRef(_) => {}
            Node::Ref(v) => self.record(id, *v),
            Node::Set(v, e) => {
                self.record(id, *v);
                self.walk(program, *e);
            }
            Node::GlobalSet(_, e) => self.walk(program, *e),
            Node::If(a, b, c) => {
                self.walk(program, *a);
                self.walk(program, *b);
                self.walk(program, *c);
            }
            Node::Seq(items) => {
                for n in items.iter() {
                    self.walk(program, *n);
                }
            }
            Node::Let { vars, inits, body } => {
                for n in inits.iter() {
                    self.walk(program, *n);
                }
                self.scopes.push(vars.to_vec());
                self.walk(program, *body);
                self.scopes.pop();
            }
            Node::Fix { vars, inits, body } => {
                self.scopes.push(vars.to_vec());
                for n in inits.iter() {
                    self.walk(program, *n);
                }
                self.walk(program, *body);
                self.scopes.pop();
            }
            Node::Lambda(l) => self.walk_lambda(program, *l),
            Node::App { rator, rands } => {
                self.walk(program, *rator);
                for n in rands.iter() {
                    self.walk(program, *n);
                }
            }
            Node::PrimCall { rands, .. } => {
                for n in rands.iter() {
                    self.walk(program, *n);
                }
            }
        }
    }
}
