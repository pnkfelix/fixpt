//! Register code for a lambda (PLAN.md 13h′): the MacScheme machine's
//! instructions (`fixpt_heap::layout::regcode`), made from the same trees,
//! as its cellular word's twin.
//!
//! Where values live, the first way: a procedure that neither calls nor
//! calls out (a leaf, loops aside, and plain calls in tail position, made
//! by moving the arguments into place: `r_leaf_tail_call`) keeps its
//! parameters, its `let`s and its temporaries in registers. Any other keeps its parameters and `let`s in
//! its frame, made on entry, since a call or a call-out may collect and
//! then only the frame holds values; its registers are only temporaries,
//! and arguments on their way to a call. What this compiler does not do yet
//! (`letrec`, `prompt`, `tagcase`, products, sums, arrays and bloblets
//! made, standard operations as values), it declines: the lambda keeps
//! its stack code alone. Past `REGS` values (arguments, parameters, free
//! values, operands), REG1…REG7 hold the first seven and REG8 a list of the
//! rest, Larceny's convention (`r_args`).
//!
//! A `letrena`'s region is the heap's (`Heap::region_enter`), and its name
//! a variable whose value is the region's handle, for `rcons`; a closure
//! that allocates in the region captures it like any other.

use super::{find, Compiler, Env, Loc, This};

fn two() -> Value {
    Value::fixnum(2)
}
use crate::ast::{BlobletOp, Exp, ExpId};
use fixpt_heap::layout::regcode::{op, REGS};
use fixpt_heap::layout::cellular::routine;
use fixpt_heap::layout::kind;
use fixpt_heap::Value;
use fixpt_read::Sym;

/// Where a variable is, to register code.
#[derive(Clone, Copy, PartialEq)]
enum RLoc {
    Reg(usize),
    Slot(usize),
    Free(usize),
    Global(Value),
    Loop,
    /// A `letrec` sibling not made yet, to be in frame slot `s`.
    Pending(usize),
    /// A constant, bound to the name (`r_const`): no place at all.
    Const(Value),
    /// A `letrec`-bound procedure only called in tail position, a join
    /// point (`r_join_ok`): its parameters' slots and label, `Gen::joins`'s.
    Join(usize),
    /// A lambda-lifted procedure (`Loc::Lifted`): only called.
    Lifted(usize),
}

/// An operand of a call-out: an expression, a constant, a procedure of
/// no arguments whose body is an expression (a `prompt`'s), a frame slot's
/// value, or a free value of the closure running.
#[derive(Clone, Copy)]
enum Arg {
    E(ExpId),
    /// An expression's value, not converted as the checker said it is
    /// (the conversion's own operand).
    AsIs(ExpId),
    V(Value),
    Thunk(ExpId),
    /// A variable's value, wherever it is (a lifted procedure's added
    /// argument).
    Name(Sym),
    Slot(usize),
    Lexical(usize),
}

enum RItem {
    Cell(Value),
    Label(usize),
    /// `branch` (false) or `branchf` (true) to a label.
    Branch(bool, usize),
    /// `brancht` to a label.
    BranchT(usize),
    /// The frame's size, known when the body is done.
    Frame,
    /// `global-guard g w` to a label: unless global cell `g` holds a
    /// closure made from word `w`.
    Guard(Value, Value, usize),
}

/// A standard operation, as register code does it.
enum Std {
    /// `op2 r`, operands in order, or swapped; then `not`, if asked.
    Op2 { r: &'static str, swap: bool, not: bool },
    Op1(&'static str),
    Op2Imm(&'static str, Value),
    Field(i64),
    /// A call-out: a runtime primitive, or a cellular routine.
    Prim(i64),
    /// A runtime primitive of one or two operands that never collects
    /// (`fixpt_runtime::never_collects`): in line, as `prim1`, `prim2` or
    /// `prim2imm`, its operands as `op2`'s.
    Pure(i64),
    Cellular(&'static str),
    /// Its argument itself (`%fx26-identity`).
    Identity,
    /// A reference written: `setfield 2`, then unit.
    Set,
    /// Arrays, the tag and key makers: several instructions (`r_app`).
    Special(&'static str),
    /// `(list x …)`: the pairs made in line (`r_cons_list`).
    List,
    /// `(apply f xs)`: `f` a `vsubr`, a closure of `%vlambda`'s over the
    /// procedure of one list, free value 0; that procedure, called with `xs`.
    Apply,
}

struct Gen {
    items: Vec<RItem>,
    leaf: bool,
    next_reg: usize,
    next_slot: usize,
    max_slot: usize,
    labels: usize,
    this: Option<(This, usize)>,
    /// In a procedure specialized at a lambda (`Compiler::spec`): where the
    /// parameter the lambda is, and the label at the body's start.
    spec: Option<(RLoc, usize)>,
    /// In a top-level definition's procedure: its name, its word, its
    /// arity, and the label at the body's start (`r_self_guarded`).
    own: Option<(Sym, Value, usize, usize)>,
    /// Whether a call of itself through its global was made a loop, in a
    /// fast version.
    looped: bool,
    /// The join points: where each one's parameters are, and its label.
    joins: Vec<(Vec<RLoc>, usize)>,
}

type O<T> = Option<T>;

impl Gen {
    fn cell(&mut self, v: Value) {
        self.items.push(RItem::Cell(v));
    }
    fn op(&mut self, name: &str, operands: &[Value]) {
        self.cell(Value::fixnum(op(name) as i64));
        for x in operands {
            self.cell(*x);
        }
    }
    fn n(k: usize) -> Value {
        Value::fixnum(k as i64)
    }
    fn label(&mut self) -> usize {
        self.labels += 1;
        self.labels - 1
    }
    fn reg(&mut self) -> O<usize> {
        self.next_reg += 1;
        (self.next_reg <= REGS).then_some(self.next_reg)
    }
    fn slot(&mut self) -> usize {
        self.next_slot += 1;
        self.max_slot = self.max_slot.max(self.next_slot);
        self.next_slot - 1
    }
    /// Pop the frame, if there is one, before leaving.
    fn leave(&mut self) {
        if !self.leaf {
            self.cell(Value::fixnum(op("pop") as i64));
            self.items.push(RItem::Frame);
        }
    }
    fn done(&mut self, tail: bool) {
        if tail {
            self.leave();
            self.op("return", &[]);
        }
    }

    fn assemble(self) -> Vec<Value> {
        let frame = self.max_slot;
        let size = |i: &RItem| match i {
            RItem::Cell(_) | RItem::Frame => 1,
            RItem::Label(_) => 0,
            RItem::Branch(..) | RItem::BranchT(_) => 2,
            RItem::Guard(..) => 4,
        };
        let mut at = vec![0i64; self.labels];
        let mut pos = 0;
        for i in &self.items {
            if let RItem::Label(n) = i {
                at[*n] = pos;
            }
            pos += size(i);
        }
        let mut cells = Vec::new();
        let mut pos = 0;
        for i in &self.items {
            match i {
                RItem::Cell(x) => cells.push(*x),
                RItem::Frame => cells.push(Value::fixnum(frame as i64)),
                RItem::Label(_) => {}
                RItem::Branch(f, n) => {
                    cells.push(Value::fixnum(op(if *f { "branchf" } else { "branch" }) as i64));
                    cells.push(Value::fixnum(at[*n] - (pos + 2)));
                }
                RItem::BranchT(n) => {
                    cells.push(Value::fixnum(op("brancht") as i64));
                    cells.push(Value::fixnum(at[*n] - (pos + 2)));
                }
                RItem::Guard(c, w, n) => {
                    cells.extend([Value::fixnum(op("global-guard") as i64), *c, *w, Value::fixnum(at[*n] - (pos + 4))]);
                }
            }
            pos += size(i);
        }
        cells
    }
}

impl Compiler<'_> {
    /// None, remembering why, for [`Compiler::register_report`].
    fn decline<T>(&mut self, why: &str) -> O<T> {
        if self.declined.is_none() {
            self.declined = Some(why.to_string());
        }
        None
    }

    /// A lambda's register code, whose closure captures `inner`'s free
    /// values in order, or none where this compiler declines.
    /// A lambda's register code: in two versions where that is sound and
    /// something is gained (`docs/performance.md`, "Versions"): its body
    /// compiled assuming every global it inlines, specializes or calls
    /// itself through holds what it held when compiled, behind one guard
    /// for each at its start; and, where a guard fails, compiled as ever.
    /// Sound where no global can change during a run of the body: its
    /// effect summary is less than 3 (it keeps no continuation for later,
    /// writes no global). Only where the body makes no closure, so that
    /// compiling it twice compiles nothing else twice.
    pub(super) fn register_code(&mut self, params: &[Sym], body: ExpId, inner: &Env, this: Option<This>, own: Option<(Sym, Value)>) -> O<Vec<Value>> {
        if self.summary_of(body) < 3 && self.inline_room(body, i64::MAX / 2) >= 0 && self.r_fast_may_pay(params, body, inner, this, own) {
            let (assumed, declined) = (self.assume.replace(Vec::new()), self.declined.take());
            let fast = self.register_body(params, body, inner, this, own);
            let assumptions = std::mem::replace(&mut self.assume, assumed).unwrap_or_default();
            self.declined = declined;
            // Worth it where the fast version is a leaf, or loops where the
            // plain one calls: else its guards, all run on entry, cost more
            // than the plain version's, each run where its call is.
            if let Some(mut fast) = fast.filter(|f| !assumptions.is_empty() && (f.leaf || f.looped)) {
                let mut plain = self.register_body(params, body, inner, this, own)?;
                let frame = fast.max_slot.max(plain.max_slot);
                (fast.max_slot, plain.max_slot) = (frame, frame);
                let (fast, plain) = (fast.assemble(), plain.assemble());
                // `args n`, the guards, the fast body, the plain one.
                let plain_at = 2 + 4 * assumptions.len() as i64 + (fast.len() as i64 - 2);
                let mut cells = fast[..2].to_vec();
                for (k, (cell, word)) in assumptions.iter().enumerate() {
                    let at = 2 + 4 * k as i64;
                    cells.extend([Value::fixnum(op("global-guard") as i64), *cell, *word, Value::fixnum(plain_at - (at + 4))]);
                }
                cells.extend_from_slice(&fast[2..]);
                cells.extend_from_slice(&plain[2..]);
                return Some(cells);
            }
        }
        Some(self.register_body(params, body, inner, this, own)?.assemble())
    }

    /// Whether a fast version may be worth compiling, asked before it is:
    /// whether, with inlined calls no calls, the body would be a leaf; or it
    /// mentions its own name, and so may loop.
    fn r_fast_may_pay(&mut self, params: &[Sym], body: ExpId, inner: &Env, this: Option<This>, own: Option<(Sym, Value)>) -> bool {
        if own.is_some_and(|(n, _)| self.mentions(body, n)) {
            return true;
        }
        let outer = (self.assume.replace(Vec::new()), std::mem::replace(&mut self.own_now, own.map(|(n, _)| (n, params.len()))));
        let leaf = !self.r_collects(body, inner, this, true);
        (self.assume, self.own_now) = outer;
        leaf
    }

    /// The effect summary of `x`'s span (`Checker::effect_summaries`); 3, the
    /// most, if none was noted.
    fn summary_of(&mut self, x: ExpId) -> u8 {
        let span = self.c.arena.span_of(x);
        let c = self.c;
        let all = self.summaries.get_or_insert_with(|| c.effect_summaries());
        all.get(&(span.start, span.end)).copied().unwrap_or(3)
    }

    /// A lambda's body in register code, not yet assembled. In a fast
    /// version, where a call inlined or of itself in tail position is no
    /// call, a leaf maybe where the plain one is not.
    fn register_body(&mut self, params: &[Sym], body: ExpId, inner: &Env, this: Option<This>, own: Option<(Sym, Value)>) -> O<Gen> {
        let outer = std::mem::replace(&mut self.own_now, own.map(|(n, _)| (n, params.len())));
        let g = self.register_body_in(params, body, inner, this, own);
        self.own_now = outer;
        g
    }

    fn register_body_in(&mut self, params: &[Sym], body: ExpId, inner: &Env, this: Option<This>, own: Option<(Sym, Value)>) -> O<Gen> {
        // Past `REGS` parameters, the rest come as a list in REG8, taken
        // apart into the frame.
        let leaf = params.len() <= REGS && !self.r_collects(body, inner, this, true);
        // A leaf too where its only calls are plain tail calls; made so
        // first, and if that runs out of registers, made as before.
        if !leaf && params.len() <= REGS {
            self.tail_calls_leave = true;
            let leaves = !self.r_collects(body, inner, this, true);
            self.tail_calls_leave = false;
            if leaves {
                let declined = self.declined.clone();
                if let Some(g) = self.register_body_as(params, body, inner, this, own, true) {
                    return Some(g);
                }
                self.declined = declined;
            }
        }
        self.register_body_as(params, body, inner, this, own, leaf)
    }

    fn register_body_as(&mut self, params: &[Sym], body: ExpId, inner: &Env, this: Option<This>, own: Option<(Sym, Value)>, leaf: bool) -> O<Gen> {
        let mut g = Gen { items: Vec::new(), leaf, next_reg: 0, next_slot: 0, max_slot: 0, labels: 0, this: None, spec: None, own: None, joins: Vec::new(), looped: false };
        g.op("args", &[Gen::n(params.len())]);
        let mut env: Vec<(Sym, RLoc)> = Vec::new();
        for (n, l) in inner {
            env.push((*n, match l {
                Loc::Slot(i) => {
                    if leaf {
                        RLoc::Reg(i + 1)
                    } else {
                        RLoc::Slot(*i)
                    }
                }
                Loc::Free(i) => RLoc::Free(*i),
                Loc::Loop => RLoc::Loop,
                Loc::Global(g) => RLoc::Global(*g),
                Loc::Lifted(k) => RLoc::Lifted(*k),
                _ => return None,
            }));
        }
        if leaf {
            g.next_reg = params.len();
        } else {
            // The frame, and the parameters into it.
            g.cell(Value::fixnum(op("save") as i64));
            g.items.push(RItem::Frame);
            for i in 0..params.len() {
                let s = g.slot();
                if params.len() <= REGS || i + 1 < REGS {
                    g.op("store", &[Gen::n(i + 1), Gen::n(s)]);
                    continue;
                }
                g.op("reg", &[Gen::n(REGS)]);
                g.op("op1", &[Value::fixnum(routine("pair-car") as i64)]);
                g.op("setstk", &[Gen::n(s)]);
                if i + 1 < params.len() {
                    g.op("reg", &[Gen::n(REGS)]);
                    g.op("op1", &[Value::fixnum(routine("pair-cdr") as i64)]);
                    g.op("setreg", &[Gen::n(REGS)]);
                }
            }
        }
        if let Some(t) = this {
            let start = g.label();
            g.items.push(RItem::Label(start));
            g.this = Some((t, start));
        }
        if let Some(sp) = &self.spec {
            let at = self.r_where(&env, sp.param_name)?;
            let start = g.label();
            g.items.push(RItem::Label(start));
            g.spec = Some((at, start));
        }
        if let Some((name, word)) = own {
            let start = g.label();
            g.items.push(RItem::Label(start));
            g.own = Some((name, word, params.len(), start));
        }
        let mut te = inner.clone();
        self.r_exp(&mut g, body, &mut env, &mut te, true)?;
        Some(g)
    }

    /// The members' `lifts`, if the `letrec` `x`'s stack code lifted it;
    /// not in a body inlined or specialized here, which another program's
    /// text may have spans in common with.
    fn r_lifted(&self, x: ExpId) -> O<Vec<usize>> {
        if !self.inlining.is_empty() || self.spec.is_some() {
            return None;
        }
        let span = self.c.arena.span_of(x);
        self.lifted.get(&(span.start, span.end)).cloned().flatten()
    }

    fn r_where(&self, env: &[(Sym, RLoc)], n: Sym) -> O<RLoc> {
        env.iter().rev().find(|(m, _)| *m == n).map(|(_, l)| *l).or_else(|| match self.where_is(&Vec::new(), n) {
            Some(Loc::Global(g)) => Some(RLoc::Global(g)),
            _ => None,
        })
    }

    /// Whether `name`, applied to `n` arguments, is a standard operation
    /// register code does, and how.
    fn r_standard(&mut self, name: &str, n: usize) -> O<Std> {
        let op2 = |r, swap, not| Some(Std::Op2 { r, swap, not });
        match (name, n) {
            ("+", 2) => op2("int-add", false, false),
            ("-", 2) => op2("int-sub", false, false),
            ("<", 2) => op2("int-less", false, false),
            (">", 2) => op2("int-less", true, false),
            ("<=", 2) => op2("int-less", true, true),
            (">=", 2) => op2("int-less", false, true),
            ("=", 2) => op2("int-eq", false, false),
            ("char=?" | "symbol=?" | "wglobal=?" | "eq?" | "bool=?", 2) => op2("eq", false, false),
            ("not", 1) => Some(Std::Op2Imm("eq", Value::FALSE)),
            ("null?" | "datum-null?", 1) => Some(Std::Op2Imm("eq", Value::NULL)),
            ("car" | "datum-car", 1) => Some(Std::Op1("pair-car")),
            ("cdr" | "datum-cdr", 1) => Some(Std::Op1("pair-cdr")),
            ("get", 1) => Some(Std::Field(2)),
            ("cons" | "datum-cons", 2) => Some(Std::Cellular("cons")),
            ("set", 2) => Some(Std::Set),
            ("abort-current-continuation", 2) => Some(Std::Cellular("abort")),
            ("call-with-composable-continuation", 2) => Some(Std::Cellular("callcomp")),
            ("cwcc", 1) => Some(Std::Cellular("callcc")),
            ("with-mark", 3) => Some(Std::Cellular("withmark")),
            ("first-mark", 2) => Some(Std::Cellular("firstmark")),
            ("current-marks", 1) => Some(Std::Cellular("currentmarks")),
            ("marks-of", 2) => Some(Std::Cellular("marksof")),
            ("array-ref", 2) => Some(Std::Special("array-ref")),
            ("array-set!", 3) => Some(Std::Special("array-set!")),
            ("array-length", 1) => Some(Std::Special("array-length")),
            ("make-array", 2) => Some(Std::Special("make-array")),
            ("set-car!", 2) => Some(Std::Special("set-car!")),
            ("set-cdr!", 2) => Some(Std::Special("set-cdr!")),
            ("make-continuation-prompt-tag" | "make-continuation-mark-key", 0) => Some(Std::Special("make-box")),
            ("apply", 2) => Some(Std::Apply),
            ("list", _) => Some(Std::List),
            _ => {
                // What the cellular compiler does with one runtime
                // primitive, register code does too.
                let mut tmp = Vec::new();
                self.standard_on(name, n, &mut tmp).ok()?;
                let prim = Value::fixnum(routine("prim") as i64);
                match tmp[..] {
                    [] if n == 1 => Some(Std::Identity),
                    [super::Item::Cell(r), super::Item::Cell(p), super::Item::Cell(k)] if r == prim && k.as_fixnum() as usize == n => {
                        let d = fixpt_runtime::PRIMITIVES.get(p.as_fixnum() as usize);
                        if (n == 1 || n == 2) && d.is_some_and(|d| fixpt_runtime::never_collects(d.name)) {
                            Some(Std::Pure(p.as_fixnum()))
                        } else {
                            Some(Std::Prim(p.as_fixnum()))
                        }
                    }
                    _ => None,
                }
            }
        }
    }

    /// Register code for a standard operation as a value (`standard_value`):
    /// its operands are its parameters, in REG1…REGn already, and a
    /// call-out, if it is one, is made in a frame. None for one done in
    /// several instructions, or that takes control (the closure then has
    /// stack code only).
    pub(super) fn r_standard_word(&mut self, name: &str, n: usize) -> O<Vec<Value>> {
        let std = self.r_standard(name, n)?;
        let callout = matches!(std, Std::Prim(_) | Std::Cellular(_));
        let mut g = Gen { items: Vec::new(), leaf: !callout, next_reg: n, next_slot: 0, max_slot: 0, labels: 0, this: None, spec: None, own: None, joins: Vec::new(), looped: false };
        g.op("args", &[Gen::n(n)]);
        if callout {
            g.cell(Value::fixnum(op("save") as i64));
            g.items.push(RItem::Frame);
        }
        let r = |name: &str| Value::fixnum(routine(name) as i64);
        match std {
            Std::Op2 { r: o, swap, not } => {
                let (a, b) = if swap { (2, 1) } else { (1, 2) };
                g.op("reg", &[Gen::n(a)]);
                g.op("op2", &[r(o), Gen::n(b)]);
                if not {
                    g.op("op2imm", &[r("eq"), Value::FALSE]);
                }
            }
            Std::Op1(o) => {
                g.op("reg", &[Gen::n(1)]);
                g.op("op1", &[r(o)]);
            }
            Std::Op2Imm(o, v) => {
                g.op("reg", &[Gen::n(1)]);
                g.op("op2imm", &[r(o), v]);
            }
            Std::Field(k) => {
                g.op("reg", &[Gen::n(1)]);
                g.op("field", &[Value::fixnum(k)]);
            }
            Std::Identity => g.op("reg", &[Gen::n(1)]),
            Std::Prim(p) => g.op("prim", &[Value::fixnum(p), Gen::n(n)]),
            Std::Pure(p) => {
                g.op("reg", &[Gen::n(1)]);
                if n == 1 {
                    g.op("prim1", &[Value::fixnum(p)]);
                } else {
                    g.op("prim2", &[Value::fixnum(p), Gen::n(2)]);
                }
            }
            Std::Cellular("cons") => g.op("cellular", &[r("cons"), Gen::n(n)]),
            _ => return None,
        }
        g.done(true);
        Some(g.assemble())
    }

    /// The operator under the type abstractions, projections, ascriptions
    /// and conversions, which compile to nothing: `((proj car @r) xs)` is
    /// `car` applied.
    fn r_operator(&self, mut f: ExpId) -> ExpId {
        loop {
            match self.c.arena.exp_at(f) {
                Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => f = *body,
                _ => return f,
            }
        }
    }

    fn r_standard_name(&self, env: &[(Sym, RLoc)], f: ExpId) -> O<String> {
        match self.c.arena.exp_at(self.r_operator(f)) {
            Exp::Var(n) if self.r_where(env, *n).is_none() => Some(self.name(*n).to_string()),
            _ => None,
        }
    }

    /// Whether `f` is the procedure running, called with its arity: its own
    /// name, still bound where the procedure knows itself to be.
    fn r_self_known(&self, g: &Gen, f: ExpId, nargs: usize, te: &Env) -> bool {
        match (g.this, self.c.arena.exp_at(f)) {
            (Some((t, _)), Exp::Var(n)) => *n == t.name && find(te, *n) == Some(t.loc) && t.added + nargs == t.params,
            _ => false,
        }
    }

    fn r_self_call(&self, g: &Gen, f: ExpId, nargs: usize, te: &Env, tail: bool) -> bool {
        match (g.this, self.c.arena.exp_at(f)) {
            (Some((t, _)), Exp::Var(n)) => tail && *n == t.name && find(te, *n) == Some(t.loc) && t.added + nargs == t.params,
            _ => false,
        }
    }

    /// Whether evaluating `x` may call or call out, and so collect. Loops
    /// do not; declined forms are said to, which does not matter.
    fn r_collects(&mut self, x: ExpId, e: &Env, this: Option<This>, tail: bool) -> bool {
        if self.c.facts.changed(x) {
            return true;
        }
        match self.c.arena.exp_at(x).clone() {
            // Join points only: no closure made, and their calls are jumps.
            Exp::Letrec { bindings, body } if tail && (0..bindings.len()).all(|i| self.r_join_ok(&bindings, body, i)) => {
                let mut inner = e.clone();
                inner.extend(bindings.iter().map(|(n, _, _)| (*n, Loc::Loop)));
                self.r_collects(body, &inner, this, tail)
                    || bindings.iter().any(|(_, _, init)| match self.lambda_of(*init) {
                        Some((ps, lbody, _)) => {
                            let mut own = inner.clone();
                            own.extend(ps.iter().map(|p| (*p, Loc::Slot(usize::MAX))));
                            self.r_collects(lbody, &own, this, true)
                        }
                        None => true,
                    })
            }
            // A standard operation as a value: a closure made; `list`'s
            // then given to `%fx26-vlambda`, a call-out.
            Exp::Var(n) if self.where_is(e, n).is_none() && Self::has_standard_value(self.name(n)) => {
                !tail || self.name(n) == "list"
            }
            Exp::Var(_) | Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => false,
            // A closure made as the value: its call-out may collect, but
            // nothing is used after it (`r_lambda`).
            Exp::Lambda { .. } if tail => false,
            Exp::If { test, then, els } => {
                self.r_collects(test, e, this, false) || self.r_collects(then, e, this, tail) || self.r_collects(els, e, this, tail)
            }
            Exp::Let { bindings, body } => {
                bindings.iter().any(|(_, y)| self.r_collects(*y, e, this, false)) || self.r_collects(body, e, this, tail)
            }
            Exp::Begin(items) => match items.split_last() {
                Some((last, rest)) => rest.iter().any(|y| self.r_collects(*y, e, this, false)) || self.r_collects(*last, e, this, tail),
                None => false,
            },
            // A place is made and ended by calling out; a region for
            // analysis only is nothing at run time.
            Exp::LetRegion { form: crate::ast::RegionForm::Region | crate::ast::RegionForm::Freeze(_), body, .. } => self.r_collects(body, e, this, tail),
            Exp::LetRegion { .. } => true,
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => self.r_collects(body, e, this, tail),
            Exp::Extract(y, _) => self.r_collects(y, e, this, false),
            Exp::Bloblet { op: BlobletOp::Ref(_), args } => args.iter().any(|y| self.r_collects(*y, e, this, false)),
            Exp::TagCase { scrutinee, arms, els } => {
                self.r_collects(scrutinee, e, this, false)
                    || arms.iter().any(|a| self.r_collects(a.body, e, this, tail))
                    || els.is_some_and(|(_, b)| self.r_collects(b, e, this, tail))
            }
            Exp::App { fun, args } => {
                let args_collect = args.iter().any(|y| self.r_collects(*y, e, this, false));
                // A loop: a call of the procedure itself, in tail position.
                let loop_call = tail
                    && (matches!((this, self.c.arena.exp_at(fun)), (Some(t), Exp::Var(n))
                    if *n == t.name && t.added + args.len() == t.params)
                        || matches!(self.c.arena.exp_at(fun), Exp::Var(n) if find(e, *n) == Some(Loc::Loop)));
                let inline = match self.c.arena.exp_at(self.r_operator(fun)) {
                    Exp::Var(n) if self.where_is(e, *n).is_none() => {
                        let name = self.name(*n).to_string();
                        matches!(
                            self.r_standard(&name, args.len()),
                            Some(Std::Op1(_) | Std::Op2 { .. } | Std::Op2Imm(..) | Std::Field(_) | Std::Identity | Std::Set | Std::Pure(_))
                        )
                    }
                    _ => false,
                };
                // A plain call in tail position, deciding a leaf: nothing
                // is used after it, so it needs no frame (`r_leaf_tail_call`).
                let leaves = self.tail_calls_leave && tail && args.len() < REGS && self.r_plain_callee(fun, args.len(), e) && !self.r_collects(fun, e, this, false);
                args_collect || !(loop_call || inline || leaves || self.r_call_is_free(fun, args.len(), e, tail))
            }
            _ => true,
        }
    }

    /// Whether a call of global `fun` with `n` arguments, in a body's fast
    /// version (`register_code`), is no call: its own in tail position, a
    /// loop; or one inlined, whose body makes none.
    fn r_call_is_free(&mut self, fun: ExpId, n: usize, e: &Env, tail: bool) -> bool {
        if self.assume.is_none() {
            return false;
        }
        let Exp::Var(name) = *self.c.arena.exp_at(fun) else { return false };
        if !matches!(self.where_is(e, name), Some(Loc::Global(_))) || self.inlining.contains(&name) {
            return false;
        }
        if tail && self.own_now == Some((name, n)) && self.inlining.is_empty() {
            return true;
        }
        let Some(k) = self.inlines.iter().position(|i| i.name == name && i.params.len() == n) else { return false };
        let (body, genv_len) = (self.inlines[k].body, self.inlines[k].genv_len);
        let own: Env = self.inlines[k].params.iter().map(|p| (*p, Loc::Slot(usize::MAX))).collect();
        let outer = self.genv_limit.replace(genv_len);
        self.inlining.push(name);
        let collects = self.r_collects(body, &own, None, tail);
        self.inlining.pop();
        self.genv_limit = outer;
        !collects
    }

    /// Whether a call of `fun` with `n` arguments is a plain `invoke`: not a
    /// standard operation, an inlined or specialized global's, or a lifted
    /// procedure's, each compiled its own way.
    fn r_plain_callee(&self, fun: ExpId, n: usize, e: &Env) -> bool {
        let Exp::Var(name) = *self.c.arena.exp_at(fun) else { return true };
        match self.where_is(e, name) {
            None | Some(Loc::Lifted(_) | Loc::Loop | Loc::Pending(_)) => false,
            Some(Loc::Global(_)) => {
                !self.inlines.iter().any(|i| i.name == name && i.params.len() == n) && !self.specials.iter().any(|s| s.name == name && s.params.len() == n)
            }
            Some(_) => true,
        }
    }

    /// Whether `x` is a variable or a constant: evaluated in `RESULT` alone,
    /// with no effect, so it may wait until its value is needed.
    fn r_simple(&self, x: ExpId) -> bool {
        let plain = match self.c.arena.exp_at(x) {
            // Not a name a standard operation has, which may be one made a
            // value, a closure.
            Exp::Var(n) => !Self::has_standard_value(self.name(*n)),
            Exp::Int(_) | Exp::Bool(_) | Exp::Char(_) | Exp::Symbol(_) | Exp::Unit | Exp::Str(_) | Exp::Float(_) => true,
            _ => false,
        };
        plain && !self.c.facts.changed(x)
    }

    /// `x`'s value into `RESULT`; in tail position, returned.
    fn r_exp(&mut self, g: &mut Gen, x: ExpId, env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        // A procedure converted to a convention: made, then given to
        // `%fx26-convert` with what it is converted to.
        if let Some(k) = self.c.facts.conversion_code(x) {
            self.r_prim(g, "%fx26-convert", &[Arg::AsIs(x), Arg::V(Value::fixnum(k))], env, te)?;
            g.done(tail);
            return Some(());
        }
        // A module reshaped (`Checker::reshape`): kept in a slot, its values
        // the type wanted has into slots, and a product of them.
        if let Some(at) = self.c.facts.reshaped.get(&x).cloned() {
            if g.leaf {
                return self.decline("a module reshaped in a leaf");
            }
            let slots = g.next_slot;
            self.r_exp_as_is(g, x, env, te, false)?;
            let m = g.slot();
            g.op("setstk", &[Gen::n(m)]);
            let mut args = vec![Arg::V(Value::fixnum(37))];
            for i in &at {
                g.op("stack", &[Gen::n(m)]);
                g.op("field", &[Value::fixnum(*i as i64 + 2)]);
                let s = g.slot();
                g.op("setstk", &[Gen::n(s)]);
                args.push(Arg::Slot(s));
            }
            self.r_prim(g, "%make-frozen", &args, env, te)?;
            g.next_slot = slots;
            g.done(tail);
            return Some(());
        }
        self.r_exp_as_is(g, x, env, te, tail)
    }

    fn r_exp_as_is(&mut self, g: &mut Gen, x: ExpId, env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        if let Some(v) = self.r_const(env, x) {
            g.op("const", &[v]);
            g.done(tail);
            return Some(());
        }
        match self.c.arena.exp_at(x).clone() {
            Exp::Var(n) => {
                match self.r_where(env, n) {
                    Some(RLoc::Reg(k)) => g.op("reg", &[Gen::n(k)]),
                    Some(RLoc::Slot(s)) => g.op("stack", &[Gen::n(s)]),
                    Some(RLoc::Free(i)) => g.op("lexical", &[Gen::n(i)]),
                    Some(RLoc::Global(c)) => g.op("global", &[c]),
                    Some(RLoc::Loop | RLoc::Pending(_) | RLoc::Const(_) | RLoc::Join(_) | RLoc::Lifted(_)) => return None,
                    None if matches!(self.name(n), "nil" | "no-pair") => g.op("const", &[Value::NULL]),
                    // A standard operation as a value: its closure, of the
                    // word the stack code makes for it, and that word's
                    // register code. A leaf makes it only in tail position.
                    None if g.leaf && !tail => return self.decline("a standard operation as a value, in a leaf"),
                    None => {
                        let mut made = Vec::new();
                        if self.standard_value(&self.name(n).to_string(), &mut made).is_err() {
                            return self.decline("a standard operation as a value");
                        }
                        let Some(super::Item::Cell(w)) = made.get(1).cloned() else { return None };
                        g.op("lambda", &[w, Gen::n(0)]);
                        // `list`'s, a `vsubr`: that closure given to
                        // `%fx26-vlambda`.
                        if self.name(n) == "list" {
                            if g.leaf {
                                return self.decline("`list` as a value, in a leaf");
                            }
                            let p = fixpt_engine::cellular::runtime_primitive("%fx26-vlambda")? as i64;
                            g.op("setreg", &[Gen::n(1)]);
                            g.op("prim", &[Value::fixnum(p), Gen::n(1)]);
                        }
                    }
                }
                g.done(tail);
            }
            Exp::Int(k) => {
                g.op("const", &[Value::fixnum(k)]);
                g.done(tail);
            }
            Exp::Bool(b) => {
                g.op("const", &[Value::boolean(b)]);
                g.done(tail);
            }
            Exp::Char(ch) => {
                g.op("const", &[Value::char(ch)]);
                g.done(tail);
            }
            Exp::Str(s) => {
                let v = self.heap.make_string(&s);
                g.op("const", &[v]);
                g.done(tail);
            }
            Exp::Float(x) => {
                let v = self.heap.make_flonum(x);
                g.op("const", &[v]);
                g.done(tail);
            }
            Exp::Symbol(s) => {
                let v = self.heap.intern(self.c.interner.name(s));
                g.op("const", &[v]);
                g.done(tail);
            }
            Exp::Unit => {
                let u = self.unit();
                g.op("const", &[u]);
                g.done(tail);
            }
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => {
                self.r_exp(g, body, env, te, tail)?
            }
            // The region's name bound, as a `let`'s, to a region entered (an
            // arena, or a reap: never in a leaf), and left with the body's
            // value, which is so not in tail position.
            Exp::LetRegion { form, region, body } => {
                let Some(enter) = form.enter() else {
                    // A region for analysis only: nothing at run time.
                    return self.r_exp(g, body, env, te, tail);
                };
                if g.leaf {
                    return None;
                }
                let name = self.c.arena.dvar_name(region);
                let (depth, tdepth, regs, slots) = (env.len(), te.len(), g.next_reg, g.next_slot);
                self.r_prim(g, enter, &[], env, te)?;
                let h = g.slot();
                g.op("setstk", &[Gen::n(h)]);
                env.push((name, RLoc::Slot(h)));
                te.push((name, Loc::Slot(usize::MAX)));
                self.r_exp(g, body, env, te, false)?;
                let v = g.slot();
                g.op("setstk", &[Gen::n(v)]);
                self.r_prim(g, "%region-exit", &[Arg::Slot(h), Arg::Slot(v)], env, te)?;
                g.done(tail);
                env.truncate(depth);
                te.truncate(tdepth);
                g.next_reg = regs;
                g.next_slot = slots;
            }
            // A test known: the arm it takes, alone.
            Exp::If { test, then, els } if self.r_const(env, test).is_some() => {
                let arm = if self.r_const(env, test) == Some(Value::FALSE) { els } else { then };
                self.r_exp(g, arm, env, te, tail)?;
            }
            Exp::If { test, then, els } => {
                let (no, end) = (g.label(), g.label());
                self.r_branch_on(g, test, false, no, env, te)?;
                self.r_exp(g, then, env, te, tail)?;
                if !tail {
                    g.items.push(RItem::Branch(false, end));
                }
                g.items.push(RItem::Label(no));
                self.r_exp(g, els, env, te, tail)?;
                g.items.push(RItem::Label(end));
            }
            Exp::Begin(items) => {
                let Some((last, rest)) = items.split_last() else {
                    let u = self.unit();
                    g.op("const", &[u]);
                    g.done(tail);
                    return Some(());
                };
                for y in rest {
                    self.r_exp(g, *y, env, te, false)?;
                }
                self.r_exp(g, *last, env, te, tail)?;
            }
            Exp::Let { bindings, body } => self.r_let(g, &bindings, body, env, te, tail)?,
            // A lambda applied at once: a `let` (`applied_lambda`).
            Exp::App { fun, args } if let Some((ps, lbody)) = self.applied_lambda(fun, args.len()) => {
                let bindings: Vec<(Sym, ExpId)> = ps.into_iter().zip(args.iter().copied()).collect();
                self.r_let(g, &bindings, lbody, env, te, tail)?;
            }
            Exp::Extract(p, _) => {
                let i = *self.c.facts.field_index.get(&x)?;
                self.r_exp(g, p, env, te, false)?;
                g.op("field", &[Value::fixnum(i as i64 + 2)]);
                g.done(tail);
            }
            Exp::Bloblet { op: BlobletOp::Ref(i), args } => {
                self.r_exp(g, args[0], env, te, false)?;
                g.op("field", &[Value::fixnum(i as i64 + 2)]);
                g.done(tail);
            }
            Exp::Lambda { params, body } => {
                let ps: Vec<Sym> = params.iter().map(|(n, _)| *n).collect();
                self.r_lambda(g, &ps, body, env, te, None, None, tail)?;
                g.done(tail);
            }
            Exp::RLambda { region, lambda } => {
                let Exp::Lambda { params, body } = self.c.arena.exp_at(lambda).clone() else { unreachable!("parsed") };
                let ps: Vec<Sym> = params.iter().map(|(n, _)| *n).collect();
                self.r_lambda(g, &ps, body, env, te, None, Some(region), false)?;
                g.done(tail);
            }
            Exp::Sum(t, v) => {
                let tag = self.heap.intern(self.c.interner.name(t));
                self.r_prim(g, "%make-frozen", &[Arg::V(Value::fixnum(36)), Arg::V(tag), Arg::E(v)], env, te)?;
                g.done(tail);
            }
            Exp::Product(fields) => {
                let mut args = vec![Arg::V(Value::fixnum(37))];
                args.extend(fields.iter().map(|(_, f)| Arg::E(*f)));
                self.r_prim(g, "%make-frozen", &args, env, te)?;
                g.done(tail);
            }
            Exp::Bloblet { op, args } => {
                let es: Vec<Arg> = args.iter().map(|a| Arg::E(*a)).collect();
                match op {
                    BlobletOp::Make => self.r_prim(g, "%make-bloblet", &es, env, te)?,
                    BlobletOp::RMake => self.r_prim(g, "%region-make-bloblet", &es, env, te)?,
                    BlobletOp::Set(i) => {
                        self.r_prim(g, "%bloblet-set!", &[es[0], Arg::V(Value::fixnum(i as i64 + 2)), es[1]], env, te)?;
                        let u = self.unit();
                        g.op("const", &[u]);
                    }
                    BlobletOp::Byte => self.r_prim(g, "%bloblet-byte", &es, env, te)?,
                    BlobletOp::SetByte => {
                        self.r_prim(g, "%bloblet-set-byte!", &es, env, te)?;
                        let u = self.unit();
                        g.op("const", &[u]);
                    }
                    BlobletOp::Bytes => self.r_prim(g, "%bloblet-bytes", &es, env, te)?,
                    BlobletOp::Freeze | BlobletOp::Ref(_) => return self.decline("bloblet-freeze"),
                }
                g.done(tail);
            }
            Exp::Prompt { tag, body, handler } => {
                self.r_call_out(g, "cellular", routine("prompt") as i64, &[Arg::E(tag), Arg::E(handler), Arg::Thunk(body)], env, te)?;
                g.done(tail);
            }
            Exp::TagCase { scrutinee, arms, els } => self.r_tagcase(g, scrutinee, &arms, els, env, te, tail)?,
            Exp::Module(items) => self.r_module(g, &items, env, te, tail)?,
            Exp::With { module, body } => self.r_with(g, x, module, body, env, te, tail)?,
            // Lifted as its stack code lifted it (`Compiler::lift`).
            Exp::Letrec { bindings, body } if self.r_lifted(x).is_some() => {
                let ks = self.r_lifted(x).expect("lifted");
                let (depth, tdepth) = (env.len(), te.len());
                for ((n, _, _), k) in bindings.iter().zip(&ks) {
                    env.push((*n, RLoc::Lifted(*k)));
                    te.push((*n, Loc::Lifted(*k)));
                }
                self.r_exp(g, body, env, te, tail)?;
                env.truncate(depth);
                te.truncate(tdepth);
            }
            Exp::Letrec { bindings, body } => {
                let (depth, tdepth, slots, regs) = (env.len(), te.len(), g.next_slot, g.next_reg);
                let n = bindings.len();
                let joins: Vec<bool> = (0..n).map(|i| tail && self.r_join_ok(&bindings, body, i)).collect();
                // A leaf makes no closure; join points it may have.
                if g.leaf && !joins.iter().all(|j| *j) {
                    return None;
                }
                // A slot for each closure (a join point is none: its slot is
                // never used).
                let at: Vec<usize> = (0..n).map(|i| if joins[i] { usize::MAX } else { g.slot() }).collect();
                // Each closure made into its slot, a placeholder for a
                // sibling not made yet; then each placeholder patched.
                let mut patches = Vec::new();
                for (i, (name, _, init)) in bindings.iter().enumerate() {
                    if joins[i] {
                        patches.push(Vec::new());
                        continue;
                    }
                    let (ps, lbody, region) = self.lambda_of(*init)?;
                    let (mut own_env, mut own_te) = (env.clone(), te.clone());
                    for (k, (sib, _, _)) in bindings.iter().enumerate() {
                        let loops = k == i && self.loops_only(lbody, *sib, ps.len(), true);
                        own_env.push((*sib, if loops { RLoc::Loop } else { RLoc::Pending(at[k]) }));
                        own_te.push((*sib, if loops { Loc::Loop } else { Loc::Pending(at[k]) }));
                    }
                    let p = self.r_lambda(g, &ps, lbody, &mut own_env, &mut own_te, Some(*name), region, false)?;
                    g.op("setstk", &[Gen::n(at[i])]);
                    patches.push(p);
                }
                for (i, ps) in patches.iter().enumerate() {
                    for &(j, sibling) in ps {
                        g.op("load", &[Gen::n(1), Gen::n(sibling)]);
                        g.op("stack", &[Gen::n(at[i])]);
                        g.op("setfield", &[Value::fixnum((super::CLOSURE_FREE0 + j) as i64), Gen::n(1)]);
                    }
                }
                // Each join point's parameters' places, and its label: in
                // registers where its body makes no call (or in a leaf), so
                // many as leave half of them; else in frame slots.
                let mut named = te.clone();
                named.extend(bindings.iter().enumerate().map(|(k, (n, _, _))| (*n, if joins[k] { Loc::Loop } else { Loc::Slot(usize::MAX) })));
                let mut js = Vec::new();
                for (i, (_, _, init)) in bindings.iter().enumerate().filter(|(i, _)| joins[*i]) {
                    let (ps, lbody, _) = self.lambda_of(*init)?;
                    let in_regs = g.leaf || {
                        let mut own = named.clone();
                        own.extend(ps.iter().map(|p| (*p, Loc::Slot(usize::MAX))));
                        !self.r_collects(lbody, &own, g.this.map(|(t, _)| t), true) && g.next_reg + ps.len() <= REGS / 2
                    };
                    let mut pslots = Vec::new();
                    for _ in &ps {
                        pslots.push(if in_regs { RLoc::Reg(g.reg()?) } else { RLoc::Slot(g.slot()) });
                    }
                    let label = g.label();
                    g.joins.push((pslots.clone(), label));
                    js.push((i, ps, lbody, pslots, label, g.joins.len() - 1));
                }
                for (k, (name, _, _)) in bindings.iter().enumerate() {
                    let (l, t) = match js.iter().find(|j| j.0 == k) {
                        Some(j) => (RLoc::Join(j.5), Loc::Loop),
                        None => (RLoc::Slot(at[k]), Loc::Slot(usize::MAX)),
                    };
                    env.push((*name, l));
                    te.push((*name, t));
                }
                self.r_exp(g, body, env, te, tail)?;
                // Each join point's body, after the body, which ends every
                // path itself (it is in tail position): where its calls go.
                for (_, ps, lbody, pslots, label, _) in js {
                    g.items.push(RItem::Label(label));
                    let (d, t) = (env.len(), te.len());
                    for (p, l) in ps.iter().zip(&pslots) {
                        env.push((*p, *l));
                        te.push((*p, Loc::Slot(usize::MAX)));
                    }
                    self.r_exp(g, lbody, env, te, tail)?;
                    env.truncate(d);
                    te.truncate(t);
                }
                env.truncate(depth);
                te.truncate(tdepth);
                g.next_slot = slots;
                g.next_reg = regs;
            }
            Exp::App { fun, args } => self.r_app(g, x, fun, &args, env, te, tail)?,
        }
        Some(())
    }

    /// A `let`: each value made, in the scope outside, and kept in a
    /// register where no call comes before the body is done with it (else
    /// the frame); a constant bound as itself.
    /// A module (`docs/research/first-class-modules.md`): its items kept in
    /// frame slots in order, as its stack code keeps them, a `define-rec`'s
    /// closures as a `letrec`'s are (with no join points); then the product
    /// of its values.
    fn r_module(&mut self, g: &mut Gen, items: &[crate::ast::ModItem], env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        use crate::ast::ModItem;
        if g.leaf {
            return self.decline("a module in a leaf");
        }
        let (depth, tdepth, slots) = (env.len(), te.len(), g.next_slot);
        let mut vals = vec![Arg::V(Value::fixnum(37))];
        let bind = |g: &mut Gen, env: &mut Vec<(Sym, RLoc)>, te: &mut Env, n: Sym| {
            let s = g.slot();
            g.op("setstk", &[Gen::n(s)]);
            env.push((n, RLoc::Slot(s)));
            te.push((n, Loc::Slot(usize::MAX)));
            s
        };
        for item in items {
            match item {
                ModItem::Desc { .. } => {}
                ModItem::Abs { up, down, up_fn, down_fn, .. } => {
                    for (n, f) in [(*up, *up_fn), (*down, *down_fn)] {
                        self.r_exp(g, f, env, te, false)?;
                        bind(g, env, te, n);
                    }
                }
                ModItem::Val { name, init, .. } => {
                    self.r_exp(g, *init, env, te, false)?;
                    vals.push(Arg::Slot(bind(g, env, te, *name)));
                }
                ModItem::Rec(group) => {
                    let at: Vec<usize> = group.iter().map(|_| g.slot()).collect();
                    let mut patches = Vec::new();
                    for (i, (name, _, init)) in group.iter().enumerate() {
                        let (ps, lbody, region) = self.lambda_of(*init)?;
                        let (mut own_env, mut own_te) = (env.clone(), te.clone());
                        for (k, (sib, _, _)) in group.iter().enumerate() {
                            let loops = k == i && self.loops_only(lbody, *sib, ps.len(), true);
                            own_env.push((*sib, if loops { RLoc::Loop } else { RLoc::Pending(at[k]) }));
                            own_te.push((*sib, if loops { Loc::Loop } else { Loc::Pending(at[k]) }));
                        }
                        let p = self.r_lambda(g, &ps, lbody, &mut own_env, &mut own_te, Some(*name), region, false)?;
                        g.op("setstk", &[Gen::n(at[i])]);
                        patches.push(p);
                    }
                    for (i, ps) in patches.iter().enumerate() {
                        for &(j, sibling) in ps {
                            g.op("load", &[Gen::n(1), Gen::n(sibling)]);
                            g.op("stack", &[Gen::n(at[i])]);
                            g.op("setfield", &[Value::fixnum((super::CLOSURE_FREE0 + j) as i64), Gen::n(1)]);
                        }
                    }
                    for (k, (n, _, _)) in group.iter().enumerate() {
                        env.push((*n, RLoc::Slot(at[k])));
                        te.push((*n, Loc::Slot(usize::MAX)));
                        vals.push(Arg::Slot(at[k]));
                    }
                }
            }
        }
        self.r_prim(g, "%make-frozen", &vals, env, te)?;
        env.truncate(depth);
        te.truncate(tdepth);
        g.next_slot = slots;
        g.done(tail);
        Some(())
    }

    /// `with`: the module's values, by position, kept in frame slots; then
    /// the body.
    #[allow(clippy::too_many_arguments)]
    fn r_with(&mut self, g: &mut Gen, x: ExpId, module: Sym, body: ExpId, env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        if g.leaf {
            return self.decline("a `with` in a leaf");
        }
        let names = self.c.facts.with_vals.get(&x)?.clone();
        let (depth, tdepth, slots) = (env.len(), te.len(), g.next_slot);
        let at: Vec<usize> = names.iter().map(|_| g.slot()).collect();
        for (i, n) in names.iter().enumerate() {
            match self.r_where(env, module)? {
                RLoc::Reg(k) => g.op("reg", &[Gen::n(k)]),
                RLoc::Slot(s) => g.op("stack", &[Gen::n(s)]),
                RLoc::Free(k) => g.op("lexical", &[Gen::n(k)]),
                RLoc::Global(c) => g.op("global", &[c]),
                _ => return self.decline("a `with` of a module not in a place"),
            }
            g.op("field", &[Value::fixnum(i as i64 + 2)]);
            g.op("setstk", &[Gen::n(at[i])]);
            env.push((*n, RLoc::Slot(at[i])));
            te.push((*n, Loc::Slot(usize::MAX)));
        }
        self.r_exp(g, body, env, te, tail)?;
        env.truncate(depth);
        te.truncate(tdepth);
        g.next_slot = slots;
        Some(())
    }

    fn r_let(&mut self, g: &mut Gen, bindings: &[(Sym, ExpId)], body: ExpId, env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        let (depth, tdepth, regs, slots) = (env.len(), te.len(), g.next_reg, g.next_slot);
        let inits: Vec<Option<ExpId>> = bindings.iter().map(|(_, i)| Some(*i)).collect();
        let mut inner = te.clone();
        inner.extend(bindings.iter().map(|(n, _)| (*n, Loc::Slot(usize::MAX))));
        let body_collects = !g.leaf && self.r_collects(body, &inner, g.this.map(|(t, _)| t), tail);
        let in_regs = self.r_in_regs(g, &inits, te, body_collects);
        let mut bound = Vec::new();
        for ((n, init), reg) in bindings.iter().zip(in_regs) {
            // A constant is bound as itself.
            if let Some(v) = self.r_const(env, *init) {
                bound.push((*n, RLoc::Const(v)));
                continue;
            }
            self.r_exp(g, *init, env, te, false)?;
            bound.push((*n, Self::r_keep(g, reg)?));
        }
        for (n, l) in bound {
            env.push((n, l));
            te.push((n, Loc::Slot(usize::MAX)));
        }
        self.r_exp(g, body, env, te, tail)?;
        env.truncate(depth);
        te.truncate(tdepth);
        g.next_reg = regs;
        g.next_slot = slots;
        Some(())
    }

    #[allow(clippy::too_many_arguments)]
    fn r_app(&mut self, g: &mut Gen, x: ExpId, f: ExpId, args: &[ExpId], env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        // A join point's call: each argument made and kept (a register in a
        // leaf, else a frame slot), then each into its parameter's place,
        // and a jump. (Before the procedure's own loop: a join point may
        // have its name.)
        if let Exp::Var(n) = *self.c.arena.exp_at(f)
            && let Some(RLoc::Join(j)) = self.r_where(env, n)
        {
            let (params, label) = g.joins[j].clone();
            if !tail || args.len() != params.len() {
                return self.decline("a join point called not in tail position");
            }
            let (regs, slots) = (g.next_reg, g.next_slot);
            // Each kept in a register where no later argument calls.
            let inits: Vec<Option<ExpId>> = args.iter().map(|a| Some(*a)).collect();
            let in_regs = self.r_in_regs(g, &inits, te, false);
            let mut made = Vec::new();
            for (a, reg) in args.iter().zip(in_regs) {
                self.r_exp(g, *a, env, te, false)?;
                made.push(Self::r_keep(g, reg)?);
            }
            for (m, p) in made.iter().zip(&params) {
                match (m, p) {
                    (RLoc::Reg(a), RLoc::Reg(b)) => g.op("movereg", &[Gen::n(*a), Gen::n(*b)]),
                    (RLoc::Slot(a), RLoc::Reg(b)) => g.op("load", &[Gen::n(*b), Gen::n(*a)]),
                    (RLoc::Reg(a), RLoc::Slot(b)) => {
                        g.op("reg", &[Gen::n(*a)]);
                        g.op("setstk", &[Gen::n(*b)]);
                    }
                    (RLoc::Slot(a), RLoc::Slot(b)) => {
                        g.op("stack", &[Gen::n(*a)]);
                        g.op("setstk", &[Gen::n(*b)]);
                    }
                    _ => return None,
                }
            }
            g.items.push(RItem::Branch(false, label));
            g.next_reg = regs;
            g.next_slot = slots;
            return Some(());
        }
        if self.r_self_call(g, f, args.len(), te, tail) {
            return self.r_loop(g, args, env, te);
        }
        if let (Some(sp), Some((at, start))) = (self.spec.clone(), g.spec) {
            let is_param = |c: &Self, env: &[(Sym, RLoc)], x: ExpId| matches!(*c.c.arena.exp_at(x), Exp::Var(n) if n == sp.param_name && c.r_where(env, n) == Some(at));
            if is_param(self, env, f) && args.len() == sp.arity {
                return self.r_spec_lambda(g, &sp, at, args, env, te, tail);
            }
            // Its own name is its own global here: in an inlined body, or
            // the lambda's, the parameter is not in scope.
            if matches!(*self.c.arena.exp_at(f), Exp::Var(n) if n == sp.name && matches!(self.r_where(env, n), Some(RLoc::Global(_))))
                && args.len() == sp.n
                && is_param(self, env, args[sp.param])
            {
                return self.r_self_guarded(g, sp.cell, sp.word, start, f, args, env, te, tail);
            }
        }
        // A top-level procedure calling itself through its global, its own
        // name not an inlined body's, which may name an older global.
        if let Some((name, word, n, start)) = g.own
            && self.inlining.is_empty()
            && args.len() == n
            && let Exp::Var(m) = *self.c.arena.exp_at(f)
            && m == name
            && let Some(RLoc::Global(cell)) = self.r_where(env, m)
        {
            return self.r_self_guarded(g, cell, word, start, f, args, env, te, tail);
        }
        if let Some(name) = self.r_standard_name(env, f) {
            let Some(std) = self.r_standard(&name, args.len()) else {
                return self.decline(&format!("standard `{name}`"));
            };
            match std {
                Std::Op2 { r, swap, not } => {
                    let (x, y) = (args[0], args[1]);
                    // A chain of `+`, and `-` of constants, with one operand
                    // not a constant, deeper than here: that one, and then
                    // the constants' sum at once. Integers are exact, so the
                    // order they are added in cannot matter.
                    let adds = |c: &Self, e: ExpId| match c.c.arena.exp_at(e) {
                        Exp::App { fun, args } => args.len() == 2 && matches!(c.r_standard_name(env, *fun).as_deref(), Some("+" | "-")),
                        _ => false,
                    };
                    if matches!(name.as_str(), "+" | "-")
                        && (adds(self, x) || adds(self, y))
                        && let Some((Some(core), k)) = self.r_split_app(env, &name, args)
                        && core != x
                        && core != y
                    {
                        self.r_exp(g, core, env, te, false)?;
                        if k > 0 {
                            g.op("op2imm", &[Value::fixnum(routine("int-add") as i64), Value::fixnum(k)]);
                        } else if k < 0 {
                            g.op("op2imm", &[Value::fixnum(routine("int-sub") as i64), Value::fixnum(-k)]);
                        }
                        g.done(tail);
                        return Some(());
                    }
                    // Operands trade places only where one is a variable or
                    // a constant, which neither has an effect nor sees one
                    // (only a definition writes a global); else they run as
                    // written. A constant goes second, an immediate, where
                    // the operation does not care which.
                    // (Asked only where it can matter, and a literal first:
                    // what is known is looked up, and that costs.)
                    let literal = |c: &Self, e: ExpId| matches!(c.c.arena.exp_at(e), Exp::Int(_) | Exp::Bool(_) | Exp::Char(_));
                    let free = |c: &mut Self, e: ExpId| c.r_simple(e) || c.r_const(env, e).is_some();
                    if swap && !free(self, x) && !free(self, y) {
                        self.r_binary_swapped(g, r, x, y, env, te)?;
                    } else if swap || (matches!(r, "int-add" | "eq" | "int-eq") && literal(self, x) && self.r_const(env, y).is_none()) {
                        self.r_binary(g, r, y, x, env, te)?;
                    } else {
                        self.r_binary(g, r, x, y, env, te)?;
                    }
                    if not {
                        g.op("op2imm", &[Value::fixnum(routine("eq") as i64), Value::FALSE]);
                    }
                }
                Std::Op1(r) => {
                    self.r_exp(g, args[0], env, te, false)?;
                    g.op("op1", &[Value::fixnum(routine(r) as i64)]);
                }
                Std::Op2Imm(r, v) => {
                    self.r_exp(g, args[0], env, te, false)?;
                    g.op("op2imm", &[Value::fixnum(routine(r) as i64), v]);
                }
                Std::Field(k) => {
                    self.r_exp(g, args[0], env, te, false)?;
                    g.op("field", &[Value::fixnum(k)]);
                }
                Std::Prim(p) => {
                    let es: Vec<Arg> = args.iter().map(|a| Arg::E(*a)).collect();
                    self.r_call_out(g, "prim", p, &es, env, te)?;
                }
                Std::Pure(p) if args.len() == 1 => {
                    self.r_exp(g, args[0], env, te, false)?;
                    g.op("prim1", &[Value::fixnum(p)]);
                }
                Std::Pure(p) => match self.r_operands(g, args[0], args[1], env, te, true)? {
                    (Some(v), _) => g.op("prim2imm", &[Value::fixnum(p), v]),
                    (None, Some(k)) => g.op("prim2", &[Value::fixnum(p), Gen::n(k)]),
                    (None, None) => return None,
                },
                // In tail position a mark replaces this frame's, as stack
                // code's `withmark-tail` does: the arguments made, the frame
                // left, and the call-out, which calls the thunk as a tail
                // call.
                Std::Cellular("withmark") if tail => {
                    let es: Vec<Arg> = args.iter().map(|a| Arg::E(*a)).collect();
                    self.r_args(g, &es, env, te, None)?;
                    g.leave();
                    g.op("cellular", &[Value::fixnum(routine("withmark-tail") as i64), Gen::n(3)]);
                    // Never reached (the call-out goes on in the thunk):
                    // register code ends each path so.
                    g.op("return", &[]);
                    return Some(());
                }
                Std::Cellular(r) => {
                    let es: Vec<Arg> = args.iter().map(|a| Arg::E(*a)).collect();
                    self.r_call_out(g, "cellular", routine(r) as i64, &es, env, te)?;
                }
                Std::Identity => self.r_exp(g, args[0], env, te, false)?,
                Std::Set => {
                    let k = self.r_operands(g, args[0], args[1], env, te, false)?.1?;
                    g.op("setfield", &[Value::fixnum(2), Gen::n(k)]);
                    let u = self.unit();
                    g.op("const", &[u]);
                }
                Std::Special(what) => self.r_special(g, what, args, env, te)?,
                Std::List => {
                    if g.leaf {
                        return self.decline("a call-out in a leaf");
                    }
                    let slots = g.next_slot;
                    let es: Vec<Arg> = args.iter().map(|a| Arg::E(*a)).collect();
                    let kept = self.r_keep_args(g, &es, env, te, true, None)?;
                    self.r_cons_list(g, &es, &kept, 0, env, te)?;
                    g.next_slot = slots;
                }
                Std::Apply => {
                    if g.leaf {
                        return self.decline("a call in a leaf");
                    }
                    // `f` and `xs` in order; `f`'s procedure kept in a slot
                    // while `xs` moves to REG1, copied there unless the
                    // checker found it at `acyclic` (`apply_shares`).
                    let (regs, slots) = (g.next_reg, g.next_slot);
                    let es: Vec<Arg> = args.iter().map(|a| Arg::E(*a)).collect();
                    self.r_args(g, &es, env, te, None)?;
                    let s = g.slot();
                    g.op("reg", &[Gen::n(1)]);
                    g.op("field", &[Value::fixnum(super::CLOSURE_FREE0 as i64)]);
                    g.op("setstk", &[Gen::n(s)]);
                    g.op("reg", &[Gen::n(2)]);
                    g.op("setreg", &[Gen::n(1)]);
                    if !self.c.facts.apply_shares.contains(&x) {
                        let p = fixpt_engine::cellular::runtime_primitive("%fx26-list-copy")? as i64;
                        g.op("prim", &[Value::fixnum(p), Gen::n(1)]);
                        g.op("setreg", &[Gen::n(1)]);
                    }
                    g.op("stack", &[Gen::n(s)]);
                    self.r_invoke(g, 1, tail);
                    g.next_reg = regs;
                    g.next_slot = slots;
                    return Some(());
                }
            }
            g.done(tail);
            return Some(());
        }
        // A call: the arguments into REG1…REGn, the procedure in RESULT.
        // An inlined call: in a fast version, no call, so in a leaf too.
        if let Some((k, cell)) = self.r_inlined(env, f, args.len()) {
            if self.assume.is_none() && g.leaf {
                return self.decline("a call in a leaf");
            }
            return self.r_inline(g, k, cell, f, args, env, te, tail);
        }
        if g.leaf && tail && args.len() < REGS && self.r_specialized(env, f, args).is_none() && !matches!(self.r_var(env, f), Some(RLoc::Lifted(_))) {
            return self.r_leaf_tail_call(g, f, args, env, te);
        }
        if g.leaf {
            return self.decline("a call in a leaf");
        }
        if let Some((k, cell, lam)) = self.r_specialized(env, f, args) {
            return self.r_specialize(g, k, cell, lam, args, env, te, tail);
        }
        // A lifted procedure's call: the names it would have captured,
        // then the arguments, into REG1…REGn; its closure, a constant.
        if let Exp::Var(n) = *self.c.arena.exp_at(f)
            && let Some(RLoc::Lifted(k)) = self.r_where(env, n)
        {
            let mut all: Vec<Arg> = self.lifts[k].added.iter().map(|a| Arg::Name(*a)).collect();
            all.extend(args.iter().map(|a| Arg::E(*a)));
            let closure = self.lifts[k].closure;
            self.r_args(g, &all, env, te, None)?;
            g.op("const", &[closure]);
            if tail {
                g.leave();
                g.op("tailinvoke", &[Gen::n(all.len())]);
            } else {
                g.op("invoke", &[Gen::n(all.len())]);
            }
            return Some(());
        }
        let es: Vec<Arg> = args.iter().map(|a| Arg::E(*a)).collect();
        // A call of the procedure itself, not in tail position: by its own
        // entry, with no closure fetched.
        if !tail && self.r_self_known(g, f, args.len(), te) {
            self.r_args(g, &es, env, te, None)?;
            g.op("invokeself", &[Gen::n(args.len())]);
            return Some(());
        }
        self.r_args(g, &es, env, te, Some(f))?;
        if tail {
            g.leave();
            g.op("tailinvoke", &[Gen::n(args.len())]);
        } else {
            g.op("invoke", &[Gen::n(args.len())]);
        }
        Some(())
    }

    /// Which of `inlines`, and its global's cell, when `f` names one of
    /// them, taking `n` arguments, whose body is not being inlined already.
    fn r_inlined(&self, env: &[(Sym, RLoc)], f: ExpId, n: usize) -> O<(usize, Value)> {
        let Exp::Var(name) = *self.c.arena.exp_at(f) else { return None };
        let Some(RLoc::Global(cell)) = self.r_where(env, name) else { return None };
        if self.inlining.contains(&name) {
            return None;
        }
        let k = self.inlines.iter().position(|i| i.name == name && i.params.len() == n)?;
        Some((k, cell))
    }

    /// A call of a small global procedure, inlined: the arguments made and
    /// kept (one that is a variable in the frame or the closure is used
    /// where it is); then, if the global still holds a closure of the word
    /// the body was compiled to, the body, in a scope of its own where the
    /// parameters are the arguments and the globals those it saw; else the
    /// call. A redefinition makes a new closure, of a new word: the call.
    #[allow(clippy::too_many_arguments)]
    fn r_inline(&mut self, g: &mut Gen, k: usize, cell: Value, f: ExpId, args: &[ExpId], env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        let (regs, slots) = (g.next_reg, g.next_slot);
        let (name, word, body, genv_len) = (self.inlines[k].name, self.inlines[k].word, self.inlines[k].body, self.inlines[k].genv_len);
        let params = self.inlines[k].params.clone();
        let (mut own_env, mut own_te, mut slow) = (Vec::new(), Vec::new(), Vec::new());
        for (p, a) in params.iter().zip(args) {
            if let Some(v) = self.r_const(env, *a) {
                own_env.push((*p, RLoc::Const(v)));
                slow.push(Arg::V(v));
                own_te.push((*p, Loc::Slot(usize::MAX)));
                continue;
            }
            // A variable used where it is: in a register too, in a fast
            // version, where no call comes after to clobber it.
            let fast = self.assume.is_some();
            match self.r_var(env, *a) {
                Some(l @ (RLoc::Slot(_) | RLoc::Free(_))) => {
                    own_env.push((*p, l));
                    slow.push(Arg::E(*a));
                }
                Some(l @ RLoc::Reg(_)) if fast => {
                    own_env.push((*p, l));
                    slow.push(Arg::E(*a));
                }
                _ => {
                    self.r_exp(g, *a, env, te, false)?;
                    let l = Self::r_keep(g, g.leaf)?;
                    own_env.push((*p, l));
                    slow.push(match l {
                        RLoc::Slot(s) => Arg::Slot(s),
                        _ => Arg::E(*a),
                    });
                }
            }
            own_te.push((*p, Loc::Slot(usize::MAX)));
        }
        let (call, end) = (g.label(), g.label());
        let assumed = self.r_assume(cell, word);
        if !assumed {
            self.r_guard(g, cell, word, call);
        }
        let outer = (g.this.take(), self.genv_limit.replace(genv_len));
        self.inlining.push(name);
        let inlined = self.r_exp(g, body, &mut own_env, &mut own_te, tail);
        self.inlining.pop();
        (g.this, self.genv_limit) = outer;
        inlined?;
        if assumed {
            g.next_reg = regs;
            g.next_slot = slots;
            return Some(());
        }
        if !tail {
            g.items.push(RItem::Branch(false, end));
        }
        g.items.push(RItem::Label(call));
        self.r_args(g, &slow, env, te, Some(f))?;
        if tail {
            g.leave();
            g.op("tailinvoke", &[Gen::n(args.len())]);
        } else {
            g.op("invoke", &[Gen::n(args.len())]);
        }
        g.items.push(RItem::Label(end));
        g.next_reg = regs;
        g.next_slot = slots;
        Some(())
    }

    /// Whether `letrec` binding `i` is a join point: a lambda whose body
    /// calls it only in tail position, as the `letrec`'s body does, and that
    /// no sibling mentions; so no closure of it need be made, and each call
    /// is a jump (the `letrec` being in tail position itself).
    pub(super) fn r_join_ok(&self, bindings: &[(Sym, crate::ast::TyId, ExpId)], body: ExpId, i: usize) -> bool {
        let (name, _, init) = bindings[i];
        let Some((ps, lbody, None)) = self.lambda_of(init) else { return false };
        !ps.contains(&name)
            && self.loops_only(lbody, name, ps.len(), true)
            && self.loops_only(body, name, ps.len(), true)
            && bindings.iter().enumerate().all(|(k, (_, _, j))| k == i || !self.mentions(*j, name))
    }

    /// Which of `specials`, its global's cell, and the lambda argument, when
    /// `f` names one of them and the argument at its parameter is a lambda
    /// small enough to inline, taking as many arguments as it is called
    /// with; not while a procedure is being specialized.
    fn r_specialized(&self, env: &[(Sym, RLoc)], f: ExpId, args: &[ExpId]) -> O<(usize, Value, ExpId)> {
        if self.spec.is_some() {
            return None;
        }
        let Exp::Var(name) = *self.c.arena.exp_at(f) else { return None };
        let Some(RLoc::Global(cell)) = self.r_where(env, name) else { return None };
        let k = self.specials.iter().position(|s| s.name == name && s.params.len() == args.len())?;
        let lam = args[self.specials[k].param];
        match self.c.arena.exp_at(lam) {
            Exp::Lambda { params, body } if params.len() == self.specials[k].arity && self.inline_room(*body, super::INLINE_LIMIT) >= 0 => {
                Some((k, cell, lam))
            }
            _ => None,
        }
    }

    /// A call of a global procedure with a lambda at a parameter it only
    /// calls: a copy of the procedure made for the lambda (`Spec`), whose
    /// closure is made first; then the arguments, the lambda's closure among
    /// them; then, if the global still holds a closure of the word the copy
    /// was made from, the copy called, else the global.
    #[allow(clippy::too_many_arguments)]
    fn r_specialize(&mut self, g: &mut Gen, k: usize, cell: Value, lam: ExpId, args: &[ExpId], env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        let (regs, slots) = (g.next_reg, g.next_slot);
        let Exp::Lambda { params, body } = self.c.arena.exp_at(lam).clone() else { return None };
        let lam_params: Vec<Sym> = params.iter().map(|(n, _)| *n).collect();
        let sp = &self.specials[k];
        let spec = super::Spec {
            name: sp.name,
            cell,
            word: sp.word,
            param: sp.param,
            param_name: sp.params[sp.param],
            n: sp.params.len(),
            arity: sp.arity,
            lam_fv: self.captured(&lam_params, body, te),
            lam_params,
            lam_body: body,
            lam_genv: self.genv_limit,
        };
        let (params, gbody, genv_len) = (sp.params.clone(), sp.body, sp.genv_len);
        // The copy compiled apart: what this body assumes is not its.
        let outer = (self.spec.replace(spec), self.genv_limit.replace(genv_len), self.declined.take(), self.assume.take());
        // Named for the procedure and the lambda.
        let span = self.c.arena.span_of(body);
        let at = match self.char_at.get(span.start as usize) {
            Some(at) if span.file.0 == 0 => at.to_string(),
            _ => format!("{}:{}", span.file.0, span.start),
        };
        self.word_name = Some(format!("{}@lambda@{at}", self.name(self.specials[k].name)));
        let made = self.lambda_word(&params, gbody, &Vec::new(), None);
        (self.spec, self.genv_limit, self.declined, self.assume) = outer;
        let (copy, _) = made.ok()?;
        let s = g.slot();
        g.op("lambda", &[copy, Gen::n(0)]);
        g.op("setstk", &[Gen::n(s)]);
        let es: Vec<Arg> = args.iter().map(|a| Arg::E(*a)).collect();
        self.r_args(g, &es, env, te, None)?;
        let (call, end) = (g.label(), g.label());
        let word = self.specials[k].word;
        if self.r_assume(cell, word) {
            g.op("stack", &[Gen::n(s)]);
            self.r_invoke(g, args.len(), tail);
            g.next_reg = regs;
            g.next_slot = slots;
            return Some(());
        }
        self.r_guard(g, cell, word, call);
        g.op("stack", &[Gen::n(s)]);
        self.r_invoke(g, args.len(), tail);
        if !tail {
            g.items.push(RItem::Branch(false, end));
        }
        g.items.push(RItem::Label(call));
        g.op("global", &[cell]);
        self.r_invoke(g, args.len(), tail);
        g.items.push(RItem::Label(end));
        g.next_reg = regs;
        g.next_slot = slots;
        Some(())
    }

    /// Whether the body being compiled is its fast version, which assumes
    /// what the guard would test (`register_code`): if so, the assumption
    /// noted, for its guard at the start.
    fn r_assume(&mut self, cell: Value, word: Value) -> bool {
        match &mut self.assume {
            Some(a) => {
                // Each global once.
                if !a.iter().any(|(c, _)| *c == cell) {
                    a.push((cell, word));
                }
                true
            }
            None => false,
        }
    }

    /// The guard of an inlined or specialized call: to `call` unless the
    /// global `cell` holds a closure of `word`.
    fn r_guard(&self, g: &mut Gen, cell: Value, word: Value, call: usize) {
        g.items.push(RItem::Guard(cell, word, call));
    }

    /// `n` arguments in registers, the procedure in RESULT: called, or in
    /// tail position, the frame left first.
    fn r_invoke(&self, g: &mut Gen, n: usize, tail: bool) {
        if tail {
            g.leave();
            g.op("tailinvoke", &[Gen::n(n)]);
        } else {
            g.op("invoke", &[Gen::n(n)]);
        }
    }

    /// In a procedure specialized at a lambda, a call of the parameter the
    /// lambda is: the lambda's body, its parameters bound to the arguments
    /// and the values its closure captured to those fields of the
    /// parameter's value, where the globals are those it saw.
    #[allow(clippy::too_many_arguments)]
    fn r_spec_lambda(&mut self, g: &mut Gen, sp: &super::Spec, at: RLoc, args: &[ExpId], env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        let (regs, slots) = (g.next_reg, g.next_slot);
        let (mut own_env, mut own_te) = (Vec::new(), Vec::new());
        let inits: Vec<Option<ExpId>> = args.iter().map(|a| Some(*a)).chain(sp.lam_fv.iter().map(|_| None)).collect();
        let inner: Env = sp.lam_params.iter().chain(&sp.lam_fv).map(|n| (*n, Loc::Slot(usize::MAX))).collect();
        // The body as it is compiled: in the globals the lambda saw.
        let outer = std::mem::replace(&mut self.genv_limit, sp.lam_genv);
        let body_collects = !g.leaf && self.r_collects(sp.lam_body, &inner, None, tail);
        self.genv_limit = outer;
        let in_regs = self.r_in_regs(g, &inits, te, body_collects);
        for ((p, a), reg) in sp.lam_params.iter().zip(args).zip(&in_regs) {
            if let Some(v) = self.r_const(env, *a) {
                own_env.push((*p, RLoc::Const(v)));
                own_te.push((*p, Loc::Slot(usize::MAX)));
                continue;
            }
            self.r_exp(g, *a, env, te, false)?;
            own_env.push((*p, Self::r_keep(g, *reg)?));
            own_te.push((*p, Loc::Slot(usize::MAX)));
        }
        for ((j, n), reg) in sp.lam_fv.iter().enumerate().zip(&in_regs[sp.lam_params.len()..]) {
            match at {
                RLoc::Reg(k) => g.op("reg", &[Gen::n(k)]),
                RLoc::Slot(s) => g.op("stack", &[Gen::n(s)]),
                _ => return None,
            }
            g.op("field", &[Value::fixnum((super::CLOSURE_FREE0 + j) as i64)]);
            own_env.push((*n, Self::r_keep(g, *reg)?));
            own_te.push((*n, Loc::Slot(usize::MAX)));
        }
        let outer = self.genv_limit;
        self.genv_limit = sp.lam_genv;
        let done = self.r_exp(g, sp.lam_body, &mut own_env, &mut own_te, tail);
        self.genv_limit = outer;
        done?;
        g.next_reg = regs;
        g.next_slot = slots;
        Some(())
    }

    /// For values bound in turn, made by `inits` (none: made without a
    /// call) in `te`, and then seen by a body that calls or calls out, or
    /// not (`body_collects`): whether each is kept in a register. In a leaf, each is. Else one is where nothing after it, a
    /// later value or the body, calls or calls out, which is all that
    /// clobbers registers or collects; so many, at most, as leave half the
    /// registers for the operations' temporaries.
    fn r_in_regs(&mut self, g: &Gen, inits: &[Option<ExpId>], te: &Env, body_collects: bool) -> Vec<bool> {
        if g.leaf {
            return vec![true; inits.len()];
        }
        let this = g.this.map(|(t, _)| t);
        let mut free = !body_collects;
        let mut out = vec![false; inits.len()];
        for i in (0..inits.len()).rev() {
            out[i] = free;
            if let Some(x) = inits[i] {
                free = free && !self.r_collects(x, te, this, false);
            }
        }
        let mut next = g.next_reg;
        for r in out.iter_mut().filter(|r| **r) {
            *r = next < REGS / 2;
            next += usize::from(*r);
        }
        out
    }

    /// RESULT kept where a `let` keeps a value: a register (`reg`), else a
    /// frame slot.
    fn r_keep(g: &mut Gen, reg: bool) -> O<RLoc> {
        Some(if reg {
            let r = g.reg()?;
            g.op("setreg", &[Gen::n(r)]);
            RLoc::Reg(r)
        } else {
            let s = g.slot();
            g.op("setstk", &[Gen::n(s)]);
            RLoc::Slot(s)
        })
    }

    /// A procedure calling itself through its global `cell` (a top-level
    /// definition's, or, in a copy specialized at a lambda, with the
    /// parameter passed as itself): the arguments made; then, if the global
    /// still holds a closure of `word` (its own, or the one the copy was
    /// made from), this procedure again, by its own entry, or in tail
    /// position a loop back to `start`; else the global.
    #[allow(clippy::too_many_arguments)]
    fn r_self_guarded(&mut self, g: &mut Gen, cell: Value, word: Value, start: usize, f: ExpId, args: &[ExpId], env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        // In a fast version, a call in tail position is a loop, in a leaf
        // too.
        if g.leaf && (!(tail && self.assume.is_some()) || args.len() > REGS) {
            return self.decline("more than REGS arguments in a leaf");
        }
        let (regs, slots) = (g.next_reg, g.next_slot);
        let (call, end) = (g.label(), g.label());
        if tail {
            // Each argument kept (in a register, in a leaf); then, the
            // procedure again, each into its parameter's place, and back to
            // the start.
            let mut made = Vec::new();
            for a in args {
                self.r_exp(g, *a, env, te, false)?;
                made.push(Self::r_keep(g, g.leaf)?);
            }
            let assumed = self.r_assume(cell, word);
            if !assumed {
                self.r_guard(g, cell, word, call);
            }
            for (i, m) in made.iter().enumerate() {
                match m {
                    RLoc::Reg(r) => g.op("movereg", &[Gen::n(*r), Gen::n(i + 1)]),
                    RLoc::Slot(s) => {
                        g.op("stack", &[Gen::n(*s)]);
                        g.op("setstk", &[Gen::n(i)]);
                    }
                    _ => return None,
                }
            }
            g.items.push(RItem::Branch(false, start));
            if assumed {
                g.looped = true;
                g.next_reg = regs;
                g.next_slot = slots;
                return Some(());
            }
            g.items.push(RItem::Label(call));
            let es: Vec<Arg> = made
                .iter()
                .map(|m| match m {
                    RLoc::Slot(s) => Some(Arg::Slot(*s)),
                    _ => None,
                })
                .collect::<O<_>>()?;
            self.r_args(g, &es, env, te, Some(f))?;
            self.r_invoke(g, args.len(), true);
        } else {
            let es: Vec<Arg> = args.iter().map(|a| Arg::E(*a)).collect();
            self.r_args(g, &es, env, te, None)?;
            if self.r_assume(cell, word) {
                g.op("invokeself", &[Gen::n(args.len())]);
                g.next_reg = regs;
                g.next_slot = slots;
                return Some(());
            }
            self.r_guard(g, cell, word, call);
            g.op("invokeself", &[Gen::n(args.len())]);
            g.items.push(RItem::Branch(false, end));
            g.items.push(RItem::Label(call));
            g.op("global", &[cell]);
            g.op("invoke", &[Gen::n(args.len())]);
            g.items.push(RItem::Label(end));
        }
        g.next_reg = regs;
        g.next_slot = slots;
        Some(())
    }

    /// `RESULT := r(a, b)`, `a` evaluated first. A constant `b` is an
    /// immediate. When `a` is simple, `b` is made first, into a register,
    /// since `a` has no effect to come before it; otherwise `a` is made
    /// first and kept, in a register or, if making `b` may collect, in the
    /// frame.
    fn r_binary(&mut self, g: &mut Gen, r: &str, a: ExpId, b: ExpId, env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        let r = Value::fixnum(routine(r) as i64);
        match self.r_operands(g, a, b, env, te, true)? {
            (Some(v), _) => g.op("op2imm", &[r, v]),
            (None, Some(k)) => g.op("op2", &[r, Gen::n(k)]),
            (None, None) => return None,
        }
        Some(())
    }

    /// Code that goes to `label` if `x` is `when` (true: anything but #f),
    /// and on if not: a test as jumps. `and` and `or` (`if`s, as the parser
    /// makes them), `not` and constants make no boolean, and are tested
    /// no more than once.
    fn r_branch_on(&mut self, g: &mut Gen, x: ExpId, when: bool, label: usize, env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        let truth = |v: Value| v != Value::FALSE;
        match self.c.arena.exp_at(x).clone() {
            Exp::The { exp, .. } => return self.r_branch_on(g, exp, when, label, env, te),
            Exp::App { fun, args } if args.len() == 1 && self.r_standard_name(env, fun).as_deref() == Some("not") => {
                return self.r_branch_on(g, args[0], !when, label, env, te);
            }
            Exp::If { test, then, els } => {
                let (tc, ec) = (self.r_const(env, then), self.r_const(env, els));
                match (tc, ec) {
                    // `(if a K e)`: where `a` holds, `K` decides.
                    (Some(t), _) if truth(t) == when => {
                        self.r_branch_on(g, test, true, label, env, te)?;
                        self.r_branch_on(g, els, when, label, env, te)?;
                    }
                    (Some(_), _) => {
                        let skip = g.label();
                        self.r_branch_on(g, test, true, skip, env, te)?;
                        self.r_branch_on(g, els, when, label, env, te)?;
                        g.items.push(RItem::Label(skip));
                    }
                    // `(if a t K)`: `and`'s shape.
                    (None, Some(e)) if truth(e) == when => {
                        self.r_branch_on(g, test, false, label, env, te)?;
                        self.r_branch_on(g, then, when, label, env, te)?;
                    }
                    (None, Some(_)) => {
                        let skip = g.label();
                        self.r_branch_on(g, test, false, skip, env, te)?;
                        self.r_branch_on(g, then, when, label, env, te)?;
                        g.items.push(RItem::Label(skip));
                    }
                    (None, None) => {
                        let (no, end) = (g.label(), g.label());
                        self.r_branch_on(g, test, false, no, env, te)?;
                        self.r_branch_on(g, then, when, label, env, te)?;
                        g.items.push(RItem::Branch(false, end));
                        g.items.push(RItem::Label(no));
                        self.r_branch_on(g, els, when, label, env, te)?;
                        g.items.push(RItem::Label(end));
                    }
                }
                return Some(());
            }
            _ => {}
        }
        if let Some(v) = self.r_const(env, x) {
            if truth(v) == when {
                g.items.push(RItem::Branch(false, label));
            }
            return Some(());
        }
        self.r_exp(g, x, env, te, false)?;
        g.items.push(if when { RItem::BranchT(label) } else { RItem::Branch(true, label) });
        Some(())
    }

    /// `x` as `core + k`: `core` the one operand of a chain of `+`, and of
    /// `-` of constants, that is not a constant (none if all are), and `k`
    /// the constants' sum, under 2^30 in size; else `x` itself and 0.
    fn r_split(&mut self, env: &[(Sym, RLoc)], x: ExpId) -> (O<ExpId>, i64) {
        const SMALL: i64 = 1 << 30;
        if let Some(v) = self.r_const(env, x)
            && v.is_fixnum()
            && v.as_fixnum().abs() < SMALL
        {
            return (None, v.as_fixnum());
        }
        let split = match self.c.arena.exp_at(x).clone() {
            Exp::App { fun, args } => match self.r_standard_name(env, fun) {
                Some(name) => self.r_split_app(env, &name, &args),
                None => None,
            },
            _ => None,
        };
        split.unwrap_or((Some(x), 0))
    }

    /// The same for standard operation `name` applied to `args`, if it is
    /// such a chain.
    fn r_split_app(&mut self, env: &[(Sym, RLoc)], name: &str, args: &[ExpId]) -> O<(O<ExpId>, i64)> {
        if args.len() != 2 || !matches!(name, "+" | "-") {
            return None;
        }
        let (pa, ka) = self.r_split(env, args[0]);
        let (pb, kb) = self.r_split(env, args[1]);
        let (core, k) = match (name, pa, pb) {
            ("+", Some(_), Some(_)) => return None,
            ("+", p, q) => (p.or(q), ka + kb),
            ("-", p, None) => (p, ka - kb),
            _ => return None,
        };
        (k.abs() < 1 << 30).then_some((core, k))
    }

    /// RESULT := r(y, x), `x` evaluated first, as written: for an operation
    /// whose operands trade places, where they may not run in the other
    /// order. `x` is kept in a register, or the frame if `y` calls.
    fn r_binary_swapped(&mut self, g: &mut Gen, r: &str, x: ExpId, y: ExpId, env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        let r = Value::fixnum(routine(r) as i64);
        let (regs, slots) = (g.next_reg, g.next_slot);
        self.r_exp(g, x, env, te, false)?;
        let collects = !g.leaf && self.r_collects(y, te, g.this.map(|(t, _)| t), false);
        let k = g.reg()?;
        if collects {
            let s = g.slot();
            g.op("setstk", &[Gen::n(s)]);
            self.r_exp(g, y, env, te, false)?;
            g.op("load", &[Gen::n(k), Gen::n(s)]);
        } else {
            g.op("setreg", &[Gen::n(k)]);
            self.r_exp(g, y, env, te, false)?;
        }
        g.op("op2", &[r, Gen::n(k)]);
        g.next_reg = regs;
        g.next_slot = slots;
        Some(())
    }

    /// `a` into RESULT and `b` into a register, `a` evaluated first; or, if
    /// `imm` and `b` is a constant, `b` as an immediate. The register is
    /// free again after: use it at once.
    fn r_operands(&mut self, g: &mut Gen, a: ExpId, b: ExpId, env: &mut Vec<(Sym, RLoc)>, te: &mut Env, imm: bool) -> O<(O<Value>, O<usize>)> {
        let (regs, slots) = (g.next_reg, g.next_slot);
        let out;
        if let (true, Some(v)) = (imm, self.r_const(env, b)) {
            self.r_exp(g, a, env, te, false)?;
            out = (Some(v), None);
        } else if let Some(RLoc::Reg(k)) = self.r_var(env, b) {
            // `b` is in a register already.
            self.r_exp(g, a, env, te, false)?;
            out = (None, Some(k));
        } else if self.r_simple(a) {
            // `b` first (`a` has no effect, and sees none), made before its
            // register is taken: a chain of operations nested in their
            // second operands then needs one register, not one a level.
            let k = if self.r_simple(b) {
                let k = g.reg()?;
                self.r_into(g, b, k, env, te)?;
                k
            } else {
                self.r_exp(g, b, env, te, false)?;
                let k = g.reg()?;
                g.op("setreg", &[Gen::n(k)]);
                k
            };
            self.r_exp(g, a, env, te, false)?;
            out = (None, Some(k));
        } else {
            self.r_exp(g, a, env, te, false)?;
            let collects = !g.leaf && self.r_collects(b, te, g.this.map(|(t, _)| t), false);
            let kept = if collects {
                let s = g.slot();
                g.op("setstk", &[Gen::n(s)]);
                RLoc::Slot(s)
            } else {
                let t = g.reg()?;
                g.op("setreg", &[Gen::n(t)]);
                RLoc::Reg(t)
            };
            let k = g.reg()?;
            self.r_into(g, b, k, env, te)?;
            match kept {
                RLoc::Slot(s) => g.op("stack", &[Gen::n(s)]),
                RLoc::Reg(t) => g.op("reg", &[Gen::n(t)]),
                _ => unreachable!(),
            }
            out = (None, Some(k));
        }
        g.next_reg = regs;
        g.next_slot = slots;
        Some(out)
    }

    /// Where `x` is, if it is a variable.
    fn r_var(&self, env: &[(Sym, RLoc)], x: ExpId) -> O<RLoc> {
        match self.c.arena.exp_at(x) {
            Exp::Var(n) if !self.c.facts.changed(x) => self.r_where(env, *n),
            _ => None,
        }
    }

    /// `x`'s value into REGk: straight from a register or the frame when it
    /// is a variable there, else by way of RESULT.
    fn r_into(&mut self, g: &mut Gen, x: ExpId, k: usize, env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        match self.r_var(env, x) {
            Some(RLoc::Slot(s)) => g.op("load", &[Gen::n(k), Gen::n(s)]),
            Some(RLoc::Reg(r)) if r == k => {}
            Some(RLoc::Reg(r)) => g.op("movereg", &[Gen::n(r), Gen::n(k)]),
            _ => {
                self.r_exp(g, x, env, te, false)?;
                g.op("setreg", &[Gen::n(k)]);
            }
        }
        Some(())
    }

    /// `x`'s value, if it is a constant that needs no allocation when it
    /// runs: a literal, a name bound to one, `nil`, a standard operation on
    /// constants folded (`+` and `-` on integers under 2^30 in size, which
    /// cannot overflow; comparisons; `not`; `null?`; `char=?`; `int->u32`
    /// and its kin of an integer that fits), or a sum or product of
    /// constants, made now, once. (Frozen, and FX-26 has no
    /// `eq?`, so no run can tell it from one it made itself.)
    fn r_const(&mut self, env: &[(Sym, RLoc)], x: ExpId) -> O<Value> {
        match self.c.arena.exp_at(x).clone() {
            Exp::Int(k) => Some(Value::fixnum(k)),
            Exp::Bool(b) => Some(Value::boolean(b)),
            Exp::Char(c) => Some(Value::char(c)),
            Exp::Var(n) => match self.r_where(env, n) {
                Some(RLoc::Const(v)) => Some(v),
                None if matches!(self.name(n), "nil" | "no-pair") => Some(Value::NULL),
                _ => None,
            },
            Exp::The { exp: body, .. } | Exp::PLambda { body, .. } | Exp::Proj { body, .. } => self.r_const(env, body),
            Exp::Sum(t, v) => {
                let v = self.r_const(env, v)?;
                let tag = self.heap.intern(self.c.interner.name(t));
                Some(self.heap.make_frozen(kind("sum"), &[tag, v]))
            }
            Exp::Product(fields) => {
                let vs: Vec<Value> = fields.iter().map(|(_, f)| self.r_const(env, *f)).collect::<O<_>>()?;
                Some(self.heap.make_frozen(kind("product"), &vs))
            }
            Exp::App { fun, args } => {
                let name = self.r_standard_name(env, fun)?;
                let vs: Vec<Value> = args.iter().map(|a| self.r_const(env, *a)).collect::<O<_>>()?;
                let small = |v: &Value| v.is_fixnum() && v.as_fixnum().abs() < 1 << 30;
                let int2 = || (vs.len() == 2 && vs.iter().all(small)).then(|| (vs[0].as_fixnum(), vs[1].as_fixnum()));
                match name.as_str() {
                    "+" => int2().map(|(a, b)| Value::fixnum(a + b)),
                    "-" => int2().map(|(a, b)| Value::fixnum(a - b)),
                    "<" => int2().map(|(a, b)| Value::boolean(a < b)),
                    ">" => int2().map(|(a, b)| Value::boolean(a > b)),
                    "<=" => int2().map(|(a, b)| Value::boolean(a <= b)),
                    ">=" => int2().map(|(a, b)| Value::boolean(a >= b)),
                    "=" => int2().map(|(a, b)| Value::boolean(a == b)),
                    "not" if vs.len() == 1 => Some(Value::boolean(vs[0] == Value::FALSE)),
                    "null?" if vs.len() == 1 => Some(Value::boolean(vs[0] == Value::NULL)),
                    "char=?" if vs.len() == 2 && vs.iter().all(|v| v.is_char()) => Some(Value::boolean(vs[0] == vs[1])),
                    // A fixed-width integer is the fixnum of its value: an
                    // integer that fits the type is its own conversion.
                    "int->i32" | "int->u32" | "int->i64" | "int->u64" if vs.len() == 1 && vs[0].is_fixnum() => {
                        let n = vs[0].as_fixnum();
                        let fits = match name.as_str() {
                            "int->i32" => i32::try_from(n).is_ok(),
                            "int->u32" => u32::try_from(n).is_ok(),
                            "int->i64" => true,
                            _ => n >= 0,
                        };
                        fits.then_some(vs[0])
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The arguments into REG1…REGn, in order, and then `f`, if a call's,
    /// into RESULT. Not in a leaf: an argument that is not simple is kept in
    /// the frame until all are made; a simple one is made last. Past `REGS`
    /// (Larceny's convention), REG1…REG7 hold the first seven and REG8 a
    /// list of the rest, made after every argument, by `cons`, which may
    /// collect: so then an argument in a register is kept first, like one
    /// that is not simple.
    fn r_args(&mut self, g: &mut Gen, args: &[Arg], env: &mut Vec<(Sym, RLoc)>, te: &mut Env, f: Option<ExpId>) -> O<()> {
        if g.leaf {
            return self.decline("a call-out in a leaf");
        }
        let many = args.len() > REGS;
        let slots = g.next_slot;
        let mut kept = self.r_keep_args(g, args, env, te, many, f)?;
        let fun = match f {
            Some(f) if !self.r_simple(f) => {
                self.r_exp(g, f, env, te, false)?;
                let s = g.slot();
                g.op("setstk", &[Gen::n(s)]);
                Some(s)
            }
            _ => None,
        };
        // The list of those past the seventh, last first, kept.
        let in_regs = if many {
            self.r_cons_list(g, args, &kept, REGS - 1, env, te)?;
            let s = g.slot();
            g.op("setstk", &[Gen::n(s)]);
            kept.truncate(REGS - 1);
            kept.push(Some(s));
            REGS
        } else {
            args.len()
        };
        for (i, k) in kept.iter().enumerate().take(in_regs) {
            match (i, k) {
                (i, Some(s)) if i + 1 == REGS && many => g.op("load", &[Gen::n(REGS), Gen::n(*s)]),
                _ => self.r_arg_into(g, &args[i], *k, i + 1, env, te)?,
            }
        }
        match (f, fun) {
            (_, Some(s)) => g.op("stack", &[Gen::n(s)]),
            (Some(f), None) => self.r_exp(g, f, env, te, false)?,
            (None, None) => {}
        }
        g.next_slot = slots;
        Some(())
    }

    /// Each argument that is not simple made, in order, and kept: in a frame
    /// slot, or (`usize::MAX`) straight in its register, the last such when
    /// the procedure `f` is simple too. With `many`, a `cons` follows, so an
    /// argument in a register is kept too, and none goes straight to its.
    #[allow(clippy::too_many_arguments)]
    fn r_keep_args(
        &mut self,
        g: &mut Gen,
        args: &[Arg],
        env: &mut Vec<(Sym, RLoc)>,
        te: &mut Env,
        many: bool,
        f: Option<ExpId>,
    ) -> O<Vec<Option<usize>>> {
        let mut kept = Vec::new();
        let simple: Vec<bool> = args
            .iter()
            .map(|a| match a {
                Arg::E(x) => self.r_simple(*x) && !(many && matches!(self.r_var(env, *x), Some(RLoc::Reg(_)))),
                Arg::Name(n) => !(many && matches!(self.r_where(env, *n), Some(RLoc::Reg(_)))),
                Arg::V(_) | Arg::Slot(_) | Arg::Lexical(_) => true,
                Arg::Thunk(_) | Arg::AsIs(_) => false,
            })
            .collect();
        // The last argument that is not simple goes straight to its
        // register, when the procedure is simple too: all that follows it
        // is simple, and touches only RESULT and its own register.
        let direct = match f {
            _ if many => None,
            Some(f) if !self.r_simple(f) => None,
            _ => simple.iter().rposition(|s| !s),
        };
        for (i, a) in args.iter().enumerate() {
            if simple[i] {
                kept.push(None);
                continue;
            }
            match a {
                Arg::E(x) => self.r_exp(g, *x, env, te, false)?,
                Arg::AsIs(x) => self.r_exp_as_is(g, *x, env, te, false)?,
                Arg::Thunk(body) => {
                    self.r_lambda(g, &[], *body, env, te, None, None, false)?;
                }
                Arg::Name(n) => self.r_name(g, *n, env)?,
                Arg::V(_) | Arg::Slot(_) | Arg::Lexical(_) => unreachable!(),
            }
            if Some(i) == direct {
                g.op("setreg", &[Gen::n(i + 1)]);
                kept.push(Some(usize::MAX));
            } else {
                let s = g.slot();
                g.op("setstk", &[Gen::n(s)]);
                kept.push(Some(s));
            }
        }
        Some(kept)
    }

    /// Into RESULT, a list of the arguments from the `from`th, as kept
    /// (`r_keep_args`): the pairs made from the last, onto `nil`.
    fn r_cons_list(&mut self, g: &mut Gen, args: &[Arg], kept: &[Option<usize>], from: usize, env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        g.op("const", &[Value::NULL]);
        for i in (from..args.len()).rev() {
            g.op("setreg", &[Gen::n(2)]);
            self.r_arg_into(g, &args[i], kept[i], 1, env, te)?;
            g.op("cellular", &[Value::fixnum(routine("cons") as i64), Gen::n(2)]);
        }
        Some(())
    }

    /// Argument `a` into REGk: from the frame slot it was kept in, if it
    /// was (`usize::MAX`: in its register already), else made there.
    fn r_arg_into(&mut self, g: &mut Gen, a: &Arg, kept: Option<usize>, k: usize, env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        match (kept, a) {
            (Some(usize::MAX), _) => {}
            (Some(s), _) => g.op("load", &[Gen::n(k), Gen::n(s)]),
            (None, Arg::E(x)) => self.r_into(g, *x, k, env, te)?,
            (None, Arg::V(v)) => {
                g.op("const", &[*v]);
                g.op("setreg", &[Gen::n(k)]);
            }
            (None, Arg::Slot(s)) => g.op("load", &[Gen::n(k), Gen::n(*s)]),
            (None, Arg::Name(n)) => match self.r_where(env, *n)? {
                RLoc::Slot(s) => g.op("load", &[Gen::n(k), Gen::n(s)]),
                RLoc::Reg(r) if r == k => {}
                RLoc::Reg(r) => g.op("movereg", &[Gen::n(r), Gen::n(k)]),
                _ => {
                    self.r_name(g, *n, env)?;
                    g.op("setreg", &[Gen::n(k)]);
                }
            },
            (None, Arg::Lexical(i)) => {
                g.op("lexical", &[Gen::n(*i)]);
                g.op("setreg", &[Gen::n(k)]);
            }
            (None, Arg::Thunk(_) | Arg::AsIs(_)) => unreachable!(),
        }
        Some(())
    }

    /// A lifted procedure's added name's value into RESULT: a value in a
    /// place, not a register.
    fn r_name(&mut self, g: &mut Gen, n: Sym, env: &[(Sym, RLoc)]) -> O<()> {
        match self.r_where(env, n)? {
            RLoc::Slot(s) => g.op("stack", &[Gen::n(s)]),
            RLoc::Reg(r) => g.op("reg", &[Gen::n(r)]),
            RLoc::Free(k) => g.op("lexical", &[Gen::n(k)]),
            RLoc::Const(v) => g.op("const", &[v]),
            _ => return self.decline("a lifted procedure's added name, not a value in a place"),
        }
        Some(())
    }

    /// A call-out, `prim p n` or `cellular r n`, on `args` in REG1…REGn.
    fn r_call_out(&mut self, g: &mut Gen, how: &str, what: i64, args: &[Arg], env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        self.r_args(g, args, env, te, None)?;
        g.op(how, &[Value::fixnum(what), Gen::n(args.len())]);
        Some(())
    }

    fn r_prim(&mut self, g: &mut Gen, name: &str, args: &[Arg], env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        let p = fixpt_engine::cellular::runtime_primitive(name)? as i64;
        self.r_call_out(g, "prim", p, args, env, te)
    }

    /// A closure of a lambda into RESULT, its free values into REG1…REGn
    /// first; `own` as for `lambda_word`. With a `region` (an `rlambda`'s),
    /// the closure is made there, by `%region-closure h fv … w`. What it
    /// gives: for each sibling not made yet (a `letrec`'s), the free value's
    /// index and the sibling's frame slot.
    #[allow(clippy::too_many_arguments)]
    fn r_lambda(
        &mut self,
        g: &mut Gen,
        ps: &[Sym],
        body: ExpId,
        env: &mut Vec<(Sym, RLoc)>,
        te: &mut Env,
        own: Option<Sym>,
        region: Option<ExpId>,
        tail: bool,
    ) -> O<Vec<(usize, usize)>> {
        // A leaf makes a closure only as its value, in tail position: its
        // call-out, where the free space has no room, may collect, and then
        // nothing but the closure is used after.
        if g.leaf && !(tail && region.is_none()) {
            return None;
        }
        let (w, fv) = match self.made_word(ps, body, te, own) {
            Some(made) => made,
            None => self.lambda_word(ps, body, te, own).ok()?,
        };
        // In a region, or past `REGS` (the rest a list, as a call's
        // arguments are, `r_args`): the free values as a call-out's operands.
        if region.is_some() || fv.len() > REGS {
            let mut args: Vec<Arg> = region.iter().map(|r| Arg::E(*r)).collect();
            let mut patches = Vec::new();
            for (j, n) in fv.iter().enumerate() {
                args.push(match self.r_where(env, *n)? {
                    RLoc::Slot(s) => Arg::Slot(s),
                    RLoc::Free(i) => Arg::Lexical(i),
                    RLoc::Pending(s) => {
                        patches.push((j, s));
                        Arg::V(Value::FALSE)
                    }
                    RLoc::Const(v) => Arg::V(v),
                    _ => return self.decline("a free value in a register"),
                });
            }
            if region.is_some() {
                args.push(Arg::V(w));
                self.r_prim(g, "%region-closure", &args, env, te)?;
            } else {
                self.r_args(g, &args, env, te, None)?;
                g.op("lambda", &[w, Gen::n(fv.len())]);
            }
            return Some(patches);
        }
        // Those in registers first, none overwritten before it is read
        // (`r_par_moves`); then the rest, in order.
        let mut moves = Vec::new();
        for (j, n) in fv.iter().enumerate() {
            if let RLoc::Reg(r) = self.r_where(env, *n)?
                && r != j + 1
            {
                moves.push((r, j + 1));
            }
        }
        Self::r_par_moves(g, moves);
        let mut patches = Vec::new();
        for (j, n) in fv.iter().enumerate() {
            match self.r_where(env, *n)? {
                RLoc::Reg(_) => {}
                RLoc::Slot(s) => g.op("load", &[Gen::n(j + 1), Gen::n(s)]),
                RLoc::Free(i) => {
                    g.op("lexical", &[Gen::n(i)]);
                    g.op("setreg", &[Gen::n(j + 1)]);
                }
                RLoc::Pending(s) => {
                    g.op("const", &[Value::FALSE]);
                    g.op("setreg", &[Gen::n(j + 1)]);
                    patches.push((j, s));
                }
                RLoc::Const(v) => {
                    g.op("const", &[v]);
                    g.op("setreg", &[Gen::n(j + 1)]);
                }
                _ => return None,
            }
        }
        g.op("lambda", &[w, Gen::n(fv.len())]);
        Some(patches)
    }

    /// A call in tail position in a leaf, which has no frame: the arguments
    /// that are not in registers and not simple made first, in order, each
    /// into a register of its own, above REG1…REGn; then all moved to REG1…REGn at once
    /// (`r_par_moves`); then the simple ones, which read no register, into
    /// theirs; the procedure in RESULT; and the call. The procedure goes to
    /// RESULT before the moves where nothing after them uses RESULT.
    fn r_leaf_tail_call(&mut self, g: &mut Gen, f: ExpId, args: &[ExpId], env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        // Registers of its own above the arguments' as well as the leaf's.
        let regs = g.next_reg;
        g.next_reg = regs.max(args.len());
        let (mut moves, mut late) = (Vec::new(), Vec::new());
        for (i, a) in args.iter().enumerate() {
            match self.r_var(env, *a) {
                Some(RLoc::Reg(r)) => {
                    if r != i + 1 {
                        moves.push((r, i + 1));
                    }
                }
                _ if self.r_simple(*a) => late.push((i + 1, *a)),
                _ => {
                    self.r_exp(g, *a, env, te, false)?;
                    let Some(t) = g.reg() else { return self.decline("a leaf's tail call, out of registers") };
                    g.op("setreg", &[Gen::n(t)]);
                    moves.push((t, i + 1));
                }
            }
        }
        let written = |k: usize, moves: &[(usize, usize)], late: &[(usize, ExpId)]| moves.iter().any(|m| m.1 == k) || late.iter().any(|l| l.0 == k);
        // Whether RESULT is free while the moves are made and after.
        let quiet = late.is_empty() && !Self::r_moves_cycle(&moves);
        // Where the procedure is once the moves are made: in RESULT already,
        // a register, or (`None`) to be fetched, reading no register.
        let fun: Option<Option<usize>> = match self.r_var(env, f) {
            Some(RLoc::Reg(r)) if !written(r, &moves, &late) => Some(Some(r)),
            Some(RLoc::Reg(r)) if quiet => {
                g.op("reg", &[Gen::n(r)]);
                Some(None)
            }
            Some(RLoc::Reg(r)) => {
                let Some(t) = g.reg() else { return self.decline("a leaf's tail call, out of registers") };
                moves.push((r, t));
                Some(Some(t))
            }
            _ if self.r_simple(f) => None,
            _ => {
                self.r_exp(g, f, env, te, false)?;
                if quiet {
                    Some(None)
                } else {
                    let Some(t) = g.reg() else { return self.decline("a leaf's tail call, out of registers") };
                    g.op("setreg", &[Gen::n(t)]);
                    Some(Some(t))
                }
            }
        };
        Self::r_par_moves(g, moves);
        for (k, a) in late {
            self.r_into(g, a, k, env, te)?;
        }
        match fun {
            Some(Some(r)) => g.op("reg", &[Gen::n(r)]),
            Some(None) => {}
            None => self.r_exp(g, f, env, te, false)?,
        }
        g.op("tailinvoke", &[Gen::n(args.len())]);
        g.next_reg = regs;
        Some(())
    }

    /// Whether register moves (source, destination) form a cycle: some left
    /// when every move whose destination no other reads is taken away.
    fn r_moves_cycle(ms: &[(usize, usize)]) -> bool {
        let mut ms = ms.to_vec();
        while let Some(k) = (0..ms.len()).find(|&k| !ms.iter().enumerate().any(|(m, (s, _))| m != k && *s == ms[k].1)) {
            ms.remove(k);
        }
        !ms.is_empty()
    }

    /// Register moves (source, destination; source 0 is RESULT), made so
    /// that none overwrites what another has yet to read: the first whose
    /// destination no other reads, in order; else, the rest a cycle, the
    /// first's destination kept in RESULT, and read from there.
    fn r_par_moves(g: &mut Gen, mut ms: Vec<(usize, usize)>) {
        while !ms.is_empty() {
            let free = (0..ms.len()).find(|&k| !ms.iter().enumerate().any(|(m, (s, _))| m != k && *s == ms[k].1));
            match free {
                Some(k) => {
                    let (s, d) = ms.remove(k);
                    if s == 0 {
                        g.op("setreg", &[Gen::n(d)]);
                    } else {
                        g.op("movereg", &[Gen::n(s), Gen::n(d)]);
                    }
                }
                None => {
                    let d = ms[0].1;
                    g.op("reg", &[Gen::n(d)]);
                    for m in ms.iter_mut().filter(|m| m.0 == d) {
                        m.0 = 0;
                    }
                }
            }
        }
    }

    /// Arrays, and the tag and key makers: as the stack compiler does them.
    fn r_special(&mut self, g: &mut Gen, what: &str, args: &[ExpId], env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        let two = Value::fixnum(2);
        let add = Value::fixnum(routine("int-add") as i64);
        let es: Vec<Arg> = args.iter().map(|a| Arg::E(*a)).collect();
        match what {
            // Field i + 2, by index: checked, since i is any int.
            "array-ref" => {
                self.r_args(g, &es, env, te, None)?;
                g.op("reg", &[Gen::n(2)]);
                g.op("op2imm", &[add, two]);
                g.op("setreg", &[Gen::n(2)]);
                g.op("cellular", &[Value::fixnum(routine("field@") as i64), Gen::n(2)]);
            }
            "array-set!" => {
                let p = fixpt_engine::cellular::runtime_primitive("%bloblet-set!")? as i64;
                self.r_args(g, &es, env, te, None)?;
                g.op("reg", &[Gen::n(2)]);
                g.op("op2imm", &[add, two]);
                g.op("setreg", &[Gen::n(2)]);
                g.op("prim", &[Value::fixnum(p), Gen::n(3)]);
                let u = self.unit();
                g.op("const", &[u]);
            }
            "array-length" => {
                self.r_prim(g, "%bloblet-fields", &es, env, te)?;
                g.op("op2imm", &[Value::fixnum(routine("int-sub") as i64), Value::fixnum(1)]);
            }
            "make-array" => self.r_prim(g, "%make-bloblet-filled", &[Arg::V(Value::fixnum(0)), es[0], es[1]], env, te)?,
            "make-box" => {
                let u = self.unit();
                self.r_prim(g, "%make-box", &[Arg::V(u)], env, te)?;
            }
            // The runtime's, which refuses a pair not to be written; then
            // unit.
            "set-car!" | "set-cdr!" => {
                self.r_prim(g, what, &es, env, te)?;
                let u = self.unit();
                g.op("const", &[u]);
            }
            _ => return None,
        }
        Some(())
    }

    /// `tagcase`: the scrutinee kept; each arm's tag compared, the last's
    /// not when there is no `else` (a checked program covers every tag);
    /// the value, or its product's members, bound.
    #[allow(clippy::too_many_arguments)]
    fn r_tagcase(
        &mut self,
        g: &mut Gen,
        scrutinee: ExpId,
        arms: &[crate::ast::Arm],
        els: Option<(Sym, ExpId)>,
        env: &mut Vec<(Sym, RLoc)>,
        te: &mut Env,
        tail: bool,
    ) -> O<()> {
        let (depth, tdepth, regs, slots) = (env.len(), te.len(), g.next_reg, g.next_slot);
        self.r_exp(g, scrutinee, env, te, false)?;
        let place = |g: &mut Gen| -> O<RLoc> {
            Some(if g.leaf {
                let r = g.reg()?;
                g.op("setreg", &[Gen::n(r)]);
                RLoc::Reg(r)
            } else {
                let s = g.slot();
                g.op("setstk", &[Gen::n(s)]);
                RLoc::Slot(s)
            })
        };
        let sc = place(g)?;
        let get = |g: &mut Gen, l: RLoc| match l {
            RLoc::Reg(r) => g.op("reg", &[Gen::n(r)]),
            RLoc::Slot(s) => g.op("stack", &[Gen::n(s)]),
            _ => unreachable!(),
        };
        let end = g.label();
        let eq = Value::fixnum(routine("eq") as i64);
        for (i, arm) in arms.iter().enumerate() {
            let last = i + 1 == arms.len() && els.is_none();
            let next = g.label();
            if !last {
                get(g, sc);
                g.op("field", &[two()]);
                let tag = self.heap.intern(self.c.interner.name(arm.tag));
                g.op("op2imm", &[eq, tag]);
                g.items.push(RItem::Branch(true, next));
            }
            let (d, td, r, s) = (env.len(), te.len(), g.next_reg, g.next_slot);
            match &arm.bind {
                crate::ast::ArmBind::Value(x) => {
                    get(g, sc);
                    g.op("field", &[Value::fixnum(3)]);
                    let l = place(g)?;
                    env.push((*x, l));
                    te.push((*x, Loc::Slot(usize::MAX)));
                }
                crate::ast::ArmBind::Fields(xs) => {
                    for (j, x) in xs.iter().enumerate() {
                        get(g, sc);
                        g.op("field", &[Value::fixnum(3)]);
                        g.op("field", &[Value::fixnum(j as i64 + 2)]);
                        let l = place(g)?;
                        env.push((*x, l));
                        te.push((*x, Loc::Slot(usize::MAX)));
                    }
                }
            }
            self.r_exp(g, arm.body, env, te, tail)?;
            env.truncate(d);
            te.truncate(td);
            g.next_reg = r;
            g.next_slot = s;
            if !tail {
                g.items.push(RItem::Branch(false, end));
            }
            g.items.push(RItem::Label(next));
        }
        if let Some((y, body)) = els {
            env.push((y, sc));
            te.push((y, Loc::Slot(usize::MAX)));
            self.r_exp(g, body, env, te, tail)?;
        }
        g.items.push(RItem::Label(end));
        env.truncate(depth);
        te.truncate(tdepth);
        g.next_reg = regs;
        g.next_slot = slots;
        Some(())
    }

    /// A tail call of the procedure itself: the new arguments made, then
    /// put where the parameters are, and back to the start.
    fn r_loop(&mut self, g: &mut Gen, args: &[ExpId], env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        let (t, start) = g.this?;
        let (regs, slots) = (g.next_reg, g.next_slot);
        let mut made = Vec::new();
        for a in args {
            self.r_exp(g, *a, env, te, false)?;
            if g.leaf {
                let r = g.reg()?;
                g.op("setreg", &[Gen::n(r)]);
                made.push(r);
            } else {
                let s = g.slot();
                g.op("setstk", &[Gen::n(s)]);
                made.push(s);
            }
        }
        // (The parameters a lifting added, first, passed on as they are.)
        for (i, m) in made.into_iter().enumerate() {
            if g.leaf {
                g.op("movereg", &[Gen::n(m), Gen::n(t.added + i + 1)]);
            } else {
                g.op("stack", &[Gen::n(m)]);
                g.op("setstk", &[Gen::n(t.added + i)]);
            }
        }
        g.items.push(RItem::Branch(false, start));
        g.next_reg = regs;
        g.next_slot = slots;
        Some(())
    }
}
