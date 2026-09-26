//! Register code for a lambda (PLAN.md 13h′): the MacScheme machine's
//! instructions (`fixpt_heap::layout::regcode`), made from the same trees,
//! as its threaded word's twin.
//!
//! Where values live, the first way: a procedure that neither calls nor
//! calls out (a leaf, loops aside) keeps its parameters, its `let`s and its
//! temporaries in registers. Any other keeps its parameters and `let`s in
//! its frame, made on entry, since a call or a call-out may collect and
//! then only the frame holds values; its registers are only temporaries,
//! and arguments on their way to a call. What this compiler does not do yet
//! (`letrec`, `prompt`, `tagcase`, products, sums, arrays and bloblets
//! made, standard operations as values, more than `REGS` values), it
//! declines: the lambda keeps its threaded code alone.

use super::{find, Compiler, Env, Loc, This};
use crate::ast::{BlobletOp, Exp, ExpId};
use fixpt_heap::layout::regcode::{op, REGS};
use fixpt_heap::layout::threaded::routine;
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
}

enum RItem {
    Cell(Value),
    Label(usize),
    /// `branch` (false) or `branchf` (true) to a label.
    Branch(bool, usize),
    /// The frame's size, known when the body is done.
    Frame,
}

/// A standard operation, as register code does it.
enum Std {
    /// `op2 r`, operands in order, or swapped; then `not`, if asked.
    Op2 { r: &'static str, swap: bool, not: bool },
    Op1(&'static str),
    Op2Imm(&'static str, Value),
    Field(i64),
    /// A call-out: a runtime primitive, or a threaded routine.
    Prim(i64, usize),
    Threaded(&'static str, usize),
}

struct Gen {
    items: Vec<RItem>,
    leaf: bool,
    next_reg: usize,
    next_slot: usize,
    max_slot: usize,
    labels: usize,
    this: Option<(This, usize)>,
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
            RItem::Branch(..) => 2,
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
            }
            pos += size(i);
        }
        cells
    }
}

impl Compiler<'_> {
    /// A lambda's register code, whose closure captures `inner`'s free
    /// values in order, or none where this compiler declines.
    pub(super) fn register_code(&mut self, params: &[Sym], body: ExpId, inner: &Env, this: Option<This>) -> O<Vec<Value>> {
        if params.len() > REGS {
            return None;
        }
        let leaf = !self.r_collects(body, inner, this);
        let mut g = Gen { items: Vec::new(), leaf, next_reg: 0, next_slot: 0, max_slot: 0, labels: 0, this: None };
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
                g.op("store", &[Gen::n(i + 1), Gen::n(s)]);
            }
        }
        if let Some(t) = this {
            let start = g.label();
            g.items.push(RItem::Label(start));
            g.this = Some((t, start));
        }
        let mut te = inner.clone();
        self.r_exp(&mut g, body, &mut env, &mut te, true)?;
        Some(g.assemble())
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
            ("=" | "char=?" | "symbol=?", 2) => op2("eq", false, false),
            ("not", 1) => Some(Std::Op2Imm("eq", Value::FALSE)),
            ("null?", 1) => Some(Std::Op2Imm("eq", Value::NULL)),
            ("car", 1) => Some(Std::Op1("pair-car")),
            ("cdr", 1) => Some(Std::Op1("pair-cdr")),
            ("get", 1) => Some(Std::Field(2)),
            ("cons", 2) => Some(Std::Threaded("cons", 2)),
            _ => {
                // What the threaded compiler does with one runtime
                // primitive, register code does too.
                let mut tmp = Vec::new();
                self.standard_on(name, n, &mut tmp).ok()?;
                let prim = Value::fixnum(routine("prim") as i64);
                match tmp[..] {
                    [super::Item::Cell(r), super::Item::Cell(p), super::Item::Cell(k)] if r == prim => {
                        Some(Std::Prim(p.as_fixnum(), k.as_fixnum() as usize))
                    }
                    _ => None,
                }
            }
        }
    }

    fn r_standard_name(&self, env: &[(Sym, RLoc)], f: ExpId) -> O<String> {
        match self.c.arena.exp_at(f) {
            Exp::Var(n) if self.r_where(env, *n).is_none() => Some(self.name(*n).to_string()),
            _ => None,
        }
    }

    fn r_self_call(&self, g: &Gen, f: ExpId, nargs: usize, te: &Env, tail: bool) -> bool {
        match (g.this, self.c.arena.exp_at(f)) {
            (Some((t, _)), Exp::Var(n)) => tail && *n == t.name && find(te, *n) == Some(t.loc) && nargs == t.params,
            _ => false,
        }
    }

    /// Whether evaluating `x` may call or call out, and so collect. Loops
    /// do not; declined forms are said to, which does not matter.
    fn r_collects(&mut self, x: ExpId, e: &Env, this: Option<This>) -> bool {
        match self.c.arena.exp_at(x).clone() {
            Exp::Var(_) | Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Symbol(_) | Exp::Unit => false,
            Exp::If { test, then, els } => [test, then, els].iter().any(|y| self.r_collects(*y, e, this)),
            Exp::Let { bindings, body } => {
                bindings.iter().any(|(_, y)| self.r_collects(*y, e, this)) || self.r_collects(body, e, this)
            }
            Exp::Begin(items) => items.iter().any(|y| self.r_collects(*y, e, this)),
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } => self.r_collects(body, e, this),
            Exp::Extract(y, _) => self.r_collects(y, e, this),
            Exp::Bloblet { op: BlobletOp::Ref(_), args } => args.iter().any(|y| self.r_collects(*y, e, this)),
            Exp::App { fun, args } => {
                let args_collect = args.iter().any(|y| self.r_collects(*y, e, this));
                let loop_call = matches!((this, self.c.arena.exp_at(fun)), (Some(t), Exp::Var(n))
                    if *n == t.name && args.len() == t.params);
                let inline = match self.c.arena.exp_at(fun) {
                    Exp::Var(n) if self.where_is(e, *n).is_none() => {
                        let name = self.name(*n).to_string();
                        matches!(self.r_standard(&name, args.len()), Some(Std::Op1(_) | Std::Op2 { .. } | Std::Op2Imm(..) | Std::Field(_)))
                    }
                    _ => false,
                };
                args_collect || !(loop_call || inline)
            }
            _ => true,
        }
    }

    /// Whether `x` is a variable or a constant: evaluated in `RESULT` alone,
    /// with no effect, so it may wait until its value is needed.
    fn r_simple(&self, x: ExpId) -> bool {
        matches!(
            self.c.arena.exp_at(x),
            Exp::Var(_) | Exp::Int(_) | Exp::Bool(_) | Exp::Char(_) | Exp::Symbol(_) | Exp::Unit | Exp::Str(_)
        )
    }

    /// `x`'s value into `RESULT`; in tail position, returned.
    fn r_exp(&mut self, g: &mut Gen, x: ExpId, env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        match self.c.arena.exp_at(x).clone() {
            Exp::Var(n) => {
                match self.r_where(env, n) {
                    Some(RLoc::Reg(k)) => g.op("reg", &[Gen::n(k)]),
                    Some(RLoc::Slot(s)) => g.op("stack", &[Gen::n(s)]),
                    Some(RLoc::Free(i)) => g.op("lexical", &[Gen::n(i)]),
                    Some(RLoc::Global(c)) => g.op("global", &[c]),
                    Some(RLoc::Loop) => return None,
                    None if self.name(n) == "nil" => g.op("const", &[Value::NULL]),
                    None => return None,
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
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } => self.r_exp(g, body, env, te, tail)?,
            Exp::If { test, then, els } => {
                let (no, end) = (g.label(), g.label());
                self.r_exp(g, test, env, te, false)?;
                g.items.push(RItem::Branch(true, no));
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
            Exp::Let { bindings, body } => {
                let (depth, tdepth, regs, slots) = (env.len(), te.len(), g.next_reg, g.next_slot);
                let mut bound = Vec::new();
                for (n, init) in &bindings {
                    self.r_exp(g, *init, env, te, false)?;
                    let l = if g.leaf {
                        let r = g.reg()?;
                        g.op("setreg", &[Gen::n(r)]);
                        RLoc::Reg(r)
                    } else {
                        let s = g.slot();
                        g.op("setstk", &[Gen::n(s)]);
                        RLoc::Slot(s)
                    };
                    bound.push((*n, l));
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
                if g.leaf {
                    return None;
                }
                let ps: Vec<Sym> = params.iter().map(|(n, _)| *n).collect();
                let (w, fv) = self.lambda_word(&ps, body, te, None).ok()?;
                if fv.len() > REGS {
                    return None;
                }
                for (j, n) in fv.iter().enumerate() {
                    match self.r_where(env, *n)? {
                        RLoc::Slot(s) => g.op("load", &[Gen::n(j + 1), Gen::n(s)]),
                        RLoc::Free(i) => {
                            g.op("lexical", &[Gen::n(i)]);
                            g.op("setreg", &[Gen::n(j + 1)]);
                        }
                        _ => return None,
                    }
                }
                g.op("lambda", &[w, Gen::n(fv.len())]);
                g.done(tail);
            }
            Exp::App { fun, args } => self.r_app(g, fun, &args, env, te, tail)?,
            _ => return None,
        }
        Some(())
    }

    fn r_app(&mut self, g: &mut Gen, f: ExpId, args: &[ExpId], env: &mut Vec<(Sym, RLoc)>, te: &mut Env, tail: bool) -> O<()> {
        if self.r_self_call(g, f, args.len(), te, tail) {
            return self.r_loop(g, args, env, te);
        }
        if let Some(name) = self.r_standard_name(env, f) {
            match self.r_standard(&name, args.len())? {
                Std::Op2 { r, swap, not } => {
                    let (a, b) = if swap { (args[1], args[0]) } else { (args[0], args[1]) };
                    self.r_binary(g, r, a, b, env, te)?;
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
                Std::Prim(p, n) => {
                    self.r_args(g, args, env, te, None)?;
                    g.op("prim", &[Value::fixnum(p), Gen::n(n)]);
                }
                Std::Threaded(r, n) => {
                    self.r_args(g, args, env, te, None)?;
                    g.op("threaded", &[Value::fixnum(routine(r) as i64), Gen::n(n)]);
                }
            }
            g.done(tail);
            return Some(());
        }
        // A call: the arguments into REG1…REGn, the procedure in RESULT.
        if g.leaf || args.len() > REGS {
            return None;
        }
        self.r_args(g, args, env, te, Some(f))?;
        if tail {
            g.leave();
            g.op("tailinvoke", &[Gen::n(args.len())]);
        } else {
            g.op("invoke", &[Gen::n(args.len())]);
        }
        Some(())
    }

    /// `RESULT := r(a, b)`, `a` evaluated first. A constant `b` is an
    /// immediate. When `a` is simple, `b` is made first, into a register,
    /// since `a` has no effect to come before it; otherwise `a` is made
    /// first and kept, in a register or, if making `b` may collect, in the
    /// frame.
    fn r_binary(&mut self, g: &mut Gen, r: &str, a: ExpId, b: ExpId, env: &mut Vec<(Sym, RLoc)>, te: &mut Env) -> O<()> {
        let r = Value::fixnum(routine(r) as i64);
        let (regs, slots) = (g.next_reg, g.next_slot);
        if let Some(v) = self.r_constant(b) {
            self.r_exp(g, a, env, te, false)?;
            g.op("op2imm", &[r, v]);
        } else if let Some(RLoc::Reg(k)) = self.r_var(env, b) {
            // `b` is in a register already.
            self.r_exp(g, a, env, te, false)?;
            g.op("op2", &[r, Gen::n(k)]);
        } else if self.r_simple(a) {
            let k = g.reg()?;
            self.r_into(g, b, k, env, te)?;
            self.r_exp(g, a, env, te, false)?;
            g.op("op2", &[r, Gen::n(k)]);
        } else {
            self.r_exp(g, a, env, te, false)?;
            let collects = !g.leaf && self.r_collects(b, te, g.this.map(|(t, _)| t));
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
            g.op("op2", &[r, Gen::n(k)]);
        }
        g.next_reg = regs;
        g.next_slot = slots;
        Some(())
    }

    /// Where `x` is, if it is a variable.
    fn r_var(&self, env: &[(Sym, RLoc)], x: ExpId) -> O<RLoc> {
        match self.c.arena.exp_at(x) {
            Exp::Var(n) => self.r_where(env, *n),
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

    /// `x`'s value, if it is a constant that needs no allocation.
    fn r_constant(&mut self, x: ExpId) -> O<Value> {
        match self.c.arena.exp_at(x).clone() {
            Exp::Int(k) => Some(Value::fixnum(k)),
            Exp::Bool(b) => Some(Value::boolean(b)),
            Exp::Char(c) => Some(Value::char(c)),
            _ => None,
        }
    }

    /// The arguments into REG1…REGn, in order, and then `f`, if a call's,
    /// into RESULT. Not in a leaf: an argument that is not simple is kept in
    /// the frame until all are made; a simple one is made last.
    fn r_args(&mut self, g: &mut Gen, args: &[ExpId], env: &mut Vec<(Sym, RLoc)>, te: &mut Env, f: Option<ExpId>) -> O<()> {
        if g.leaf {
            return None;
        }
        let slots = g.next_slot;
        let mut kept = Vec::new();
        // The last argument that is not simple goes straight to its
        // register, when the procedure is simple too: all that follows it
        // is simple, and touches only RESULT and its own register.
        let direct = match f {
            Some(f) if !self.r_simple(f) => None,
            _ => args.iter().rposition(|a| !self.r_simple(*a)),
        };
        for (i, a) in args.iter().enumerate() {
            if self.r_simple(*a) {
                kept.push(None);
            } else if Some(i) == direct {
                self.r_exp(g, *a, env, te, false)?;
                g.op("setreg", &[Gen::n(i + 1)]);
                kept.push(Some(usize::MAX));
            } else {
                self.r_exp(g, *a, env, te, false)?;
                let s = g.slot();
                g.op("setstk", &[Gen::n(s)]);
                kept.push(Some(s));
            }
        }
        let fun = match f {
            Some(f) if !self.r_simple(f) => {
                self.r_exp(g, f, env, te, false)?;
                let s = g.slot();
                g.op("setstk", &[Gen::n(s)]);
                Some(s)
            }
            _ => None,
        };
        for (i, (a, k)) in args.iter().zip(&kept).enumerate() {
            match k {
                Some(usize::MAX) => {}
                Some(s) => g.op("load", &[Gen::n(i + 1), Gen::n(*s)]),
                None => self.r_into(g, *a, i + 1, env, te)?,
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
        for (i, m) in made.into_iter().enumerate() {
            if g.leaf {
                g.op("movereg", &[Gen::n(m), Gen::n(i + 1)]);
            } else {
                g.op("stack", &[Gen::n(m)]);
                g.op("setstk", &[Gen::n(i)]);
            }
        }
        let _ = t;
        g.items.push(RItem::Branch(false, start));
        g.next_reg = regs;
        g.next_slot = slots;
        Some(())
    }
}
