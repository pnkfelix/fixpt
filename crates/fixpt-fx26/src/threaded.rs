//! FX-26 compiled to threaded words, in Rust (PLAN.md, M13 step 13a): the
//! compiler written in FX-26 (`compile.fx`), decision for decision, over
//! the Rust checker's trees, so that the two make the same words and each
//! optimization can be written here first and checked end to end.
//!
//! The machine is `fixpt_engine::threaded`'s: a lambda's arguments are its
//! frame on the data stack, a `let`'s values are pushed onto the frame,
//! closures are flat, globals are cells, and a call in tail position is a
//! `tailcall`. A variable is resolved once: to a slot, a free value, a
//! global's cell, or, for `letrec`'s, a box in a slot or free value.

use crate::ast::{ArmBind, BlobletOp, Exp, ExpId};
use crate::check::Checker;
use crate::top::Top;
use fixpt_heap::layout::kind;
use fixpt_heap::layout::threaded::{routine, ROUTINES};
use fixpt_heap::{Heap, Value};
use fixpt_read::Sym;

/// One item of a word being built: a cell, a label, or a branch to one.
#[derive(Clone, Copy)]
enum Item {
    Cell(Value),
    Label(usize),
    Branch(usize),
    ZBranch(usize),
}

/// Where a variable is.
#[derive(Clone, Copy)]
enum Loc {
    Slot(usize),
    Free(usize),
    Global(Value),
    BoxedSlot(usize),
    BoxedFree(usize),
}

type Env = Vec<(Sym, Loc)>;

/// The innermost binding of `n` in `e`.
fn find(e: &Env, n: Sym) -> Option<Loc> {
    e.iter().rev().find(|(m, _)| *m == n).map(|(_, l)| *l)
}

pub struct Compiler<'a> {
    heap: &'a mut Heap,
    c: &'a Checker,
    /// The program's text, for naming each lambda by where its body starts,
    /// in characters, as the compiler written in FX-26 does.
    char_at: Vec<u32>,
    labels: usize,
    /// The globals, as compiling has reached them, and those given a cell
    /// ahead of their typed definitions.
    genv: Env,
    declared: Vec<Sym>,
}

type R<T> = Result<T, String>;

impl<'a> Compiler<'a> {
    pub fn new(heap: &'a mut Heap, c: &'a Checker, text: &str) -> Compiler<'a> {
        let mut char_at = vec![0; text.len() + 1];
        let mut n = 0;
        for (b, ch) in text.char_indices() {
            for x in &mut char_at[b..b + ch.len_utf8()] {
                *x = n;
            }
            n += 1;
        }
        char_at[text.len()] = n;
        Compiler { heap, c, char_at, labels: 0, genv: Vec::new(), declared: Vec::new() }
    }

    fn name(&self, s: Sym) -> &str {
        self.c.interner.name(s)
    }

    fn fresh(&mut self) -> usize {
        self.labels += 1;
        self.labels - 1
    }

    // ------------------------------------------------------------ code

    fn op(&self, code: &mut Vec<Item>, name: &str) {
        code.push(Item::Cell(Value::fixnum(routine(name) as i64)));
    }
    fn op1(&self, code: &mut Vec<Item>, name: &str, x: Value) {
        self.op(code, name);
        code.push(Item::Cell(x));
    }
    fn lit(&self, code: &mut Vec<Item>, x: Value) {
        self.op1(code, "lit", x);
    }
    fn int(&self, code: &mut Vec<Item>, n: i64) {
        self.lit(code, Value::fixnum(n));
    }
    fn unit(&mut self) -> Value {
        self.heap.intern("#u")
    }
    fn prim(&self, code: &mut Vec<Item>, name: &str, n: usize) -> R<()> {
        let p = fixpt_engine::threaded::runtime_primitive(name).ok_or_else(|| format!("no runtime primitive {name}"))?;
        self.op1(code, "prim", Value::fixnum(p as i64));
        code.push(Item::Cell(Value::fixnum(n as i64)));
        Ok(())
    }
    fn unit_after(&mut self, code: &mut Vec<Item>) {
        self.op(code, "drop");
        let u = self.unit();
        self.lit(code, u);
    }
    fn done(&self, code: &mut Vec<Item>, tail: bool) {
        if tail {
            self.op(code, "return");
        }
    }

    /// The items as a word: labels placed, branches resolved (an offset
    /// counts from the cell after it).
    fn assemble(&mut self, items: &[Item], name: &str) -> R<Value> {
        let size = |i: &Item| match i {
            Item::Cell(_) => 1,
            Item::Label(_) => 0,
            Item::Branch(_) | Item::ZBranch(_) => 2,
        };
        let mut at = vec![0i64; self.labels];
        let mut pos = 0;
        for i in items {
            if let Item::Label(n) = i {
                at[*n] = pos;
            }
            pos += size(i);
        }
        let mut cells = Vec::new();
        let mut pos = 0;
        for i in items {
            match i {
                Item::Cell(x) => cells.push(*x),
                Item::Label(_) => {}
                Item::Branch(n) | Item::ZBranch(n) => {
                    let r = if matches!(i, Item::Branch(_)) { "branch" } else { "0branch" };
                    cells.push(Value::fixnum(routine(r) as i64));
                    cells.push(Value::fixnum(at[*n] - (pos + 2)));
                }
            }
            pos += size(i);
        }
        let sym = self.heap.intern(name);
        self.heap.make_threaded_word(sym, &cells)
    }

    // ------------------------------------------------------- variables

    fn where_is(&self, e: &Env, n: Sym) -> Option<Loc> {
        find(e, n).or_else(|| find(&self.genv, n))
    }

    fn load(&self, code: &mut Vec<Item>, l: Loc) {
        match l {
            Loc::Slot(i) => self.op1(code, "slot", Value::fixnum(i as i64)),
            Loc::Free(i) => self.op1(code, "free", Value::fixnum(i as i64)),
            Loc::Global(g) => self.op1(code, "global", g),
            Loc::BoxedSlot(i) | Loc::BoxedFree(i) => {
                self.op1(code, if matches!(l, Loc::BoxedSlot(_)) { "slot" } else { "free" }, Value::fixnum(i as i64));
                self.int(code, 2);
                self.op(code, "field@");
            }
        }
    }

    // ------------------------------------------------------ free names
    // In `compile.fx`'s order: each new name goes in front, and the parts
    // of a form are visited as it visits them.

    fn free(&self, x: ExpId, bound: &[Sym], acc: &mut Vec<Sym>) {
        let adjoin = |acc: &mut Vec<Sym>, n: Sym| {
            if !acc.contains(&n) {
                acc.insert(0, n);
            }
        };
        let with = |bound: &[Sym], ns: &[Sym]| -> Vec<Sym> {
            let mut b: Vec<Sym> = ns.iter().rev().copied().collect();
            b.extend_from_slice(bound);
            b
        };
        match self.c.arena.exp_at(x).clone() {
            Exp::Var(n) => {
                if !bound.contains(&n) {
                    adjoin(acc, n);
                }
            }
            Exp::Lambda { params, body } => {
                let ps: Vec<Sym> = params.iter().map(|(n, _)| *n).collect();
                self.free(body, &with(bound, &ps), acc);
            }
            Exp::App { fun, args } => {
                for a in &args {
                    self.free(*a, bound, acc);
                }
                self.free(fun, bound, acc);
            }
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } => self.free(body, bound, acc),
            Exp::If { test, then, els } => {
                self.free(els, bound, acc);
                self.free(then, bound, acc);
                self.free(test, bound, acc);
            }
            Exp::Letrec { bindings, body } => {
                let ns: Vec<Sym> = bindings.iter().map(|(n, _, _)| *n).collect();
                let inner = with(bound, &ns);
                for (_, _, init) in &bindings {
                    self.free(*init, &inner, acc);
                }
                self.free(body, &inner, acc);
            }
            Exp::Let { bindings, body } => {
                for (_, init) in &bindings {
                    self.free(*init, bound, acc);
                }
                let ns: Vec<Sym> = bindings.iter().map(|(n, _)| *n).collect();
                self.free(body, &with(bound, &ns), acc);
            }
            Exp::Begin(items) => {
                for i in items {
                    self.free(i, bound, acc);
                }
            }
            Exp::Prompt { tag, body, handler } => {
                self.free(handler, bound, acc);
                self.free(body, bound, acc);
                self.free(tag, bound, acc);
            }
            Exp::Bloblet { args, .. } => {
                for a in args {
                    self.free(a, bound, acc);
                }
            }
            Exp::Product(fields) => {
                for (_, x) in fields {
                    self.free(x, bound, acc);
                }
            }
            Exp::Extract(x, _) | Exp::Sum(_, x) => self.free(x, bound, acc),
            Exp::TagCase { scrutinee, arms, els } => {
                if let Some((y, body)) = els {
                    self.free(body, &with(bound, &[y]), acc);
                }
                for arm in &arms {
                    self.free(arm.body, &with(bound, &arm.names()), acc);
                }
                self.free(scrutinee, bound, acc);
            }
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Symbol(_) | Exp::Unit => {}
        }
    }

    // ----------------------------------------------------- expressions
    // `depth` is how many values are on the frame above its start, so the
    // next value pushed is slot `depth`. In tail position, code ends the
    // word: with a `tailcall`, or with `return` after the value.

    fn exps(&mut self, xs: &[ExpId], e: &Env, depth: usize, code: &mut Vec<Item>) -> R<usize> {
        for (i, x) in xs.iter().enumerate() {
            self.exp(*x, e, depth + i, code, false)?;
        }
        Ok(xs.len())
    }

    /// After a body whose value is on top of `n` values bound from `slot`
    /// up: the value into `slot`, the others dropped. Nothing in tail
    /// position, where `return` drops the whole frame.
    fn unbind(&self, code: &mut Vec<Item>, slot: usize, n: usize, tail: bool) {
        if tail || n == 0 {
            return;
        }
        self.op1(code, "slot!", Value::fixnum(slot as i64));
        for _ in 1..n {
            self.op(code, "drop");
        }
    }

    fn exp(&mut self, x: ExpId, e: &Env, depth: usize, code: &mut Vec<Item>, tail: bool) -> R<()> {
        match self.c.arena.exp_at(x).clone() {
            Exp::Var(n) => {
                match self.where_is(e, n) {
                    Some(l) => self.load(code, l),
                    None if self.name(n) == "nil" => self.lit(code, Value::NULL),
                    None => {
                        let name = self.name(n).to_string();
                        self.standard_value(&name, code)?;
                    }
                }
                self.done(code, tail);
            }
            Exp::Int(n) => {
                self.int(code, n);
                self.done(code, tail);
            }
            Exp::Bool(b) => {
                self.lit(code, Value::boolean(b));
                self.done(code, tail);
            }
            Exp::Str(s) => {
                let v = self.heap.make_string(&s);
                self.lit(code, v);
                self.done(code, tail);
            }
            Exp::Char(ch) => {
                self.lit(code, Value::char(ch));
                self.done(code, tail);
            }
            Exp::Symbol(s) => {
                let v = self.heap.intern(self.c.interner.name(s));
                self.lit(code, v);
                self.done(code, tail);
            }
            Exp::Unit => {
                let u = self.unit();
                self.lit(code, u);
                self.done(code, tail);
            }
            Exp::Lambda { params, body } => {
                let ps: Vec<Sym> = params.iter().map(|(n, _)| *n).collect();
                self.lambda(&ps, body, e, depth, code)?;
                self.done(code, tail);
            }
            Exp::App { fun, args } => self.app(fun, &args, e, depth, code, tail)?,
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } => self.exp(body, e, depth, code, tail)?,
            Exp::If { test, then, els } => {
                let (no, end) = (self.fresh(), self.fresh());
                self.exp(test, e, depth, code, false)?;
                code.push(Item::ZBranch(no));
                self.exp(then, e, depth, code, tail)?;
                if !tail {
                    code.push(Item::Branch(end));
                }
                code.push(Item::Label(no));
                self.exp(els, e, depth, code, tail)?;
                code.push(Item::Label(end));
            }
            Exp::Let { bindings, body } => {
                // Each value pushed, in the scope outside; the names are the slots.
                let mut inner = e.clone();
                for (i, (n, init)) in bindings.iter().enumerate() {
                    self.exp(*init, e, depth + i, code, false)?;
                    inner.push((*n, Loc::Slot(depth + i)));
                }
                let n = bindings.len();
                self.exp(body, &inner, depth + n, code, tail)?;
                self.unbind(code, depth, n, tail);
            }
            Exp::Letrec { bindings, body } => {
                // A box per name first, so each closure can carry the box
                // before it has its value; then each value into its box.
                let n = bindings.len();
                let mut inner = e.clone();
                for (i, (name, _, _)) in bindings.iter().enumerate() {
                    // Until filled, a procedure that traps when called.
                    self.prim(code, "%fx26-undefined", 0)?;
                    self.prim(code, "%make-box", 1)?;
                    inner.push((*name, Loc::BoxedSlot(depth + i)));
                }
                for (i, (_, _, init)) in bindings.iter().enumerate() {
                    self.op1(code, "slot", Value::fixnum((depth + i) as i64));
                    self.exp(*init, &inner, depth + n + 1, code, false)?;
                    self.op(code, "swap");
                    self.int(code, 2);
                    self.op(code, "field!");
                }
                self.exp(body, &inner, depth + n, code, tail)?;
                self.unbind(code, depth, n, tail);
            }
            Exp::Begin(items) => self.begin(&items, e, depth, code, tail)?,
            Exp::Prompt { tag, body, handler } => {
                self.exp(tag, e, depth, code, false)?;
                self.exp(handler, e, depth + 1, code, false)?;
                self.lambda(&[], body, e, depth + 2, code)?;
                self.op(code, "prompt");
                self.done(code, tail);
            }
            Exp::Bloblet { op, args } => {
                self.bloblet(op, &args, e, depth, code)?;
                self.done(code, tail);
            }
            Exp::Product(fields) => {
                self.int(code, 37);
                for (i, (_, f)) in fields.iter().enumerate() {
                    self.exp(*f, e, depth + 1 + i, code, false)?;
                }
                self.prim(code, "%make-frozen", 1 + fields.len())?;
                self.done(code, tail);
            }
            Exp::Extract(p, _) => {
                let i = *self.c.facts.field_index.get(&x).ok_or("an extract the checker did not see")?;
                self.exp(p, e, depth, code, false)?;
                self.int(code, i as i64 + 2);
                self.op(code, "field@");
                self.done(code, tail);
            }
            Exp::Sum(t, v) => {
                self.int(code, 36);
                let sym = self.heap.intern(self.c.interner.name(t));
                self.lit(code, sym);
                self.exp(v, e, depth + 2, code, false)?;
                self.prim(code, "%make-frozen", 3)?;
                self.done(code, tail);
            }
            Exp::TagCase { scrutinee, arms, els } => {
                let end = self.fresh();
                self.exp(scrutinee, e, depth, code, false)?;
                self.arms(&arms, &els, e, depth, code, tail, end)?;
                code.push(Item::Label(end));
            }
        }
        Ok(())
    }

    fn begin(&mut self, es: &[ExpId], e: &Env, depth: usize, code: &mut Vec<Item>, tail: bool) -> R<()> {
        match es {
            [] => {
                let u = self.unit();
                self.lit(code, u);
                self.done(code, tail);
            }
            [last] => self.exp(*last, e, depth, code, tail)?,
            [first, rest @ ..] => {
                self.exp(*first, e, depth, code, false)?;
                self.op(code, "drop");
                self.begin(rest, e, depth, code, tail)?;
            }
        }
        Ok(())
    }

    /// A lambda: its free values pushed, then its word closed over them.
    fn lambda(&mut self, params: &[Sym], body: ExpId, e: &Env, depth: usize, code: &mut Vec<Item>) -> R<()> {
        let mut free = Vec::new();
        self.free(body, &params.iter().rev().copied().collect::<Vec<_>>(), &mut free);
        // The free names that are locals here, not globals or standard ones.
        let fv: Vec<Sym> = free.into_iter().filter(|n| find(e, *n).is_some()).collect();
        let mut inner: Env = params.iter().enumerate().map(|(i, p)| (*p, Loc::Slot(i))).collect();
        for (i, n) in fv.iter().enumerate() {
            let l = match find(e, *n).expect("found") {
                Loc::BoxedSlot(_) | Loc::BoxedFree(_) => Loc::BoxedFree(i),
                _ => Loc::Free(i),
            };
            inner.push((*n, l));
        }
        // Each captured value, or its box, as the closure will hold it.
        for n in &fv {
            match find(e, *n).expect("found") {
                Loc::Slot(i) | Loc::BoxedSlot(i) => self.op1(code, "slot", Value::fixnum(i as i64)),
                Loc::Free(i) | Loc::BoxedFree(i) => self.op1(code, "free", Value::fixnum(i as i64)),
                Loc::Global(_) => return Err("a global is not captured".into()),
            }
        }
        let mut body_code = Vec::new();
        self.exp(body, &inner, params.len(), &mut body_code, true)?;
        // Named for where its body starts, so that a profile can say which.
        let start = self.char_at[self.c.arena.span_of(body).start as usize];
        let w = self.assemble(&body_code, &format!("lambda@{start}"))?;
        self.op1(code, "closure", w);
        code.push(Item::Cell(Value::fixnum(fv.len() as i64)));
        let _ = depth;
        Ok(())
    }

    // ---------------------------------------------------- applications

    fn app(&mut self, f: ExpId, args: &[ExpId], e: &Env, depth: usize, code: &mut Vec<Item>, tail: bool) -> R<()> {
        let standard = match self.c.arena.exp_at(f) {
            Exp::Var(n) if self.where_is(e, *n).is_none() => Some(self.name(*n).to_string()),
            _ => None,
        };
        match standard {
            None => {
                let n = self.exps(args, e, depth, code)?;
                self.exp(f, e, depth + n, code, false)?;
                // The checker typed the callee a subroutine: a typed call.
                self.op1(code, if tail { "ttailcall" } else { "tcall" }, Value::fixnum(n as i64));
            }
            // In tail position, the mark replaces this frame's: a loop that
            // marks each iteration runs in constant space.
            Some(s) if tail && s == "with-mark" => {
                self.exps(args, e, depth, code)?;
                self.op(code, "withmark-tail");
            }
            Some(s) => {
                self.standard(&s, args, e, depth, code)?;
                self.done(code, tail);
            }
        }
        Ok(())
    }

    /// How many arguments a standard operation takes, as a value.
    fn arity(n: &str) -> Option<usize> {
        match n {
            "make-continuation-prompt-tag" | "make-continuation-mark-key" => Some(0),
            "car" | "cdr" | "null?" | "not" | "new" | "get" | "char->integer" | "integer->char" | "string-length"
            | "symbol->string" | "string->symbol" | "char->string" | "array-length" | "current-marks" | "cwcc" => Some(1),
            "with-mark" | "array-set!" | "substring" => Some(3),
            "+" | "-" | "*" | "<" | ">" | "<=" | ">=" | "=" | "modulo" | "quotient" | "cons" | "set-car!" | "set-cdr!"
            | "set" | "char=?" | "string-append" | "string=?" | "symbol=?" | "array-ref" | "string-ref" | "make-array"
            | "abort-current-continuation" | "call-with-composable-continuation" | "first-mark" | "marks-of" => Some(2),
            _ => None,
        }
    }

    /// A standard operation as a value: a closure of its arity whose body
    /// applies it to its parameters.
    fn standard_value(&mut self, name: &str, code: &mut Vec<Item>) -> R<()> {
        let n = Self::arity(name).ok_or_else(|| format!("not yet compiled as a value: {name}"))?;
        let mut body = Vec::new();
        if name == "make-array" {
            self.int(&mut body, 0);
        }
        for i in 0..n {
            self.op1(&mut body, "slot", Value::fixnum(i as i64));
        }
        if name == "make-array" {
            self.prim(&mut body, "%make-bloblet-filled", 3)?;
        } else {
            self.standard_on(name, n, &mut body)?;
        }
        self.op(&mut body, "return");
        let w = self.assemble(&body, name)?;
        self.op1(code, "closure", w);
        code.push(Item::Cell(Value::fixnum(0)));
        Ok(())
    }

    fn standard(&mut self, name: &str, args: &[ExpId], e: &Env, depth: usize, code: &mut Vec<Item>) -> R<()> {
        if name == "make-array" {
            // (%make-bloblet-filled 0 n fill): the 0 first, under the others.
            self.int(code, 0);
            self.exps(args, e, depth + 1, code)?;
            return self.prim(code, "%make-bloblet-filled", 3);
        }
        let n = self.exps(args, e, depth, code)?;
        self.standard_on(name, n, code)
    }

    /// A standard operation, open-coded: a routine, or a runtime primitive,
    /// with FX-26's conventions made plain (mutators give unit; arrays skip
    /// the trailer's field).
    fn standard_on(&mut self, name: &str, n: usize, code: &mut Vec<Item>) -> R<()> {
        let f = Value::FALSE;
        match name {
            "+" => self.op(code, "+"),
            "-" => self.op(code, "-"),
            "<" => self.op(code, "<"),
            ">" => {
                self.op(code, "swap");
                self.op(code, "<");
            }
            "<=" => {
                self.op(code, "swap");
                self.op(code, "<");
                self.lit(code, f);
                self.op(code, "eq");
            }
            ">=" => {
                self.op(code, "<");
                self.lit(code, f);
                self.op(code, "eq");
            }
            "=" | "symbol=?" | "char=?" => self.op(code, "eq"),
            "cons" => self.op(code, "cons"),
            "car" => self.op(code, "car"),
            "cdr" => self.op(code, "cdr"),
            "set-car!" | "set-cdr!" => {
                self.prim(code, name, 2)?;
                self.unit_after(code);
            }
            "new" => self.prim(code, "%make-box", 1)?,
            "get" => {
                self.int(code, 2);
                self.op(code, "field@");
            }
            "set" => {
                self.op(code, "swap");
                self.int(code, 2);
                self.op(code, "field!");
                let u = self.unit();
                self.lit(code, u);
            }
            "null?" => {
                self.lit(code, Value::NULL);
                self.op(code, "eq");
            }
            "not" => {
                self.lit(code, f);
                self.op(code, "eq");
            }
            "char->string" => self.prim(code, "string", 1)?,
            "make-continuation-prompt-tag" | "make-continuation-mark-key" => {
                let u = self.unit();
                self.lit(code, u);
                self.prim(code, "%make-box", 1)?;
            }
            "abort-current-continuation" => self.op(code, "abort"),
            "call-with-composable-continuation" => self.op(code, "callcomp"),
            "cwcc" => self.op(code, "callcc"),
            "with-mark" => self.op(code, "withmark"),
            "first-mark" => self.op(code, "firstmark"),
            "current-marks" => self.op(code, "currentmarks"),
            "marks-of" => self.op(code, "marksof"),
            "array-ref" => {
                self.int(code, 2);
                self.op(code, "+");
                self.op(code, "field@");
            }
            "array-set!" => {
                self.op(code, "swap");
                self.int(code, 2);
                self.op(code, "+");
                self.op(code, "swap");
                self.prim(code, "%bloblet-set!", 3)?;
                self.unit_after(code);
            }
            "array-length" => {
                self.prim(code, "%bloblet-fields", 1)?;
                self.int(code, 1);
                self.op(code, "-");
            }
            "*" | "modulo" | "quotient" | "char->integer" | "integer->char" | "string-append" | "string-length"
            | "string-ref" | "substring" | "string=?" | "string->symbol" | "symbol->string" => self.prim(code, name, n)?,
            // The rest, as the lowering runs them: a runtime primitive, or
            // nothing at all.
            _ => match standard_primitive(name) {
                Some("%fx26-identity") => {}
                Some(p) => self.prim(code, p, n)?,
                None => return Err(format!("not yet compiled: {name}")),
            },
        }
        Ok(())
    }

    fn bloblet(&mut self, op: BlobletOp, args: &[ExpId], e: &Env, depth: usize, code: &mut Vec<Item>) -> R<()> {
        match op {
            BlobletOp::Make => {
                let n = self.exps(args, e, depth, code)?;
                self.prim(code, "%make-bloblet", n)?;
            }
            BlobletOp::Ref(i) => {
                self.exps(args, e, depth, code)?;
                self.int(code, i as i64 + 2);
                self.op(code, "field@");
            }
            BlobletOp::Set(i) => {
                self.exp(args[0], e, depth, code, false)?;
                self.int(code, i as i64 + 2);
                self.exp(args[1], e, depth + 2, code, false)?;
                self.prim(code, "%bloblet-set!", 3)?;
                self.unit_after(code);
            }
            BlobletOp::Freeze => {
                self.exps(args, e, depth, code)?;
                self.op(code, "dup");
                self.lit(code, Value::TRUE);
                self.lit(code, Value::FALSE);
                self.prim(code, "%bloblet-freeze!", 3)?;
                self.op(code, "drop");
            }
            BlobletOp::Byte => {
                let n = self.exps(args, e, depth, code)?;
                self.prim(code, "%bloblet-byte", n)?;
            }
            BlobletOp::SetByte => {
                let n = self.exps(args, e, depth, code)?;
                self.prim(code, "%bloblet-set-byte!", n)?;
                self.unit_after(code);
            }
            BlobletOp::Bytes => {
                let n = self.exps(args, e, depth, code)?;
                self.prim(code, "%bloblet-bytes", n)?;
            }
        }
        Ok(())
    }

    // --------------------------------------------------------- tagcase

    #[allow(clippy::too_many_arguments)]
    fn arms(
        &mut self,
        arms: &[crate::ast::Arm],
        els: &Option<(Sym, ExpId)>,
        e: &Env,
        depth: usize,
        code: &mut Vec<Item>,
        tail: bool,
        end: usize,
    ) -> R<()> {
        let Some((arm, rest)) = arms.split_first() else {
            match els {
                // A checked program covers every tag; this is never reached.
                None => {
                    self.lit(code, Value::FALSE);
                    self.int(code, 0);
                    self.op(code, "field@");
                    self.done(code, tail);
                }
                Some((y, body)) => {
                    let mut inner = e.clone();
                    inner.push((*y, Loc::Slot(depth)));
                    self.exp(*body, &inner, depth + 1, code, tail)?;
                    self.unbind(code, depth, 1, tail);
                }
            }
            return Ok(());
        };
        let next = self.fresh();
        // Is the tag this arm's?
        self.op1(code, "slot", Value::fixnum(depth as i64));
        self.int(code, 2);
        self.op(code, "field@");
        let tag = self.heap.intern(self.c.interner.name(arm.tag));
        self.lit(code, tag);
        self.op(code, "eq");
        code.push(Item::ZBranch(next));
        // The value, or its product's members, as slots after the sum.
        self.op1(code, "slot", Value::fixnum(depth as i64));
        self.int(code, 3);
        self.op(code, "field@");
        let mut bound = e.clone();
        let n = match &arm.bind {
            ArmBind::Value(x) => {
                bound.push((*x, Loc::Slot(depth + 1)));
                1
            }
            ArmBind::Fields(xs) => {
                for (j, x) in xs.iter().enumerate() {
                    self.op1(code, "slot", Value::fixnum(depth as i64 + 1));
                    self.int(code, j as i64 + 2);
                    self.op(code, "field@");
                    bound.push((*x, Loc::Slot(depth + 2 + j)));
                }
                1 + xs.len()
            }
        };
        self.exp(arm.body, &bound, depth + 1 + n, code, tail)?;
        self.unbind(code, depth, n + 1, tail);
        if !tail {
            code.push(Item::Branch(end));
        }
        code.push(Item::Label(next));
        self.arms(rest, els, e, depth, code, tail, end)
    }

    // -------------------------------------------------------- programs

    fn push_global(&mut self, n: Sym) -> Value {
        let undefined = self.heap.undefined_closure();
        let name = self.heap.intern(self.c.interner.name(n));
        let g = self.heap.make_bloblet(kind("bloblet"), 2, 0, true);
        self.heap.set_bloblet_slot(g, 2, undefined);
        self.heap.set_bloblet_slot(g, 3, name);
        self.genv.push((n, Loc::Global(g)));
        g
    }

    /// A checked program's forms, as the checker found them, to one word
    /// that runs it and leaves its last expression's value (unit if none).
    pub fn program(&mut self, tops: &[Top]) -> R<Value> {
        for t in tops {
            if let Top::Define { name, recursive: true, .. } = t
                && find(&self.genv, *name).is_none()
            {
                self.push_global(*name);
                self.declared.push(*name);
            }
        }
        let mut code = Vec::new();
        let mut has_value = false;
        for t in tops {
            match t {
                Top::Define { name, exp, recursive, .. } => {
                    if has_value {
                        self.op(&mut code, "drop");
                    }
                    let g = if !recursive {
                        self.exp(*exp, &Vec::new(), 0, &mut code, false)?;
                        self.push_global(*name)
                    } else {
                        let g = match self.declared.iter().position(|n| n == name) {
                            Some(i) => {
                                self.declared.remove(i);
                                match find(&self.genv, *name) {
                                    Some(Loc::Global(g)) => g,
                                    _ => return Err("not a global".into()),
                                }
                            }
                            None => self.push_global(*name),
                        };
                        self.exp(*exp, &Vec::new(), 0, &mut code, false)?;
                        g
                    };
                    self.op1(&mut code, "global!", g);
                    has_value = false;
                }
                Top::Exp(k) => {
                    if has_value {
                        self.op(&mut code, "drop");
                    }
                    self.exp(k.exp, &Vec::new(), 0, &mut code, false)?;
                    has_value = true;
                }
                _ => {}
            }
        }
        if !has_value {
            let u = self.unit();
            self.lit(&mut code, u);
        }
        self.op(&mut code, "exit");
        self.assemble(&code, "program")
    }
}

/// The runtime primitive a standard operation runs as: as `standard.fx`
/// says, from the lowering's table.
fn standard_primitive(name: &str) -> Option<&'static str> {
    crate::lower::STANDARD.iter().find(|(fx, _, _)| *fx == name).and_then(|(_, scheme, _)| {
        (*scheme == "%fx26-identity" || fixpt_engine::threaded::runtime_primitive(scheme).is_some()).then_some(*scheme)
    })
}

/// Every routine this compiler emits names one the machine has.
const _: () = assert!(ROUTINES.len() > 38);
