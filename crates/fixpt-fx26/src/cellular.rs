//! FX-26 compiled to cellular words, in Rust (PLAN.md, M13 step 13a): the
//! compiler written in FX-26 (`compile.fx`), decision for decision, over
//! the Rust checker's trees, so that the two make the same words and each
//! optimization can be written here first and checked end to end.
//!
//! The machine is `fixpt_engine::cellular`'s: a lambda's arguments are its
//! frame on the data stack, a `let`'s values are pushed onto the frame,
//! closures are flat, globals are cells, and a call in tail position is a
//! `tailcall`. A variable is resolved once: to a slot, a free value, a
//! global's cell, or, for `letrec`'s, a box in a slot or free value.

use crate::ast::{ArmBind, BlobletOp, Exp, ExpId, TyId};
use std::collections::HashMap;
use crate::check::Checker;
use crate::top::Top;
use fixpt_heap::layout::kind;
use fixpt_heap::layout::cellular::{routine, CLOSURE_FREE0, ROUTINES, WORD_TWIN};

mod regcode;
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
#[derive(Clone, Copy, PartialEq)]
enum Loc {
    Slot(usize),
    Free(usize),
    Global(Value),
    /// A `letrec` sibling not made yet, to be in slot `i`: a closure that
    /// captures it holds a placeholder, patched once every sibling is made.
    Pending(usize),
    /// A `letrec`-bound procedure, in its own body, where it is only
    /// called in tail position: each call is a jump back to its start.
    Loop,
    /// A `letrec`-bound procedure lambda-lifted (`Lift`, `lifts`'s index):
    /// only called, by a closure over nothing made once, with the names
    /// it would have captured passed first.
    Lifted(usize),
}

/// A `letrec`-bound procedure lambda-lifted, as Twobit's pass 2 lifts
/// (`pass2p2.sch`): its closure, over nothing, made while compiling; the
/// names it would have captured, each passed as an argument before its
/// own; its own parameters' count.
struct Lift {
    closure: Value,
    added: Vec<Sym>,
}

/// A lambda's word, made by the stack code of the body it is in: where
/// its body is, its parameters and its own name, and the names it captures.
struct Made {
    span: (u32, u32),
    params: Vec<Sym>,
    own: Option<Sym>,
    word: Value,
    fv: Vec<Sym>,
}

/// The word being compiled, when it is a `letrec`-bound procedure's: a
/// tail call of `name`, still bound at `loc`, is a loop (13e).
#[derive(Clone, Copy)]
struct This {
    name: Sym,
    loc: Loc,
    params: usize,
    start: usize,
    /// How many of the parameters, first, were added by lifting it: a
    /// loop passes them on as they are.
    added: usize,
}

type Env = Vec<(Sym, Loc)>;

/// The innermost binding of `n` in `e`.
fn find(e: &[(Sym, Loc)], n: Sym) -> Option<Loc> {
    e.iter().rev().find(|(m, _)| *m == n).map(|(_, l)| *l)
}

pub struct Compiler<'a> {
    heap: &'a mut Heap,
    c: &'a Checker,
    /// The program's text, for naming each lambda by where its body starts,
    /// in characters, as the compiler written in FX-26 does.
    char_at: Vec<u32>,
    labels: usize,
    /// The globals, as compiling has reached them.
    genv: Env,
    /// The same by name: each name's globals, newest last, with each one's
    /// place in `genv`, so that finding a global is not a search of them all.
    genv_index: std::collections::HashMap<Sym, Vec<(usize, Loc)>>,
    this: Option<This>,
    /// Whether each lambda also gets register code (PLAN.md 13h′), as its
    /// word's twin.
    pub registers: bool,
    /// For each lambda given register code or declined: its name, and why
    /// it was declined (the first form the register compiler does not do).
    pub register_report: Vec<(String, Option<String>)>,
    /// The words of the lambdas the body being compiled makes, as its stack
    /// code made them; and those of the body whose register code is being
    /// made, which uses them rather than making each again (and each of
    /// theirs, twice as many at every depth).
    made: Vec<Made>,
    reuse: Vec<Made>,
    /// The procedures lambda-lifted; and, by where each `letrec` is, its
    /// members' (none if it is not lifted), so that its register code
    /// lifts it as its stack code did, with the same words.
    lifts: Vec<Lift>,
    lifted: HashMap<(u32, u32), Option<Vec<usize>>>,
    /// The parameters added to the lambda about to be compiled.
    lifting_added: usize,
    declined: Option<String>,
    /// The global procedures a call in register code may inline, as
    /// `inline_room` allows:
    /// each one's name, word, parameters, body, and how many globals there
    /// were when its body was compiled, which are those its names see.
    inlines: Vec<Inline>,
    /// While an inlined body is compiled: how many globals it sees.
    genv_limit: Option<usize>,
    /// The globals whose bodies are being inlined, which are not again.
    inlining: Vec<Sym>,
    /// The word of the lambda compiled last.
    last_word: Value,
    /// While a top-level `(define m (module …))` is compiled: its members
    /// that are lambdas naming no other member, each with its word,
    /// parameters and body, to be inlined, if small, where a re-export
    /// `(define f (with m f))` is called (`TODO.md` §38).
    module_members: Option<Vec<(Sym, Value, Vec<Sym>, ExpId)>>,
    /// Each top-level module's such members, by its global, with how many
    /// globals their bodies see.
    modules: Vec<(Sym, usize, Vec<(Sym, Value, Vec<Sym>, ExpId)>)>,
    /// The global procedures a call in register code may specialize at a
    /// lambda argument (`regcode::r_specialize`).
    specials: Vec<Special>,
    /// While a procedure specialized at a lambda is compiled: which.
    spec: Option<Spec>,
    /// The name the next lambda's word gets, if not where its body starts.
    word_name: Option<String>,
    /// The name of the lambda whose body is compiled, without where it
    /// starts: an inner lambda's word is named within it, `outer/inner@N`.
    scope_name: Option<String>,
    /// While a `let`'s binding's init is compiled, the binding's name: the
    /// first lambda compiled in it is named for it.
    bind_name: Option<Sym>,
    /// The top-level definition whose lambda is compiled next: its name.
    defining: Option<Sym>,
    /// While a body's fast version is compiled (`regcode::register_code`):
    /// the globals it assumes hold what they held, and what that was.
    assume: Option<Vec<(Value, Value)>>,
    /// Each expression's effect summary, by span, once asked.
    summaries: Option<std::collections::HashMap<(u32, u32), u8>>,
    /// The top-level definition whose body is being compiled: its name and
    /// arity.
    own_now: Option<(Sym, usize)>,
    /// While deciding whether a body is a leaf: a plain call in tail
    /// position, its arguments collecting nothing, counts as no call
    /// (`regcode::r_leaf_tail_call`).
    tail_calls_leave: bool,
}

/// A global procedure whose parameter `param` is only called (with
/// `arity` arguments) or passed as itself to a call of the procedure: a
/// call with a lambda there may run a copy of the procedure made for that
/// lambda, the lambda's body inlined where the parameter is called.
struct Special {
    name: Sym,
    word: Value,
    params: Vec<Sym>,
    body: ExpId,
    genv_len: usize,
    param: usize,
    arity: usize,
}

/// A procedure being specialized: its global's name, cell and word, the
/// parameter, and the lambda (its parameters, body, the names its closure
/// captures in order, and the globals it sees).
#[derive(Clone)]
struct Spec {
    name: Sym,
    cell: Value,
    word: Value,
    param: usize,
    param_name: Sym,
    n: usize,
    arity: usize,
    lam_params: Vec<Sym>,
    lam_body: ExpId,
    lam_fv: Vec<Sym>,
    lam_genv: Option<usize>,
}

/// A small global procedure a call may inline, guarded, in register code
/// (`regcode::r_inline`).
struct Inline {
    name: Sym,
    word: Value,
    params: Vec<Sym>,
    body: ExpId,
    genv_len: usize,
}

/// The most parser-tree nodes a body may have to be inlined.
const INLINE_LIMIT: i64 = 20;
/// The most a procedure's body may have to be specialized at a lambda.
const SPECIAL_LIMIT: i64 = 60;

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
        Compiler { heap, c, char_at, labels: 0, genv: Vec::new(), genv_index: Default::default(), this: None, registers: false,
            register_report: Vec::new(),
            made: Vec::new(),
            reuse: Vec::new(),
            lifts: Vec::new(),
            lifted: HashMap::new(),
            lifting_added: 0,
            declined: None,
            inlines: Vec::new(),
            genv_limit: None,
            inlining: Vec::new(),
            last_word: Value::FALSE,
            module_members: None,
            modules: Vec::new(),
            specials: Vec::new(),
            spec: None,
            word_name: None,
            scope_name: None,
            bind_name: None,
            defining: None,
            assume: None,
            summaries: None,
            own_now: None,
            tail_calls_leave: false,
        }
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
    /// Field `k` of a bloblet whose type says it has one.
    fn field(&self, code: &mut Vec<Item>, k: i64) {
        self.op1(code, "field", Value::fixnum(k));
    }
    fn unit(&mut self) -> Value {
        self.heap.intern("#u")
    }
    fn prim(&self, code: &mut Vec<Item>, name: &str, n: usize) -> R<()> {
        let p = fixpt_engine::cellular::runtime_primitive(name).ok_or_else(|| format!("no runtime primitive {name}"))?;
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
        self.heap.make_cellular_word(sym, &cells)
    }

    // ------------------------------------------------------- variables

    /// `n`'s newest global of the first `limit`.
    fn global(&self, n: Sym, limit: usize) -> Option<Loc> {
        self.genv_index.get(&n)?.iter().rev().find(|(i, _)| *i < limit).map(|(_, l)| *l)
    }

    fn where_is(&self, e: &Env, n: Sym) -> Option<Loc> {
        find(e, n).or_else(|| self.global(n, self.genv_limit.unwrap_or(self.genv.len())))
    }

    fn load(&self, code: &mut Vec<Item>, l: Loc) {
        match l {
            Loc::Slot(i) => self.op1(code, "slot", Value::fixnum(i as i64)),
            Loc::Free(i) => self.op1(code, "free", Value::fixnum(i as i64)),
            Loc::Global(g) => self.op1(code, "global", g),
            Loc::Loop => unreachable!("a loop is only ever called, in tail position"),
            Loc::Pending(_) => unreachable!("a letrec sibling not made yet is only captured"),
            Loc::Lifted(_) => unreachable!("a lifted procedure is only called"),
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
            // A module's items see all of them, as a `letrec*`'s.
            Exp::Module(items) => {
                let mut names = Vec::new();
                for item in &items {
                    match item {
                        crate::ast::ModItem::Desc { .. } => {}
                        crate::ast::ModItem::Abs { up, down, .. } => names.extend([*up, *down]),
                        crate::ast::ModItem::Val { name, .. } => names.push(*name),
                        crate::ast::ModItem::Rec(group) => names.extend(group.iter().map(|(n, _, _)| *n)),
                    }
                }
                let inner = with(bound, &names);
                for item in items {
                    match item {
                        crate::ast::ModItem::Desc { .. } => {}
                        crate::ast::ModItem::Abs { up_fn, down_fn, .. } => {
                            self.free(up_fn, &inner, acc);
                            self.free(down_fn, &inner, acc);
                        }
                        crate::ast::ModItem::Val { init, .. } => self.free(init, &inner, acc),
                        crate::ast::ModItem::Rec(group) => {
                            for (_, _, init) in &group {
                                self.free(*init, &inner, acc);
                            }
                        }
                    }
                }
            }
            // The module, then the body, the module's values bound in it.
            Exp::With { module, body } => {
                if !bound.contains(&module) {
                    adjoin(acc, module);
                }
                let names = self.c.facts.with_vals.get(&x).cloned().unwrap_or_default();
                self.free(body, &with(bound, &names), acc);
            }
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
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => self.free(body, bound, acc),
            Exp::LetRegion { region, body, .. } => self.free(body, &with(bound, &[self.c.arena.dvar_name(region)]), acc),
            Exp::RLambda { region, lambda } => {
                self.free(lambda, bound, acc);
                self.free(region, bound, acc);
            }
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
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => {}
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
        // A procedure converted to a convention: made, then given to
        // `%fx26-convert` with what it is converted to.
        if let Some(k) = self.c.facts.conversion_code(x) {
            self.exp_as_is(x, e, depth, code, false)?;
            self.int(code, k);
            self.prim(code, "%fx26-convert", 2)?;
            self.done(code, tail);
            return Ok(());
        }
        // A module reshaped (`Checker::reshape`): made, then a product of
        // the values the type wanted has, by position.
        if let Some(at) = self.c.facts.reshaped.get(&x).cloned() {
            self.exp_as_is(x, e, depth, code, false)?;
            self.int(code, 37);
            for i in &at {
                self.op1(code, "slot", Value::fixnum(depth as i64));
                self.field(code, *i as i64 + 2);
            }
            self.prim(code, "%make-frozen", 1 + at.len())?;
            self.unbind(code, depth, 1, false);
            self.done(code, tail);
            return Ok(());
        }
        self.exp_as_is(x, e, depth, code, tail)
    }

    fn exp_as_is(&mut self, x: ExpId, e: &Env, depth: usize, code: &mut Vec<Item>, tail: bool) -> R<()> {
        match self.c.arena.exp_at(x).clone() {
            Exp::Var(n) => {
                match self.where_is(e, n) {
                    Some(l) => self.load(code, l),
                    None if matches!(self.name(n), "nil" | "no-pair") => self.lit(code, Value::NULL),
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
            Exp::Float(x) => {
                let v = self.heap.make_flonum(x);
                self.lit(code, v);
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
                self.lambda(&ps, body, e, depth, code, None, None)?;
                self.done(code, tail);
            }
            Exp::RLambda { region, lambda } => {
                let Exp::Lambda { params, body } = self.c.arena.exp_at(lambda).clone() else { unreachable!("parsed") };
                let ps: Vec<Sym> = params.iter().map(|(n, _)| *n).collect();
                self.lambda(&ps, body, e, depth, code, None, Some(region))?;
                self.done(code, tail);
            }
            // A lambda applied at once, to as many arguments as it has
            // parameters: a `let`, with no closure made and no call.
            Exp::App { fun, args } if let Some((ps, lbody)) = self.applied_lambda(fun, args.len()) => {
                let bindings: Vec<(Sym, ExpId)> = ps.into_iter().zip(args.iter().copied()).collect();
                self.let_(&bindings, lbody, e, depth, code, tail)?;
            }
            Exp::App { fun, args } => self.app(x, fun, &args, e, depth, code, tail)?,
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => {
                self.exp(body, e, depth, code, tail)?
            }
            // The region's name bound in a slot, as a `let`'s, to a region
            // entered (an arena, or a reap), and left with the body's value,
            // which is so not in tail position.
            Exp::LetRegion { form, region, body } => {
                let Some(enter) = form.enter() else {
                    // A region for analysis only: nothing at run time.
                    return self.exp(body, e, depth, code, tail);
                };
                let mut inner = e.clone();
                inner.push((self.c.arena.dvar_name(region), Loc::Slot(depth)));
                self.prim(code, enter, 0)?;
                self.exp(body, &inner, depth + 1, code, false)?;
                self.prim(code, "%region-exit", 2)?;
                self.done(code, tail);
            }
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
            Exp::Let { bindings, body } => self.let_(&bindings, body, e, depth, code, tail)?,
            Exp::Letrec { bindings, body } if self.lift(x, &bindings, body, e, tail)?.is_some() => {
                let ks = self.lift(x, &bindings, body, e, tail)?.expect("lifted");
                let mut inner = e.clone();
                inner.extend(bindings.iter().zip(&ks).map(|((g, _, _), k)| (*g, Loc::Lifted(*k))));
                self.exp(body, &inner, depth, code, tail)?;
            }
            Exp::Letrec { bindings, body } => {
                let inner = self.letrec_group(&bindings, e, depth, code)?;
                let n = bindings.len();
                self.exp(body, &inner, depth + n, code, tail)?;
                self.unbind(code, depth, n, tail);
            }
            // A module: its items made in slots in order, as a `letrec*`'s
            // (`crate::modorder`): a lambda naming an item not made yet
            // captures it once it is made, as a `letrec`'s siblings are
            // (`module_closure`); then the product of its values
            // (`docs/research/first-class-modules.md`).
            Exp::Module(items) => {
                // Only the outermost module of a top-level definition notes
                // its members (`module_members`).
                let mut members = self.module_members.take();
                let lambdas = self.c.module_lambdas(&items);
                let is_lambda = |n: Sym, i: usize| lambdas.iter().any(|(m, _, _, at)| *m == n && *at == i);
                // Each name's slot, in written order.
                let mut slots: Vec<(Sym, usize)> = Vec::new();
                for item in &items {
                    let d = depth + slots.len();
                    match item {
                        crate::ast::ModItem::Desc { .. } => {}
                        crate::ast::ModItem::Abs { up, down, .. } => slots.extend([(*up, d), (*down, d + 1)]),
                        crate::ast::ModItem::Val { name, .. } => slots.push((*name, d)),
                        crate::ast::ModItem::Rec(group) => slots.extend(group.iter().enumerate().map(|(k, (n, _, _))| (*n, d + k))),
                    }
                }
                let (mut inner, mut made, mut vals) = (e.clone(), 0, Vec::new());
                // Closures to finish: (closure's slot, free value, slot it waits for).
                let mut waiting: Vec<(usize, usize, usize)> = Vec::new();
                for (i, item) in items.iter().enumerate() {
                    let made_here: Vec<(Sym, ExpId)> = match item {
                        crate::ast::ModItem::Desc { .. } => Vec::new(),
                        crate::ast::ModItem::Abs { up, down, up_fn, down_fn, .. } => vec![(*up, *up_fn), (*down, *down_fn)],
                        crate::ast::ModItem::Val { name, init, .. } => vec![(*name, *init)],
                        crate::ast::ModItem::Rec(group) => group.iter().map(|(n, _, x)| (*n, *x)).collect(),
                    };
                    for (n, x) in made_here {
                        let d = depth + made;
                        let later: Vec<(Sym, usize)> = slots[made..].to_vec();
                        if is_lambda(n, i) && self.names_any(x, &later) {
                            let ps = self.module_closure(n, x, &inner, &later, d, code)?;
                            waiting.extend(ps.into_iter().map(|(j, s)| (d, j, s)));
                        } else {
                            self.exp(x, &inner, d, code, false)?;
                            // A lambda naming no other member (the checks of
                            // size are where a re-export is seen, as the FX-26
                            // compiler's, whose come later in its files).
                            if matches!(item, crate::ast::ModItem::Val { .. })
                                && let Some(ms) = members.as_mut()
                                && let Some((params, body, None)) = self.lambda_of(x)
                                && self.captured(&params, body, &inner).is_empty()
                            {
                                ms.push((n, self.last_word, params, body));
                            }
                        }
                        inner.push((n, Loc::Slot(d)));
                        if !matches!(item, crate::ast::ModItem::Abs { .. }) {
                            vals.push(d);
                        }
                        made += 1;
                        // Each closure that waited for this one, given it.
                        for (c, j, _) in waiting.iter().filter(|(_, _, s)| *s == d) {
                            self.op1(code, "slot", Value::fixnum(d as i64));
                            self.op1(code, "slot", Value::fixnum(*c as i64));
                            self.int(code, (CLOSURE_FREE0 + j) as i64);
                            self.op(code, "field!");
                        }
                    }
                }
                self.int(code, 37);
                for s in &vals {
                    self.op1(code, "slot", Value::fixnum(*s as i64));
                }
                self.prim(code, "%make-frozen", 1 + vals.len())?;
                self.done(code, tail);
                self.unbind(code, depth, made, tail);
                self.module_members = members;
            }
            // `with`: the module's values, by position, in slots.
            Exp::With { module, body } => {
                let names = self.c.facts.with_vals.get(&x).cloned().ok_or("a `with` the checker did not see")?;
                let m = self.where_is(e, module).ok_or("a `with` of an unbound module")?;
                let mut inner = e.clone();
                for (i, n) in names.iter().enumerate() {
                    self.load(code, m);
                    self.field(code, i as i64 + 2);
                    inner.push((*n, Loc::Slot(depth + i)));
                }
                self.exp(body, &inner, depth + names.len(), code, tail)?;
                self.unbind(code, depth, names.len(), tail);
            }
            Exp::Begin(items) => self.begin(&items, e, depth, code, tail)?,
            Exp::Prompt { tag, body, handler } => {
                self.exp(tag, e, depth, code, false)?;
                self.exp(handler, e, depth + 1, code, false)?;
                self.lambda(&[], body, e, depth + 2, code, None, None)?;
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
                self.field(code, i as i64 + 2);
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

    /// A lambda: its free values pushed, then its word closed over them;
    /// or, with a `region` (an `rlambda`'s), that region first, and the
    /// closure made there by `%region-closure h fv … w`. `own` is the
    /// `letrec` name it is bound to, whose tail calls in its body are loops.
    /// What it gives: for each `letrec` sibling it captured before the
    /// sibling was made, its free value's index and the slot the sibling
    /// will be in.
    #[allow(clippy::too_many_arguments)]
    fn lambda(
        &mut self,
        params: &[Sym],
        body: ExpId,
        e: &Env,
        depth: usize,
        code: &mut Vec<Item>,
        own: Option<Sym>,
        region: Option<ExpId>,
    ) -> R<Vec<(usize, usize)>> {
        if let Some(r) = region {
            self.exp(r, e, depth, code, false)?;
        }
        let (w, fv) = self.lambda_word(params, body, e, own)?;
        self.last_word = w;
        // Each captured value, as the closure will hold it.
        let mut patches = Vec::new();
        for (j, n) in fv.iter().enumerate() {
            match find(e, *n).expect("found") {
                Loc::Slot(i) => self.op1(code, "slot", Value::fixnum(i as i64)),
                Loc::Free(i) => self.op1(code, "free", Value::fixnum(i as i64)),
                Loc::Pending(sibling) => {
                    self.lit(code, Value::FALSE);
                    patches.push((j, sibling));
                }
                Loc::Global(_) | Loc::Loop | Loc::Lifted(_) => return Err("a global is not captured".into()),
            }
        }
        if region.is_some() {
            self.lit(code, w);
            self.prim(code, "%region-closure", fv.len() + 2)?;
        } else {
            self.op1(code, "closure", w);
            code.push(Item::Cell(Value::fixnum(fv.len() as i64)));
        }
        Ok(patches)
    }

    /// A lambda's word, and the names its closure captures, in order; with
    /// its register code as its twin when this compiler makes register code.
    /// The names a closure of a lambda made in `e` captures, in order: its
    /// free names that are locals there, not globals or standard ones, nor
    /// a loop, which is not a value. (A definition's own global, in its
    /// body's names, is still a global.)
    fn captured(&self, params: &[Sym], body: ExpId, e: &Env) -> Vec<Sym> {
        let mut free = Vec::new();
        self.free(body, &params.iter().rev().copied().collect::<Vec<_>>(), &mut free);
        self.with_lifted_names(&mut free, params, e);
        free.into_iter().filter(|n| matches!(find(e, *n), Some(l) if l != Loc::Loop && !matches!(l, Loc::Global(_) | Loc::Lifted(_)))).collect()
    }

    /// `free` with, for each lifted procedure in it, the names its calls
    /// pass (not `params`), after: code that calls one needs them too.
    fn with_lifted_names(&self, free: &mut Vec<Sym>, params: &[Sym], e: &Env) {
        let lifted: Vec<usize> = free.iter().filter_map(|n| match find(e, *n) {
            Some(Loc::Lifted(k)) => Some(k),
            _ => None,
        }).collect();
        for k in lifted {
            for a in &self.lifts[k].added {
                if !free.contains(a) && !params.contains(a) {
                    free.push(*a);
                }
            }
        }
    }

    fn lambda_word(&mut self, params: &[Sym], body: ExpId, e: &Env, own: Option<Sym>) -> R<(Value, Vec<Sym>)> {
        let outer_made = std::mem::take(&mut self.made);
        let made = self.lambda_word_in(params, body, e, own);
        self.made = outer_made;
        let (w, fv) = made?;
        let span = self.c.arena.span_of(body);
        let own = own.filter(|f| !params.contains(f));
        self.made.push(Made { span: (span.start, span.end), params: params.to_vec(), own, word: w, fv: fv.clone() });
        Ok((w, fv))
    }

    /// The word the stack code of the body being compiled made for this
    /// lambda, if it made one here.
    fn made_word(&self, params: &[Sym], body: ExpId, e: &Env, own: Option<Sym>) -> Option<(Value, Vec<Sym>)> {
        let span = self.c.arena.span_of(body);
        let fv = self.captured(params, body, e);
        let own = own.filter(|f| !params.contains(f));
        self.reuse
            .iter()
            .find(|m| m.span == (span.start, span.end) && m.params == params && m.own == own && m.fv == fv)
            .map(|m| (m.word, fv))
    }

    fn lambda_word_in(&mut self, params: &[Sym], body: ExpId, e: &Env, own: Option<Sym>) -> R<(Value, Vec<Sym>)> {
        let named = self.word_name.take();
        let bound = self.bind_name.take();
        // Named for the definition it is in, and the name it is bound to
        // there (`letrec`'s or `let`'s), or `lambda`: `k-check/walk`. Its
        // inner lambdas are named within it.
        let base = named.clone().unwrap_or_else(|| {
            let inner = own.or(bound).map_or("lambda", |f| self.c.interner.name(f));
            self.scope_name.as_ref().map_or_else(|| inner.to_string(), |s| format!("{s}/{inner}"))
        });
        let outer_scope = self.scope_name.replace(base.clone());
        let r = self.lambda_word_named(params, body, e, own, named, base);
        self.scope_name = outer_scope;
        r
    }

    fn lambda_word_named(&mut self, params: &[Sym], body: ExpId, e: &Env, own: Option<Sym>, named: Option<String>, base: String) -> R<(Value, Vec<Sym>)> {
        let defining = self.defining.take();
        let fv = self.captured(params, body, e);
        // A parameter of the same name hides the procedure.
        let own = own.filter(|f| !params.contains(f));
        let added = std::mem::take(&mut self.lifting_added);
        // Lifted procedures are known everywhere inside: they are constants.
        let mut inner: Env = e.iter().filter(|(_, l)| matches!(l, Loc::Lifted(_))).copied().collect();
        // A `letrec`-bound procedure's own name: a loop, where it is only
        // called so. (A top-level definition's own name is its global, as
        // any use of it is: a redefinition may change what it holds.)
        if let Some(f) = own.filter(|f| !fv.contains(f)) {
            inner.push((f, Loc::Loop));
        }
        inner.extend(params.iter().enumerate().map(|(i, p)| (*p, Loc::Slot(i))));
        inner.extend(fv.iter().enumerate().map(|(i, n)| (*n, Loc::Free(i))));
        let this = match own {
            Some(f) => Some(This { name: f, loc: find(&inner, f).expect("bound"), params: params.len(), start: self.fresh(), added }),
            None => None,
        };
        let mut body_code = Vec::new();
        if let Some(t) = this {
            body_code.push(Item::Label(t.start));
        }
        let outer = std::mem::replace(&mut self.this, this);
        let compiled = self.exp(body, &inner, params.len(), &mut body_code, true);
        self.this = outer;
        compiled?;
        // Unless a global's, named for where its body starts too, so that a
        // profile can say which. (A body read from another file, a
        // module's, `load-module`: named for that file and where in it.)
        let span = self.c.arena.span_of(body);
        let start = self.char_at.get(span.start as usize).copied().filter(|_| span.file.0 == 0).unwrap_or(u32::MAX);
        let name = named.unwrap_or_else(|| match self.char_at.get(span.start as usize) {
            Some(start) if span.file.0 == 0 => format!("{base}@{start}"),
            _ => format!("{base}@{}:{}", span.file.0, self.loaded_char_at(span)),
        });
        let w = self.assemble(&body_code, &name)?;
        // For bisecting a fault: with `FIXPT_REG_RANGE=lo-hi,…`, only the
        // lambdas whose bodies start in those character ranges get register
        // code.
        let in_range = std::env::var("FIXPT_REG_RANGE").ok().map(|r| {
            r.split(',').any(|part| {
                part.split_once('-')
                    .and_then(|(lo, hi)| Some((lo.parse::<u32>().ok()?..hi.parse::<u32>().ok()?).contains(&start)))
                    .unwrap_or(false)
            })
        });
        if self.registers && in_range != Some(false) {
            self.declined = None;
            let outer_reuse = std::mem::replace(&mut self.reuse, std::mem::take(&mut self.made));
            let cells = self.register_code(params, body, &inner, this, defining.map(|n| (n, w)));
            self.reuse = outer_reuse;
            match cells {
                Some(cells) => {
                    let sym = self.heap.intern(&name);
                    let twin = self.heap.make_register_word(sym, w, &cells).map_err(|e| format!("register code for {name}: {e}"))?;
                    self.heap.set_bloblet_slot(w, WORD_TWIN, twin);
                    self.register_report.push((name, None));
                }
                None => {
                    let why = self.declined.take().unwrap_or_else(|| "?".into());
                    self.register_report.push((name, Some(why)));
                }
            }
        }
        Ok((w, fv))
    }

    // ------------------------------------------------- known procedures

    /// The parameters and body of `x`, when it is a lambda under any type
    /// abstractions, ascriptions and conversions, which compile to nothing; and its
    /// region, when it is an `rlambda`.
    /// Where `span` starts in its module's file (`load-module`), in
    /// characters, as the FX-26 compiler places it; in bytes if the file is
    /// not one the checker read.
    fn loaded_char_at(&self, span: fixpt_read::Span) -> u32 {
        let text = self.c.loaded.values().find(|(_, _, f)| *f == span.file).map(|(_, t, _)| t.as_str());
        match text {
            Some(t) => t[..(span.start as usize).min(t.len())].chars().count() as u32,
            None => span.start,
        }
    }

    /// `(define name (with m f))`, `m` a top-level module whose member `f`
    /// is small and names no other member: `name` inlined where called as
    /// `f` is, behind the same guard, the global holding `f`'s closure
    /// (`TODO.md` §38). Members that name others are called.
    fn reexport_inline(&mut self, name: Sym, exp: ExpId) {
        let Exp::With { module, body } = *self.c.arena.exp_at(exp) else { return };
        let Exp::Var(f) = *self.c.arena.exp_at(body) else { return };
        let Some((_, genv_len, ms)) = self.modules.iter().find(|(m, _, _)| *m == module) else { return };
        let Some((_, word, params, body)) = ms.iter().find(|(n, _, _, _)| *n == f) else { return };
        let (word, params, body, genv_len) = (*word, params.clone(), *body, *genv_len);
        let stays = self.c.interner.get("stay-cellular").is_some_and(|s| self.mentions(body, s));
        if !stays && self.inline_room(body, INLINE_LIMIT) >= 0 && !self.mentions(body, f) {
            self.inlines.push(Inline { name, word, params, body, genv_len });
        }
    }

    /// The next lambda's word named for global `name`, whose definition it
    /// is, rather than for where its body starts: so that a profile, a
    /// disassembly or a fault says which procedure (`fixpt_native::symbols`).
    fn name_word_for(&mut self, name: Sym) {
        self.word_name = Some(self.c.interner.name(name).to_string());
    }

    fn lambda_of(&self, mut x: ExpId) -> Option<(Vec<Sym>, ExpId, Option<ExpId>)> {
        let mut region = None;
        loop {
            match self.c.arena.exp_at(x) {
                Exp::PLambda { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => x = *body,
                Exp::RLambda { region: r, lambda } => {
                    region = Some(*r);
                    x = *lambda;
                }
                Exp::Lambda { params, body } => return Some((params.iter().map(|(n, _)| *n).collect(), *body, region)),
                _ => return None,
            }
        }
    }

    fn mentions(&self, x: ExpId, n: Sym) -> bool {
        let mut acc = Vec::new();
        self.free(x, &[], &mut acc);
        acc.contains(&n)
    }

    /// How many of `n` parser-tree nodes are left once `x`'s are counted,
    /// as `compile.fx`'s `c-inline-room` counts them: negative, and counted
    /// no further, once they run out, or at a form that makes a closure,
    /// which an inlined body would have to capture its slots in.
    fn inline_room(&self, x: ExpId, n: i64) -> i64 {
        let n = n - 1;
        if n < 0 {
            return n;
        }
        let all = |xs: &[ExpId], n: i64| xs.iter().fold(n, |n, a| if n < 0 { n } else { self.inline_room(*a, n) });
        match self.c.arena.exp_at(x).clone() {
            Exp::Lambda { .. } | Exp::RLambda { .. } | Exp::Letrec { .. } | Exp::Prompt { .. } | Exp::Module(_) | Exp::With { .. } => -1,
            Exp::App { fun, args } => all(&args, self.inline_room(fun, n)),
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => self.inline_room(body, n),
            Exp::LetRegion { body, .. } => self.inline_room(body, n),
            Exp::If { test, then, els } => all(&[then, els], self.inline_room(test, n)),
            Exp::Let { bindings, body } => all(&[body], all(&bindings.iter().map(|(_, i)| *i).collect::<Vec<_>>(), n)),
            Exp::Begin(items) => all(&items, n),
            Exp::Bloblet { args, .. } => all(&args, n),
            Exp::Product(fields) => all(&fields.iter().map(|(_, x)| *x).collect::<Vec<_>>(), n),
            Exp::Extract(x, _) | Exp::Sum(_, x) => self.inline_room(x, n),
            Exp::TagCase { scrutinee, arms, els } => {
                let n = all(&arms.iter().map(|a| a.body).collect::<Vec<_>>(), self.inline_room(scrutinee, n));
                all(&els.map(|(_, b)| b).into_iter().collect::<Vec<_>>(), n)
            }
            Exp::Var(_) | Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => n,
        }
    }

    /// Whether `p` is, in `x`, only called, or passed as itself as argument
    /// `k` of `n` to a call of `f`; nothing binding either name again. The
    /// arity it is called with (every call the same), or none.
    fn call_only(&self, x: ExpId, p: Sym, f: Sym, k: usize, n: usize, arity: &mut Option<usize>) -> bool {
        let all = |xs: &[ExpId], arity: &mut Option<usize>| xs.iter().all(|a| self.call_only(*a, p, f, k, n, arity));
        match self.c.arena.exp_at(x).clone() {
            // Not compiled yet (M3): said of no module.
            Exp::Module(_) | Exp::With { .. } => false,
            Exp::Var(m) => m != p,
            Exp::App { fun, args } => match *self.c.arena.exp_at(fun) {
                Exp::Var(m) if m == p => {
                    let same = arity.is_none_or(|a| a == args.len());
                    *arity = Some(args.len());
                    same && all(&args, arity)
                }
                Exp::Var(m) if m == f && args.len() == n && matches!(*self.c.arena.exp_at(args[k]), Exp::Var(q) if q == p) => {
                    args.iter().enumerate().all(|(i, a)| i == k || self.call_only(*a, p, f, k, n, arity))
                }
                _ => self.call_only(fun, p, f, k, n, arity) && all(&args, arity),
            },
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => {
                self.call_only(body, p, f, k, n, arity)
            }
            Exp::LetRegion { region, body, .. } => {
                let r = self.c.arena.dvar_name(region);
                r != p && r != f && self.call_only(body, p, f, k, n, arity)
            }
            Exp::If { test, then, els } => all(&[test, then, els], arity),
            Exp::Let { bindings, body } => {
                bindings.iter().all(|(m, i)| *m != p && *m != f && self.call_only(*i, p, f, k, n, arity)) && self.call_only(body, p, f, k, n, arity)
            }
            Exp::Begin(items) => all(&items, arity),
            Exp::Bloblet { args, .. } => all(&args, arity),
            Exp::Product(fields) => fields.iter().all(|(_, x)| self.call_only(*x, p, f, k, n, arity)),
            Exp::Extract(x, _) | Exp::Sum(_, x) => self.call_only(x, p, f, k, n, arity),
            Exp::TagCase { scrutinee, arms, els } => {
                self.call_only(scrutinee, p, f, k, n, arity)
                    && arms.iter().all(|a| !a.names().iter().any(|m| *m == p || *m == f) && self.call_only(a.body, p, f, k, n, arity))
                    && els.is_none_or(|(y, b)| y != p && y != f && self.call_only(b, p, f, k, n, arity))
            }
            Exp::Lambda { .. } | Exp::RLambda { .. } | Exp::Letrec { .. } | Exp::Prompt { .. } => false,
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => true,
        }
    }

    /// Whether every use of `f` in `x` is a call with `n` arguments, in
    /// any position and in lambdas inside too: so it is never a value.
    fn called_only(&self, x: ExpId, f: Sym, n: usize) -> bool {
        let all = |xs: &[ExpId]| xs.iter().all(|a| self.called_only(*a, f, n));
        match self.c.arena.exp_at(x).clone() {
            // Not compiled yet (M3): said of no module.
            Exp::Module(_) | Exp::With { .. } => false,
            Exp::Var(m) => m != f,
            Exp::App { fun, args } => {
                all(&args)
                    && match self.c.arena.exp_at(fun) {
                        Exp::Var(m) if *m == f => args.len() == n,
                        _ => self.called_only(fun, f, n),
                    }
            }
            Exp::Lambda { params, body } => params.iter().any(|(p, _)| *p == f) || self.called_only(body, f, n),
            Exp::RLambda { region, lambda } => all(&[region, lambda]),
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => self.called_only(body, f, n),
            Exp::LetRegion { region, body, .. } => self.c.arena.dvar_name(region) == f || self.called_only(body, f, n),
            Exp::If { test, then, els } => all(&[test, then, els]),
            Exp::Letrec { bindings, body } => {
                bindings.iter().any(|(m, _, _)| *m == f)
                    || (bindings.iter().all(|(_, _, i)| self.called_only(*i, f, n)) && self.called_only(body, f, n))
            }
            Exp::Let { bindings, body } => {
                bindings.iter().all(|(_, i)| self.called_only(*i, f, n)) && (bindings.iter().any(|(m, _)| *m == f) || self.called_only(body, f, n))
            }
            Exp::Begin(items) => all(&items),
            Exp::Prompt { tag, body, handler } => all(&[tag, body, handler]),
            Exp::Bloblet { args, .. } => all(&args),
            Exp::Product(fields) => fields.iter().all(|(_, x)| self.called_only(*x, f, n)),
            Exp::Extract(x, _) | Exp::Sum(_, x) => self.called_only(x, f, n),
            Exp::TagCase { scrutinee, arms, els } => {
                self.called_only(scrutinee, f, n)
                    && arms.iter().all(|a| a.names().contains(&f) || self.called_only(a.body, f, n))
                    && els.is_none_or(|(y, b)| y == f || self.called_only(b, f, n))
            }
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => true,
        }
    }

    /// Whether the `letrec` `x` (these `bindings` and `body`, in `e`) is
    /// lambda-lifted, deciding the first time it is asked (by its stack
    /// code: its register code asks again, and has the same answer and
    /// words): its members' `lifts` if so, each member's word made, with
    /// the names it takes first.
    fn lift(&mut self, x: ExpId, bindings: &[(Sym, crate::ast::TyId, ExpId)], body: ExpId, e: &Env, tail: bool) -> R<Option<Vec<usize>>> {
        let span = self.c.arena.span_of(x);
        let key = (span.start, span.end);
        if let Some(done) = self.lifted.get(&key) {
            return Ok(done.clone());
        }
        let Some((lams, added)) = self.lift_plan(bindings, body, e, tail) else {
            self.lifted.insert(key, None);
            return Ok(None);
        };
        // Each closure first, over nothing, its word to come: members call
        // each other.
        let mut ks = Vec::new();
        for a in &added {
            let closure = self.heap.closure_over_nothing();
            self.lifts.push(Lift { closure, added: a.clone() });
            ks.push(self.lifts.len() - 1);
        }
        self.lifted.insert(key, Some(ks.clone()));
        let mut known: Env = e.iter().filter(|(_, l)| matches!(l, Loc::Lifted(_))).copied().collect();
        known.extend(bindings.iter().zip(&ks).map(|((g, _, _), k)| (*g, Loc::Lifted(*k))));
        for (i, (name, _, _)) in bindings.iter().enumerate() {
            let (ps, lbody) = &lams[i];
            let mut all = added[i].clone();
            all.extend(ps.iter().copied());
            // Its own calls in tail position are loops, as a closure's are.
            let own = self.loops_only(*lbody, *name, ps.len(), true).then_some(*name);
            self.lifting_added = added[i].len();
            let (w, fv) = self.lambda_word(&all, *lbody, &known, own)?;
            if !fv.is_empty() {
                return Err(format!("a lifted procedure captures {} name(s)", fv.len()));
            }
            self.heap.set_bloblet_slot(self.lifts[ks[i]].closure, fixpt_heap::layout::cellular::CLOSURE_WORD, w);
        }
        Ok(Some(ks))
    }

    /// Whether to lift a `letrec` (`lift`), and if so each member's
    /// parameters and body, and the names it takes before them. Lifted
    /// where every member is a plain lambda only ever called, with its
    /// arity; where the group is not join points (register code's jumps,
    /// better still); and where each member takes fewer than 6 names more
    /// (Twobit's bound, `POLICY:LIFT?`) and no more than `REGS` arguments
    /// in all. The names a member takes: the locals it would capture, and
    /// those of each sibling it calls (Twobit's flow equations,
    /// `compute-added-arguments`); outermost first.
    #[allow(clippy::type_complexity)]
    fn lift_plan(&self, bindings: &[(Sym, crate::ast::TyId, ExpId)], body: ExpId, e: &Env, tail: bool) -> Option<(Vec<(Vec<Sym>, ExpId)>, Vec<Vec<Sym>>)> {
        if tail && (0..bindings.len()).all(|i| self.r_join_ok(bindings, body, i)) {
            return None;
        }
        let mut lams = Vec::new();
        for (_, _, init) in bindings {
            let (ps, lbody, region) = self.lambda_of(*init)?;
            if region.is_some() {
                return None;
            }
            lams.push((ps, lbody));
        }
        for (k, (name, _, _)) in bindings.iter().enumerate() {
            let n = lams[k].0.len();
            if !self.called_only(body, *name, n) || !bindings.iter().all(|(_, _, i)| self.called_only(*i, *name, n)) {
                return None;
            }
        }
        let names: Vec<Sym> = bindings.iter().map(|(n, _, _)| *n).collect();
        let (mut added, mut calls) = (Vec::new(), Vec::new());
        for (ps, lbody) in &lams {
            let mut free = Vec::new();
            self.free(*lbody, &ps.iter().rev().copied().collect::<Vec<_>>(), &mut free);
            self.with_lifted_names(&mut free, ps, e);
            let (mut mine, mut cs) = (Vec::new(), Vec::new());
            for n in free {
                if let Some(k) = names.iter().position(|m| *m == n) {
                    cs.push(k);
                    continue;
                }
                match find(e, n) {
                    Some(Loc::Slot(_) | Loc::Free(_)) => mine.push(n),
                    Some(Loc::Pending(_) | Loc::Loop) => return None,
                    _ => {}
                }
            }
            added.push(mine);
            calls.push(cs);
        }
        loop {
            let mut more = false;
            for i in 0..added.len() {
                for j in calls[i].clone() {
                    for v in added[j].clone() {
                        if !added[i].contains(&v) {
                            added[i].push(v);
                            more = true;
                        }
                    }
                }
            }
            if !more {
                break;
            }
        }
        let at = |n: &Sym| e.iter().rposition(|(m, _)| m == n);
        for a in &mut added {
            a.sort_by_key(at);
        }
        let regs = fixpt_heap::layout::regcode::REGS;
        if added.iter().zip(&lams).any(|(a, (ps, _))| a.len() >= 6 || a.len() + ps.len() > regs) {
            return None;
        }
        Some((lams, added))
    }

    /// Whether every use of `f` in `x` is a call with `n` arguments in tail
    /// position, which the compiler makes a loop.
    fn loops_only(&self, x: ExpId, f: Sym, n: usize, tail: bool) -> bool {
        let all = |xs: &[ExpId]| xs.iter().all(|a| self.loops_only(*a, f, n, false));
        match self.c.arena.exp_at(x).clone() {
            // Not compiled yet (M3): said of no module.
            Exp::Module(_) | Exp::With { .. } => false,
            Exp::Var(m) => m != f,
            Exp::Lambda { params, body } => params.iter().any(|(p, _)| *p == f) || !self.mentions(body, f),
            Exp::App { fun, args } => {
                all(&args)
                    && match self.c.arena.exp_at(fun) {
                        Exp::Var(m) if *m == f => tail && args.len() == n,
                        _ => self.loops_only(fun, f, n, false),
                    }
            }
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => self.loops_only(body, f, n, tail),
            Exp::LetRegion { region, body, .. } => self.c.arena.dvar_name(region) == f || self.loops_only(body, f, n, false),
            Exp::RLambda { region, lambda } => self.loops_only(region, f, n, false) && self.loops_only(lambda, f, n, false),
            Exp::If { test, then, els } => {
                self.loops_only(test, f, n, false) && self.loops_only(then, f, n, tail) && self.loops_only(els, f, n, tail)
            }
            Exp::Letrec { bindings, body } => {
                bindings.iter().any(|(m, _, _)| *m == f)
                    || (bindings.iter().all(|(_, _, i)| self.loops_only(*i, f, n, false)) && self.loops_only(body, f, n, tail))
            }
            Exp::Let { bindings, body } => {
                bindings.iter().all(|(_, i)| self.loops_only(*i, f, n, false))
                    && (bindings.iter().any(|(m, _)| *m == f) || self.loops_only(body, f, n, tail))
            }
            Exp::Begin(items) => match items.split_last() {
                Some((last, rest)) => all(rest) && self.loops_only(*last, f, n, tail),
                None => true,
            },
            Exp::Prompt { tag, body, handler } => all(&[tag, handler]) && !self.mentions(body, f),
            Exp::Bloblet { args, .. } => all(&args),
            Exp::Product(fields) => fields.iter().all(|(_, x)| self.loops_only(*x, f, n, false)),
            Exp::Extract(x, _) | Exp::Sum(_, x) => self.loops_only(x, f, n, false),
            Exp::TagCase { scrutinee, arms, els } => {
                self.loops_only(scrutinee, f, n, false)
                    && arms.iter().all(|a| a.names().contains(&f) || self.loops_only(a.body, f, n, tail))
                    && els.is_none_or(|(y, b)| y == f || self.loops_only(b, f, n, tail))
            }
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => true,
        }
    }

    // ---------------------------------------------------- applications

    /// A `let`: each value pushed, in the scope outside; the names are the
    /// slots.
    /// A `letrec`'s group, its closures made in slots from `depth`: the
    /// environment with them bound. Every binding is a lambda (the checker
    /// says so). Each closure is made in its slot, with a placeholder for a
    /// sibling not made yet; then each placeholder is patched with its
    /// sibling. Nothing runs in between, so no one sees the knot tied. A
    /// name used only in calls of itself that are loops is not captured at
    /// all.
    fn letrec_group(&mut self, bindings: &[(Sym, TyId, ExpId)], e: &Env, depth: usize, code: &mut Vec<Item>) -> R<Env> {
        let mut patches = Vec::new();
        for (i, (name, _, init)) in bindings.iter().enumerate() {
            let (ps, lbody, region) = self.lambda_of(*init).ok_or("a letrec binds only lambdas")?;
            let mut own = e.clone();
            for (k, (g, _, _)) in bindings.iter().enumerate() {
                let loops = k == i && self.loops_only(lbody, *g, ps.len(), true);
                own.push((*g, if loops { Loc::Loop } else { Loc::Pending(depth + k) }));
            }
            patches.push(self.lambda(&ps, lbody, &own, depth + i, code, Some(*name), region)?);
        }
        for (i, ps) in patches.iter().enumerate() {
            for &(j, sibling) in ps {
                self.op1(code, "slot", Value::fixnum(sibling as i64));
                self.op1(code, "slot", Value::fixnum((depth + i) as i64));
                self.int(code, (CLOSURE_FREE0 + j) as i64);
                self.op(code, "field!");
            }
        }
        let mut inner = e.clone();
        inner.extend(bindings.iter().enumerate().map(|(k, (g, _, _))| (*g, Loc::Slot(depth + k))));
        Ok(inner)
    }

    /// Whether `x` names any of `later` (a module's items not made yet).
    pub(crate) fn names_any(&self, x: ExpId, later: &[(Sym, usize)]) -> bool {
        let mut free = Vec::new();
        self.free(x, &[], &mut free);
        free.iter().any(|m| later.iter().any(|(l, _)| l == m))
    }

    /// Module item `n`'s lambda `x`, made at `depth` in `e`, naming items
    /// of `later` (with their slots), not made yet, itself among them: those
    /// captured as a `letrec`'s siblings are, to be given once made. What
    /// it gives: as `lambda`'s.
    fn module_closure(&mut self, n: Sym, x: ExpId, e: &Env, later: &[(Sym, usize)], depth: usize, code: &mut Vec<Item>) -> R<Vec<(usize, usize)>> {
        let (ps, lbody, region) = self.lambda_of(x).ok_or("a module's typed lambda is a lambda")?;
        let mut own = e.clone();
        for (m, s) in later {
            let loops = *m == n && self.loops_only(lbody, n, ps.len(), true);
            own.push((*m, if loops { Loc::Loop } else { Loc::Pending(*s) }));
        }
        self.lambda(&ps, lbody, &own, depth, code, Some(n), region)
    }

    fn let_(&mut self, bindings: &[(Sym, ExpId)], body: ExpId, e: &Env, depth: usize, code: &mut Vec<Item>, tail: bool) -> R<()> {
        let mut inner = e.clone();
        for (i, (n, init)) in bindings.iter().enumerate() {
            self.bind_name = Some(*n);
            let r = self.exp(*init, e, depth + i, code, false);
            self.bind_name = None;
            r?;
            inner.push((*n, Loc::Slot(depth + i)));
        }
        let n = bindings.len();
        self.exp(body, &inner, depth + n, code, tail)?;
        self.unbind(code, depth, n, tail);
        Ok(())
    }

    /// The parameters and body of `f`, when it is a plain lambda (under
    /// forms that compile to nothing) of `n` parameters: applied to `n`
    /// arguments, it is a `let` of them.
    pub(crate) fn applied_lambda(&self, f: ExpId, n: usize) -> Option<(Vec<Sym>, ExpId)> {
        match self.lambda_of(f)? {
            (ps, body, None) if ps.len() == n => Some((ps, body)),
            _ => None,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn app(&mut self, x: ExpId, f: ExpId, args: &[ExpId], e: &Env, depth: usize, code: &mut Vec<Item>, tail: bool) -> R<()> {
        if let (true, Some(t), Exp::Var(n)) = (tail, self.this, self.c.arena.exp_at(f)) {
            if *n == t.name && find(e, *n) == Some(t.loc) && t.added + args.len() == t.params {
                // A loop: the arguments into the parameters' slots (those a
                // lifting added passed on as they are), the rest of the
                // frame dropped, and back to the start.
                self.exps(args, e, depth, code)?;
                for i in (t.added..t.params).rev() {
                    self.op1(code, "slot!", Value::fixnum(i as i64));
                }
                for _ in t.params..depth {
                    self.op(code, "drop");
                }
                code.push(Item::Branch(t.start));
                return Ok(());
            }
        }
        // A lifted procedure's call: the names it would have captured, then
        // the arguments, then its closure.
        if let Exp::Var(n) = *self.c.arena.exp_at(f)
            && let Some(Loc::Lifted(k)) = self.where_is(e, n)
        {
            let added = self.lifts[k].added.clone();
            for a in &added {
                let l = self.where_is(e, *a).ok_or("a lifted procedure's added name is not bound")?;
                self.load(code, l);
            }
            let n = self.exps(args, e, depth + added.len(), code)?;
            self.op1(code, "lit", self.lifts[k].closure);
            self.op1(code, if tail { "ttailcall" } else { "tcall" }, Value::fixnum((added.len() + n) as i64));
            return Ok(());
        }
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
            // `apply` copies its list, unless the checker found it at
            // `acyclic` (`apply_shares`): the variadic procedure's rest list
            // must be one nothing else can write.
            Some(s) if s == "apply" && !self.c.facts.apply_shares.contains(&x) => {
                self.exps(args, e, depth, code)?;
                self.prim(code, "%fx26-list-copy", 1)?;
                self.standard_on("apply", 2, code)?;
                self.done(code, tail);
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
            | "set" | "char=?" | "string-append" | "string=?" | "symbol=?" | "wglobal=?" | "eq?" | "bool=?" | "array-ref" | "string-ref" | "make-array"
            | "abort-current-continuation" | "call-with-composable-continuation" | "first-mark" | "marks-of" => Some(2),
            // The rest: the arity of the runtime primitive it runs as, if
            // that takes a fixed number (`char-downcase`).
            _ => standard_primitive(n).filter(|p| *p != "%fx26-identity").and_then(|p| {
                let d = &fixpt_runtime::PRIMITIVES[fixpt_engine::cellular::runtime_primitive(p)?];
                (d.max == Some(d.min)).then_some(d.min)
            }),
        }
    }

    /// Whether a standard name has a value: an operation of an arity, or
    /// `list`, a `vsubr`.
    pub(crate) fn has_standard_value(name: &str) -> bool {
        name == "list" || Self::arity(name).is_some()
    }

    /// A standard operation as a value: a closure of its arity whose body
    /// applies it to its parameters. `list` is a `vsubr`: `%vlambda`'s
    /// closure over a procedure of one list that copies it, as `datum-list`
    /// does (and its register code is `datum-list`'s). A copy, not the list
    /// itself: `apply` gives a list at `acyclic` as it is (F11), and `list`
    /// may give it at any region, one that can be written.
    fn standard_value(&mut self, name: &str, code: &mut Vec<Item>) -> R<()> {
        if name == "list" {
            let mut body = Vec::new();
            self.op1(&mut body, "slot", Value::fixnum(0));
            self.standard_on("datum-list", 1, &mut body)?;
            self.op(&mut body, "return");
            let w = self.assemble(&body, name)?;
            self.register_twin(w, name, "datum-list", 1)?;
            self.op1(code, "closure", w);
            code.push(Item::Cell(Value::fixnum(0)));
            return self.prim(code, "%fx26-vlambda", 1);
        }
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
        self.register_twin(w, name, name, n)?;
        self.op1(code, "closure", w);
        code.push(Item::Cell(Value::fixnum(0)));
        Ok(())
    }

    /// Register code for word `w`, named `name`, as standard operation `op`
    /// of `n` arguments has it as a value, for the native compiler to start
    /// from.
    fn register_twin(&mut self, w: Value, name: &str, op: &str, n: usize) -> R<()> {
        if self.registers
            && let Some(cells) = self.r_standard_word(op, n)
        {
            let sym = self.heap.intern(name);
            let twin = self.heap.make_register_word(sym, w, &cells).map_err(|e| format!("register code for {name}: {e}"))?;
            self.heap.set_bloblet_slot(w, WORD_TWIN, twin);
        }
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
            // Typed routines: the checker has proved the operands' types.
            "+" => self.op(code, "int-add"),
            "-" => self.op(code, "int-sub"),
            "<" => self.op(code, "int-less"),
            ">" => {
                self.op(code, "swap");
                self.op(code, "int-less");
            }
            "<=" => {
                self.op(code, "swap");
                self.op(code, "int-less");
                self.lit(code, f);
                self.op(code, "eq");
            }
            ">=" => {
                self.op(code, "int-less");
                self.lit(code, f);
                self.op(code, "eq");
            }
            // Ints may be bignums, compared by value.
            "=" => self.op(code, "int-eq"),
            "symbol=?" | "wglobal=?" | "char=?" | "eq?" | "bool=?" => self.op(code, "eq"),
            "cons" => self.op(code, "cons"),
            "car" => self.op(code, "pair-car"),
            "cdr" => self.op(code, "pair-cdr"),
            "set-car!" | "set-cdr!" => {
                self.prim(code, name, 2)?;
                self.unit_after(code);
            }
            "new" => self.prim(code, "%make-box", 1)?,
            "get" => self.field(code, 2),
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
                self.op(code, "int-add");
                self.op(code, "field@");
            }
            "array-set!" => {
                self.op(code, "swap");
                self.int(code, 2);
                self.op(code, "int-add");
                self.op(code, "swap");
                self.prim(code, "%bloblet-set!", 3)?;
                self.unit_after(code);
            }
            // `(apply f xs)`: `f` is a `vsubr`, a closure of `%vlambda`'s
            // over the procedure of one list, free value 0; that procedure,
            // called with `xs`.
            "apply" => {
                self.op(code, "swap");
                self.op1(code, "field", Value::fixnum(fixpt_heap::layout::cellular::CLOSURE_FREE0 as i64));
                self.op1(code, "tcall", Value::fixnum(1));
            }
            "array-length" => {
                self.prim(code, "%bloblet-fields", 1)?;
                self.int(code, 1);
                self.op(code, "int-sub");
            }
            "modulo" | "char->integer" | "integer->char" | "string-append" | "string-length"
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
            BlobletOp::RMake => {
                let n = self.exps(args, e, depth, code)?;
                self.prim(code, "%region-make-bloblet", n)?;
            }
            BlobletOp::Ref(i) => {
                self.exps(args, e, depth, code)?;
                self.field(code, i as i64 + 2);
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
        self.field(code, 2);
        let tag = self.heap.intern(self.c.interner.name(arm.tag));
        self.lit(code, tag);
        self.op(code, "eq");
        code.push(Item::ZBranch(next));
        // The value, or its product's members, as slots after the sum.
        self.op1(code, "slot", Value::fixnum(depth as i64));
        self.field(code, 3);
        let mut bound = e.clone();
        let n = match &arm.bind {
            ArmBind::Value(x) => {
                bound.push((*x, Loc::Slot(depth + 1)));
                1
            }
            ArmBind::Fields(xs) => {
                for (j, x) in xs.iter().enumerate() {
                    self.op1(code, "slot", Value::fixnum(depth as i64 + 1));
                    self.field(code, j as i64 + 2);
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
        self.genv_index.entry(n).or_default().push((self.genv.len(), Loc::Global(g)));
        self.genv.push((n, Loc::Global(g)));
        g
    }

    /// The global a definition of `n` sets: the one `n` has, if the
    /// definition assigns it (`Top`'s `assigns`); else a new one.
    fn global_for(&mut self, n: Sym, assigns: bool) -> Value {
        self.inlines.retain(|i| i.name != n);
        self.specials.retain(|i| i.name != n);
        match self.global(n, self.genv.len()) {
            Some(Loc::Global(g)) if assigns => g,
            _ => self.push_global(n),
        }
    }

    /// A checked program's forms, as the checker found them, to one word
    /// that runs it and leaves its last expression's value (unit if none).
    pub fn program(&mut self, tops: &[Top]) -> R<Value> {
        let mut code = Vec::new();
        let mut has_value = false;
        for t in tops {
            match t {
                Top::Define { name, exp, recursive, assigns, .. } => {
                    if has_value {
                        self.op(&mut code, "drop");
                    }
                    // A lambda's global first, so that it can call itself:
                    // through the global, as any use of it does, which holds
                    // whatever the name is defined as when the call is made
                    // (`docs/fx26.md`, "Redefinition"). A procedure that must
                    // call itself binds itself locally, with `letrec`.
                    // A module defined again no longer says what its
                    // re-exports are.
                    self.modules.retain(|(m, _, _)| m != name);
                    let g = if !recursive {
                        let is_module = matches!(self.c.arena.exp_at(*exp), Exp::Module(_));
                        if is_module {
                            self.module_members = Some(Vec::new());
                        }
                        let genv_len = self.genv.len();
                        self.exp(*exp, &Vec::new(), 0, &mut code, false)?;
                        if let (true, Some(ms)) = (is_module, self.module_members.take()) {
                            self.modules.push((*name, genv_len, ms));
                        }
                        let g = self.global_for(*name, *assigns);
                        // After its global, which forgets what the name was.
                        self.reexport_inline(*name, *exp);
                        g
                    } else {
                        let g = self.global_for(*name, *assigns);
                        if let Some((_, _, None)) = self.lambda_of(*exp) {
                            self.defining = Some(*name);
                            self.name_word_for(*name);
                        }
                        self.exp(*exp, &Vec::new(), 0, &mut code, false)?;
                        self.defining = None;
                        // Small enough, and not calling itself: inlined
                        // where it is called. Not one that stays cellular
                        // (`stay-cellular`), which would make its callers so.
                        let stays = |c: &Self, body| c.c.interner.get("stay-cellular").is_some_and(|s| c.mentions(body, s));
                        if let Some((params, body, None)) = self.lambda_of(*exp)
                            && self.inline_room(body, INLINE_LIMIT) >= 0
                            && !self.mentions(body, *name)
                            && !stays(self, body)
                        {
                            let (word, genv_len) = (self.last_word, self.genv.len());
                            self.inlines.push(Inline { name: *name, word, params, body, genv_len });
                        } else if let Some((params, body, None)) = self.lambda_of(*exp)
                            && self.inline_room(body, SPECIAL_LIMIT) >= 0
                            && !stays(self, body)
                        {
                            // Else, with a parameter only called: specialized
                            // where it is called with a lambda there.
                            let n = params.len();
                            let found = (0..n).find_map(|k| {
                                let mut arity = None;
                                (self.call_only(body, params[k], *name, k, n, &mut arity) && arity.is_some()).then(|| (k, arity.unwrap_or(0)))
                            });
                            if let Some((param, arity)) = found {
                                let (word, genv_len) = (self.last_word, self.genv.len());
                                self.specials.push(Special { name: *name, word, params, body, genv_len, param, arity });
                            }
                        }
                        g
                    };
                    self.op1(&mut code, "global!", g);
                    has_value = false;
                }
                // Every name's global first; then each lambda, which runs
                // nothing.
                Top::DefineRec { bindings, assigns } => {
                    if has_value {
                        self.op(&mut code, "drop");
                    }
                    let gs: Vec<Value> = bindings.iter().map(|(n, _, _)| self.global_for(*n, *assigns)).collect();
                    for ((n, _, e), g) in bindings.iter().zip(gs) {
                        if let Some((_, _, None)) = self.lambda_of(*e) {
                            self.name_word_for(*n);
                        }
                        self.exp(*e, &Vec::new(), 0, &mut code, false)?;
                        self.op1(&mut code, "global!", g);
                    }
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
        (*scheme == "%fx26-identity" || fixpt_engine::cellular::runtime_primitive(scheme).is_some()).then_some(*scheme)
    })
}

/// Every routine this compiler emits names one the machine has.
const _: () = assert!(ROUTINES.len() > 38);
