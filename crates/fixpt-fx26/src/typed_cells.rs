//! Typed cellular code (`docs/research/typed-cellular-code.md`): a word's
//! certificate, and a verifier that checks the word's cells against it in
//! one pass, as Hoare logic: each routine a triple, the certificate's
//! assertions at the word's entry, exit and branch targets, and every
//! precondition a verification condition (VC) to discharge.
//!
//! The propositions start with type assertions, `(: t T)`, which the
//! verifier discharges itself, by subtyping (no inference: the certificate
//! gave what inference found). The others (`Prop`'s rest) are the logic's
//! room to grow: a VC the verifier cannot discharge is kept, open, for a
//! prover outside.

use crate::ast::{Effect, Size, Ty, TyId};
use crate::check::Checker;
use fixpt_heap::layout::cellular::{operands, CLOSURE_WORD, GLOBAL_VALUE, PRIMITIVES, ROUTINES, WORD_CELL0};
use fixpt_heap::{Heap, ObjType, Value};
use std::collections::HashMap;

/// A term of the logic: what names a value at a cell boundary. A place
/// (`Slot`, `Free`), a literal, a value the verifier made (`Made`, the
/// result of an operation, named by number), or a function of the logic
/// applied (`(car t)`, `(field 2 t)`, `(eq t u)`): a term never runs.
#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Slot(usize),
    Free(usize),
    Lit(Value),
    Made(u32),
    App(&'static str, Vec<Term>),
}

/// An integer relation.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Rel {
    Lt,
    Le,
    Eq,
}

/// A proposition of the logic. `Has` is the baseline, the only one the
/// compilers' certificates state today; the rest are what assertions
/// beyond types are made of.
#[derive(Clone, Debug, PartialEq)]
pub enum Prop {
    /// `(: t T)`: `t`'s value is of type `T`.
    Has(Term, TyId),
    /// `(eq t u)`: the same value.
    Same(Term, Term),
    /// `(< t u)`, `(<= t u)`, `(= t u)`, of integers.
    Rel(Rel, Term, Term),
    Not(Box<Prop>),
    And(Vec<Prop>),
    Or(Vec<Prop>),
    Implies(Box<Prop>, Box<Prop>),
}

/// A word's certificate: its signature (the types of its parameters, slots
/// `0 …`, and of its free values; its result's and its latent effect, none
/// for a word that ends in `exit`), and assertions before some of its
/// cells, by cell number: at a branch target, what the join rule cannot
/// give.
#[derive(Clone, Debug, Default)]
pub struct Cert {
    /// The binders of a polymorphic value's word (a `plambda`'s): its
    /// types are under them, and a closure over it is of a `poly` type.
    pub poly: Vec<(crate::ast::DVar, crate::ast::Kind)>,
    pub params: Vec<TyId>,
    pub frees: Vec<TyId>,
    pub result: Option<TyId>,
    pub effect: Option<Effect>,
    pub notes: Vec<(usize, Vec<Prop>)>,
    /// The cells that run a standard operation, by cell number: its name,
    /// and what its type's binders are instantiated at (checking found it;
    /// the verifier substitutes, and does not search).
    pub ops: Vec<(usize, String, Vec<crate::ast::D>)>,
}

/// The certificates a compilation made: each word's, and each global cell's
/// type, by the word's or cell's address. Good until the heap collects.
#[derive(Default)]
pub struct Certs {
    pub words: HashMap<u64, Cert>,
    pub globals: HashMap<u64, TyId>,
}

/// What verifying a word found: how many VCs it discharged, those that
/// failed (the word refused), those left open (for a prover outside), the
/// debts (preconditions the machine checks as it runs, failing safely
/// where one does not hold: `car` of a list that may be `nil`, `TODO.md`
/// §86), and, if it stopped, at which routine it has no rule for yet.
#[derive(Debug, Default)]
pub struct Outcome {
    pub discharged: usize,
    pub failed: Vec<String>,
    pub open: Vec<String>,
    pub debts: Vec<String>,
    pub stopped: Option<String>,
}

impl Outcome {
    pub fn verified(&self) -> bool {
        self.failed.is_empty() && self.open.is_empty() && self.stopped.is_none()
    }
}

/// A value on the stack: its term, its type if known, and the type it was
/// made with, which a narrowing does not change and a join falls back to.
#[derive(Clone, Debug, PartialEq)]
struct V {
    term: Term,
    ty: Option<TyId>,
    made: Option<TyId>,
}

impl V {
    fn new(term: Term, ty: Option<TyId>) -> V {
        V { term, ty, made: ty }
    }
}

/// The state at a cell boundary: the data stack above the frame pointer,
/// slot 0 first.
#[derive(Clone, Debug)]
struct State {
    stack: Vec<V>,
}

/// One instruction: where its cell is, its routine's name (or `None`, a
/// word run as a cell), and its operands.
struct Ins {
    at: usize,
    name: Option<&'static str>,
    ops: Vec<Value>,
}

/// Verify `word` against its certificate in `certs`.
pub fn verify(c: &mut Checker, heap: &Heap, certs: &Certs, word: Value) -> Outcome {
    let mut v = Verifier { c, heap, certs, out: Outcome::default(), made: 0, effect: Effect::pure() };
    match certs.words.get(&word.raw()) {
        Some(cert) => v.word(word, cert),
        None => v.out.stopped = Some("no certificate".into()),
    }
    v.out
}

struct Verifier<'a> {
    c: &'a mut Checker,
    heap: &'a Heap,
    certs: &'a Certs,
    out: Outcome,
    made: u32,
    effect: Effect,
}

impl Verifier<'_> {
    fn fresh(&mut self) -> Term {
        self.made += 1;
        Term::Made(self.made)
    }

    fn show(&self, t: TyId) -> String {
        self.c.show_ty(t)
    }

    /// A VC: `v` is of type `t`. A literal is looked at; anything else is
    /// within `t` by subtyping.
    fn holds(&mut self, v: &V, t: TyId, what: &str) {
        if let Term::Lit(x) = v.term
            && self.inhabits(x, t)
        {
            self.out.discharged += 1;
            return;
        }
        // A `poly`'s value, made of a value checked against its body with
        // its binders held abstract (no `plambda`): of the body's type.
        let is_poly = |me: &Self, t: Option<TyId>| t.is_some_and(|t| matches!(me.c.arena.get(me.c.arena.resolve(t)), Ty::Poly { .. }));
        let t = match self.c.arena.get(self.c.arena.resolve(t)).clone() {
            Ty::Poly { body, .. } if !is_poly(self, v.ty) => body,
            _ => t,
        };
        match v.ty {
            Some(s) if self.c.subtype(s, t) => self.out.discharged += 1,
            Some(s) => {
                let msg = format!("{what}: {} is not within {}", self.show(s), self.show(t));
                self.out.failed.push(msg);
            }
            None => self.out.open.push(format!("{what}: (: {:?} {})", v.term, self.show(t))),
        }
    }

    /// Whether literal `x` is of type `t`, by looking at it.
    fn inhabits(&mut self, x: Value, t: TyId) -> bool {
        let t = self.c.arena.resolve(t);
        match self.c.arena.get(t).clone() {
            Ty::Nat(Size::Finite) => x.is_fixnum() && x.as_fixnum() >= 0,
            Ty::Nat(s) => x.is_fixnum() && s.as_lit() == Some(x.as_fixnum()),
            Ty::False => x.is_false(),
            Ty::Nil => x.is_null(),
            Ty::Union(ms) => ms.iter().any(|m| self.inhabits(x, *m)),
            Ty::Pair(a, b, _, nil) => (nil && x.is_null()) || (x.is_pair() && self.inhabits(self.heap.car(x), a) && self.inhabits(self.heap.cdr(x), b)),
            _ if t == self.c.int => x.is_fixnum(),
            _ if t == self.c.string => self.heap.is_a(x, ObjType::String),
            _ if t == self.c.f64_ => self.heap.is_a(x, ObjType::Flonum),
            _ if t == self.c.bool_ => x.is_boolean(),
            _ if t == self.c.char_ => x.is_char(),
            _ if t == self.c.unit => self.symbol_named(x, "#u"),
            _ if t == self.c.symbol => self.heap.is_a(x, ObjType::Symbol),
            _ => false,
        }
    }

    fn symbol_named(&self, x: Value, name: &str) -> bool {
        self.heap.is_a(x, ObjType::Symbol) && self.heap.symbol_name(x) == name
    }

    /// A literal's type, where one is plain from the value.
    fn lit_type(&mut self, x: Value) -> Option<TyId> {
        if x.is_fixnum() && x.as_fixnum() >= 0 {
            Some(self.c.arena.ty(Ty::Nat(Size::lit(x.as_fixnum()))))
        } else if x.is_fixnum() {
            Some(self.c.int)
        } else if x.is_boolean() {
            Some(self.c.bool_)
        } else if x.is_null() {
            Some(self.c.arena.ty(Ty::Nil))
        } else if x.is_char() {
            Some(self.c.char_)
        } else if self.symbol_named(x, "#u") {
            Some(self.c.unit)
        } else if self.heap.is_a(x, ObjType::Symbol) {
            Some(self.c.symbol)
        } else if x.is_bloblet() && self.heap.bloblet_kind(x) == fixpt_heap::layout::kind("cellular-closure") {
            // A closure made while compiling (a lifted procedure's): its
            // word's signature, closed over nothing.
            let w = self.heap.bloblet_slot(x, CLOSURE_WORD);
            let cert = self.certs.words.get(&w.raw())?.clone();
            self.subr_of(&cert)
        } else {
            None
        }
    }

    /// The procedure type a word's signature gives a closure over it.
    fn subr_of(&mut self, cert: &Cert) -> Option<TyId> {
        let (result, effect) = (cert.result?, cert.effect.clone()?);
        let conv = self.c.conv_default;
        let subr = self.c.arena.ty(Ty::Subr { conv, effect, params: cert.params.clone(), result });
        Some(match cert.poly.is_empty() {
            true => subr,
            false => self.c.arena.ty(Ty::Poly { binders: cert.poly.clone(), body: subr }),
        })
    }

    fn decode(&mut self, word: Value) -> Vec<Ins> {
        let n = self.heap.bloblet_head(word).fields;
        let mut out = Vec::new();
        let mut k = WORD_CELL0;
        while k <= n {
            let cell = self.heap.bloblet_slot(word, k);
            let (name, m) = if cell.is_fixnum() && (cell.as_fixnum() as usize) < PRIMITIVES {
                let name = ROUTINES[cell.as_fixnum() as usize].0;
                (Some(name), operands(name))
            } else {
                (None, 0)
            };
            let ops = (1..=m).map(|j| self.heap.bloblet_slot(word, k + j)).collect();
            out.push(Ins { at: k - WORD_CELL0, name, ops });
            k += 1 + m;
        }
        out
    }

    fn word(&mut self, word: Value, cert: &Cert) {
        let code = self.decode(word);
        let entry = State {
            stack: cert.params.iter().enumerate().map(|(i, t)| V::new(Term::Slot(i), Some(*t))).collect(),
        };
        let notes: HashMap<usize, &Vec<Prop>> = cert.notes.iter().map(|(k, p)| (*k, p)).collect();
        // The states waiting at each later cell, from branches to it.
        let mut waiting: HashMap<usize, Vec<State>> = HashMap::new();
        let mut cur = Some(entry.clone());
        for ins in &code {
            let mut arriving: Vec<State> = waiting.remove(&ins.at).unwrap_or_default();
            if let Some(s) = cur.take() {
                arriving.push(s);
            }
            if arriving.is_empty() {
                // Reached by no way: the code after an unconditional branch
                // that nothing branches to. Not run, so not verified.
                continue;
            }
            let at = format!("cell {}", ins.at);
            let mut s = match notes.get(&ins.at) {
                Some(note) => self.assume(&arriving, note, &at),
                None => match self.join(&arriving, &at) {
                    Some(s) => s,
                    None => return,
                },
            };
            let Some(name) = ins.name else {
                self.out.stopped = Some("a word run as a cell".into());
                return;
            };
            match self.step(name, &ins.ops, &mut s, cert, &at, &entry, ins.at, &mut waiting) {
                Ok(Some(next)) => cur = Some(next),
                Ok(None) => {}
                Err(()) => return,
            }
        }
        if cur.is_some() {
            self.out.failed.push("the last cell falls through".into());
        }
        if let Some(latent) = &cert.effect
            && !self.effect.within(latent)
        {
            let msg = format!("effect {} is not within the latent {}", self.c.show_effect(&self.effect), self.c.show_effect(latent));
            self.out.open.push(msg);
        }
    }

    /// The state at a cell the ways in `arriving` reach, joined: each place
    /// keeps a value the ways agree on; one they do not agree on keeps its
    /// term if they share it, at the type it was made with.
    fn join(&mut self, arriving: &[State], at: &str) -> Option<State> {
        let first = &arriving[0];
        if arriving.iter().any(|s| s.stack.len() != first.stack.len()) {
            self.out.failed.push(format!("{at}: the ways in leave the stack at different heights"));
            return None;
        }
        let mut stack = Vec::new();
        for (i, v) in first.stack.iter().enumerate() {
            if arriving.iter().all(|s| s.stack[i] == *v) {
                stack.push(v.clone());
            } else if arriving.iter().all(|s| s.stack[i].term == v.term && s.stack[i].made == v.made) {
                stack.push(V { term: v.term.clone(), ty: v.made, made: v.made });
            } else {
                self.out.failed.push(format!("{at}: slot {i} differs on the ways in, and no assertion says what it is"));
                return None;
            }
        }
        Some(State { stack })
    }

    /// The state at a cell with an assertion: each way in must establish
    /// it (VCs); then the slots it names hold fresh values at the types it
    /// says, and the rest are joined.
    fn assume(&mut self, arriving: &[State], note: &[Prop], at: &str) -> State {
        let mut named: Vec<(usize, TyId)> = Vec::new();
        for p in note {
            match p {
                Prop::Has(Term::Slot(i), t) => named.push((*i, *t)),
                other => self.out.open.push(format!("{at}: an assertion the verifier does not read: {other:?}")),
            }
        }
        for s in arriving {
            for (i, t) in &named {
                match s.stack.get(*i).cloned() {
                    Some(v) => self.holds(&v, *t, at),
                    None => self.out.failed.push(format!("{at}: no slot {i}")),
                }
            }
        }
        // The named slots replaced by what is asserted, so that the ways'
        // values there need not agree.
        let mut ways: Vec<State> = arriving.to_vec();
        for (i, t) in &named {
            let fresh = self.fresh();
            for s in &mut ways {
                if let Some(v) = s.stack.get_mut(*i) {
                    *v = V::new(fresh.clone(), Some(*t));
                }
            }
        }
        self.join(&ways, at).unwrap_or(State { stack: Vec::new() })
    }

    fn pop(&mut self, s: &mut State, at: &str) -> Result<V, ()> {
        s.stack.pop().ok_or_else(|| self.out.failed.push(format!("{at}: the stack is empty")))
    }

    fn push_made(&mut self, s: &mut State, ty: Option<TyId>, term: Option<Term>) {
        let term = term.unwrap_or_else(|| self.fresh());
        s.stack.push(V::new(term, ty));
    }

    /// The resolved type of `v`, if known.
    fn ty_of(&self, v: &V) -> Option<Ty> {
        v.ty.map(|t| self.c.arena.get(self.c.arena.resolve(t)).clone())
    }

    /// The effect of reading region `r`, unless it is frozen.
    fn reads(&mut self, r: crate::ast::Region) {
        if !matches!(r, crate::ast::Region::Frozen(..)) {
            self.effect = self.effect.union(&Effect::atom(crate::ast::Atom::Read(r)));
        }
    }

    /// One instruction's triple, on `s`: the state after it, or none if it
    /// leaves the word or branches away for good.
    #[allow(clippy::too_many_arguments)]
    fn step(&mut self, name: &'static str, ops: &[Value], s: &mut State, cert: &Cert, at: &str, entry: &State, here: usize, waiting: &mut HashMap<usize, Vec<State>>) -> Result<Option<State>, ()> {
        let int = self.c.int;
        let bool_ = self.c.bool_;
        match name {
            "lit" => {
                let ty = self.lit_type(ops[0]);
                s.stack.push(V::new(Term::Lit(ops[0]), ty));
            }
            "slot" => {
                let i = ops[0].as_fixnum() as usize;
                let v = s.stack.get(i).cloned().ok_or_else(|| self.out.failed.push(format!("{at}: no slot {i}")))?;
                s.stack.push(v);
            }
            "slot!" => {
                let i = ops[0].as_fixnum() as usize;
                let v = self.pop(s, at)?;
                match s.stack.get_mut(i) {
                    Some(slot) => *slot = v,
                    None => {
                        self.out.failed.push(format!("{at}: no slot {i}"));
                        return Err(());
                    }
                }
            }
            "drop" => {
                self.pop(s, at)?;
            }
            "dup" => {
                let v = s.stack.last().cloned().ok_or_else(|| self.out.failed.push(format!("{at}: the stack is empty")))?;
                s.stack.push(v);
            }
            "swap" => {
                let (b, a) = (self.pop(s, at)?, self.pop(s, at)?);
                s.stack.push(b);
                s.stack.push(a);
            }
            "over" => {
                let n = s.stack.len();
                if n < 2 {
                    self.out.failed.push(format!("{at}: over, on fewer than two"));
                    return Err(());
                }
                s.stack.push(s.stack[n - 2].clone());
            }
            "free" => {
                let i = ops[0].as_fixnum() as usize;
                let ty = cert.frees.get(i).copied();
                if ty.is_none() {
                    self.out.failed.push(format!("{at}: no free value {i}"));
                    return Err(());
                }
                s.stack.push(V::new(Term::Free(i), ty));
            }
            "global" => {
                let ty = self.certs.globals.get(&ops[0].raw()).copied();
                let term = Term::App("global", vec![Term::Lit(ops[0])]);
                // A global known while compiling to hold a word's closure.
                let ty = ty.or_else(|| {
                    let v = self.heap.bloblet_slot(ops[0], GLOBAL_VALUE);
                    self.lit_type(v)
                });
                s.stack.push(V::new(term, ty));
            }
            "global!" => {
                let v = self.pop(s, at)?;
                match self.certs.globals.get(&ops[0].raw()).copied() {
                    Some(t) => self.holds(&v, t, at),
                    None => self.out.open.push(format!("{at}: a global of no known type written")),
                }
            }
            "int-add" | "int-sub" => {
                let (b, a) = (self.pop(s, at)?, self.pop(s, at)?);
                self.holds(&a, int, at);
                self.holds(&b, int, at);
                let f = if name == "int-add" { "+" } else { "-" };
                // Naturals added are a natural, their sizes added, as the
                // checkers' `+` types them.
                let ty = match (self.ty_of(&a), self.ty_of(&b), name) {
                    (Some(Ty::Nat(x)), Some(Ty::Nat(y)), "int-add") => Some(self.c.arena.ty(Ty::Nat(x.add_scaled(&y, 1)))),
                    _ => Some(int),
                };
                self.push_made(s, ty, Some(Term::App(f, vec![a.term, b.term])));
            }
            "int-less" | "int-eq" => {
                let (b, a) = (self.pop(s, at)?, self.pop(s, at)?);
                self.holds(&a, int, at);
                self.holds(&b, int, at);
                let f = if name == "int-less" { "<" } else { "=" };
                self.push_made(s, Some(bool_), Some(Term::App(f, vec![a.term, b.term])));
            }
            "eq" => {
                let (b, a) = (self.pop(s, at)?, self.pop(s, at)?);
                self.push_made(s, Some(bool_), Some(Term::App("eq", vec![a.term, b.term])));
            }
            "pair-car" | "pair-cdr" => {
                let p = self.pop(s, at)?;
                match self.ty_of(&p) {
                    Some(Ty::Pair(a, b, r, nil)) => {
                        if nil {
                            self.out.debts.push(format!("{at}: (not (eq {:?} nil))", p.term));
                        }
                        self.reads(r);
                        let f = if name == "pair-car" { "car" } else { "cdr" };
                        self.push_made(s, Some(if name == "pair-car" { a } else { b }), Some(Term::App(f, vec![p.term])));
                    }
                    Some(_) => {
                        let msg = format!("{at}: {name} of {}, not a pair", self.show(p.ty.expect("known")));
                        self.out.failed.push(msg);
                        return Err(());
                    }
                    None => {
                        self.out.open.push(format!("{at}: {name} of a value of no known type"));
                        self.push_made(s, None, None);
                    }
                }
            }
            "field" => {
                let k = ops[0].as_fixnum() as usize;
                let o = self.pop(s, at)?;
                let ty = self.field_type(&o, k, at)?;
                self.push_made(s, ty, Some(Term::App("field", vec![Term::Lit(Value::fixnum(k as i64)), o.term])));
            }
            "closure" | "nclosure" => {
                let (w, n) = (ops[0], ops[1].as_fixnum() as usize);
                let Some(callee) = self.certs.words.get(&w.raw()).cloned() else {
                    self.out.stopped = Some("a closure over a word with no certificate".into());
                    return Err(());
                };
                if callee.frees.len() != n {
                    self.out.failed.push(format!("{at}: a closure over {n} values, of a word that has {}", callee.frees.len()));
                    return Err(());
                }
                let mut vals = Vec::new();
                for _ in 0..n {
                    vals.push(self.pop(s, at)?);
                }
                vals.reverse();
                for (v, t) in vals.iter().zip(&callee.frees) {
                    self.holds(v, *t, at);
                }
                if name == "nclosure" {
                    self.out.stopped = Some("nclosure (the native convention)".into());
                    return Err(());
                }
                let ty = self.subr_of(&callee);
                self.push_made(s, ty, None);
            }
            "call" | "tcall" | "tailcall" | "ttailcall" => {
                let n = ops[0].as_fixnum() as usize;
                let f = self.pop(s, at)?;
                let mut args = Vec::new();
                for _ in 0..n {
                    args.push(self.pop(s, at)?);
                }
                args.reverse();
                let (params, result, effect) = match self.ty_of(&f) {
                    Some(t) if t.as_subr().is_some() => {
                        let (effect, params, result) = t.as_subr().expect("a subroutine");
                        (params, result, effect)
                    }
                    Some(Ty::Poly { .. }) => {
                        self.out.stopped = Some("a call of a polymorphic value: no instantiation in the certificate yet".into());
                        return Err(());
                    }
                    Some(_) => {
                        let msg = format!("{at}: a call of {}, not a procedure", self.show(f.ty.expect("known")));
                        self.out.failed.push(msg);
                        return Err(());
                    }
                    None => {
                        self.out.open.push(format!("{at}: a call of a value of no known type"));
                        if name.ends_with("tailcall") {
                            return Ok(None);
                        }
                        self.push_made(s, None, None);
                        return Ok(Some(s.clone()));
                    }
                };
                if params.len() != n {
                    self.out.failed.push(format!("{at}: {n} arguments to a procedure of {}", params.len()));
                    return Err(());
                }
                for (a, p) in args.iter().zip(&params) {
                    self.holds(a, *p, at);
                }
                self.effect = self.effect.union(&effect);
                if name.ends_with("tailcall") {
                    match cert.result {
                        Some(want) => self.holds(&V::new(Term::App("call", vec![f.term]), Some(result)), want, at),
                        None => self.out.failed.push(format!("{at}: a tail call from a word with no result")),
                    }
                    return Ok(None);
                }
                self.push_made(s, Some(result), None);
            }
            "return" => {
                let r = self.pop(s, at)?;
                match cert.result {
                    Some(want) => self.holds(&r, want, at),
                    None => self.out.failed.push(format!("{at}: a return from a word with no result")),
                }
                return Ok(None);
            }
            "exit" => return Ok(None),
            "branch" | "0branch" => {
                let to = (here as i64 + 2 + ops[0].as_fixnum()) as usize;
                let (taken, rest) = if name == "branch" {
                    (s.clone(), None)
                } else {
                    let flag = self.pop(s, at)?;
                    let (mut no, mut yes) = (s.clone(), s.clone());
                    self.narrow(&flag.term, false, &mut no);
                    self.narrow(&flag.term, true, &mut yes);
                    (no, Some(yes))
                };
                if to <= here {
                    // A loop: back to the start, whose assertion is the
                    // signature's precondition, the invariant.
                    if to != 0 || taken.stack.len() != entry.stack.len() {
                        self.out.failed.push(format!("{at}: a branch back to cell {to}, not a loop's start"));
                        return Err(());
                    }
                    for (v, t) in taken.stack.iter().zip(&cert.params) {
                        self.holds(v, *t, at);
                    }
                } else {
                    waiting.entry(to).or_default().push(taken);
                }
                return Ok(rest);
            }
            "prim" | "cons" if cert.ops.iter().any(|(k, _, _)| *k == here) => {
                let (_, op, inst) = cert.ops.iter().find(|(k, _, _)| *k == here).expect("found").clone();
                let pname = match name {
                    "prim" => fixpt_runtime::PRIMITIVES.get(ops[0].as_fixnum() as usize).map_or("?", |d| d.name),
                    _ => "cons",
                };
                // The cell must run the operation, as the compilers' table
                // has it (`lower::STANDARD`, and the few the compiler runs
                // by their own names).
                let runs = pname == op
                    || crate::cellular::standard_primitive(&op) == Some(pname)
                    || matches!((op.as_str(), pname), ("new", "%make-box") | ("char->string", "string"));
                if !runs {
                    self.out.failed.push(format!("{at}: said to run `{op}`, and runs {pname}"));
                    return Err(());
                }
                let n = if name == "prim" { ops[1].as_fixnum() as usize } else { 2 };
                let Some((params, result, effect)) = self.op_type(&op, &inst, n) else {
                    self.out.stopped = Some(format!("`{op}`: its type, instantiated"));
                    return Err(());
                };
                if params.len() != n {
                    self.out.failed.push(format!("{at}: `{op}` with {n} values, of {}", params.len()));
                    return Err(());
                }
                let mut args = Vec::new();
                for _ in 0..n {
                    args.push(self.pop(s, at)?);
                }
                args.reverse();
                for (a, p) in args.iter().zip(&params) {
                    self.holds(a, *p, at);
                }
                self.effect = self.effect.union(&effect);
                let terms = args.into_iter().map(|a| a.term).collect();
                self.push_made(s, Some(result), Some(Term::App("op", terms)));
            }
            "prim" => {
                let p = ops[0].as_fixnum() as usize;
                let pname = fixpt_runtime::PRIMITIVES.get(p).map_or("?", |d| d.name);
                self.out.stopped = Some(format!("prim {pname}"));
                return Err(());
            }
            other => {
                self.out.stopped = Some(other.to_string());
                return Err(());
            }
        }
        Ok(Some(s.clone()))
    }

    /// Standard operation `op`'s type, its binders instantiated at `inst`,
    /// for a call of `n` values: its parameters, result and effect.
    fn op_type(&mut self, op: &str, inst: &[crate::ast::D], n: usize) -> Option<(Vec<TyId>, TyId, Effect)> {
        let sym = self.c.interner.intern(op);
        let t = self.c.standard_type(sym)?;
        let (kinds, inner) = self.c.binders_of(t);
        let inner = match kinds.len() {
            0 => inner,
            k if k == inst.len() => {
                let map: HashMap<crate::ast::DVar, crate::ast::D> = kinds.iter().map(|(v, _)| *v).zip(inst.iter().cloned()).collect();
                self.c.subst(inner, &map)
            }
            _ => return None,
        };
        match self.c.arena.get(self.c.arena.resolve(inner)).clone() {
            // A `vsubr` (`list`): as many parameters as values, each its
            // element type.
            Ty::Named { which: 0, args } => match &args[..] {
                [crate::ast::D::Effect(e), crate::ast::D::Type(elem), crate::ast::D::Type(r)] => Some((vec![*elem; n], *r, e.clone())),
                _ => None,
            },
            t => t.as_subr().map(|(e, p, r)| (p, r, e)),
        }
    }

    /// Field `k` of `o`'s value: its type, by `o`'s.
    fn field_type(&mut self, o: &V, k: usize, at: &str) -> Result<Option<TyId>, ()> {
        let Some(t) = self.ty_of(o) else {
            self.out.open.push(format!("{at}: field {k} of a value of no known type"));
            return Ok(None);
        };
        let fail = |me: &mut Self| {
            let msg = format!("{at}: field {k} of {}", me.show(o.ty.expect("known")));
            me.out.failed.push(msg);
        };
        match t {
            Ty::Sum(arms) if k == 2 => {
                let _ = arms;
                Ok(Some(self.c.symbol))
            }
            Ty::Sum(arms) if k == 3 && arms.len() == 1 => Ok(Some(arms[0].1)),
            Ty::Sum(_) if k == 3 => {
                self.out.failed.push(format!("{at}: a sum's value, with its tag not known"));
                Err(())
            }
            Ty::Product(labels) if k >= 2 && k - 2 < labels.len() => Ok(Some(labels[k - 2].1)),
            Ty::Ref(t, r) if k == 2 => {
                self.reads(r);
                Ok(Some(t))
            }
            Ty::Bloblet { fields, frozen, region } if k >= 2 && k - 2 < fields.len() => {
                if !frozen {
                    self.reads(region);
                }
                Ok(Some(fields[k - 2]))
            }
            Ty::Module { vals, .. } if k >= 2 && k - 2 < vals.len() => Ok(Some(vals[k - 2].1)),
            _ => {
                fail(self);
                Err(())
            }
        }
    }

    /// What a branch on `flag` tells the way where it is true (`yes`) or
    /// false: narrowing, from what the flag's term says it tested.
    fn narrow(&mut self, flag: &Term, yes: bool, s: &mut State) {
        let Term::App("eq", args) = flag else { return };
        let [a, b] = &args[..] else { return };
        match (a, b) {
            // `not`, and the tests that end in one.
            (t, Term::Lit(f)) if f.is_false() => self.narrow(t, !yes, s),
            // `null?`: a list not `nil`, where false.
            (t, Term::Lit(n)) if n.is_null() => {
                for v in s.stack.iter_mut().filter(|v| v.term == *t) {
                    let Some(ty) = v.ty else { continue };
                    if let Ty::Pair(x, y, r, true) = self.c.arena.get(self.c.arena.resolve(ty)).clone() {
                        v.ty = Some(if yes { self.c.arena.ty(Ty::Nil) } else { self.c.arena.ty(Ty::Pair(x, y, r, false)) });
                    }
                }
            }
            // A sum's tag: the arm, where true.
            (Term::App("field", f), Term::Lit(tag)) if yes && f.first() == Some(&Term::Lit(Value::fixnum(2))) => {
                let scrutinee = &f[1];
                for v in s.stack.iter_mut().filter(|v| v.term == *scrutinee) {
                    let Some(ty) = v.ty else { continue };
                    if let Ty::Sum(arms) = self.c.arena.get(self.c.arena.resolve(ty)).clone() {
                        let name = self.heap.symbol_name(*tag);
                        let arm: Vec<_> = arms.into_iter().filter(|(l, _)| self.c.interner.name(*l) == name).collect();
                        v.ty = Some(self.c.arena.ty(Ty::Sum(arm)));
                    }
                }
            }
            _ => {}
        }
    }
}
