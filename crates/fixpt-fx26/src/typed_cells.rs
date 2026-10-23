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
use fixpt_heap::layout::cellular::{operands, CLOSURE_FREE0, CLOSURE_WORD, GLOBAL_VALUE, PRIMITIVES, ROUTINES, WORD_CELL0};
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
    pub poly: Vec<Vec<(crate::ast::DVar, crate::ast::Kind)>>,
    pub params: Vec<TyId>,
    pub frees: Vec<TyId>,
    pub result: Option<TyId>,
    pub effect: Option<Effect>,
    pub notes: Vec<(usize, Vec<Prop>)>,
    /// The cells that run a standard operation, by cell number: its name,
    /// and what its type's binders are instantiated at (checking found it;
    /// the verifier substitutes, and does not search).
    pub ops: Vec<(usize, String, Vec<crate::ast::D>)>,
    /// A conversion's: the type it is bound at, between a representation
    /// and its abstract type (a module's `up-t`, `down-t`), where its
    /// signature is the representation's identity. Checked (`conversion`),
    /// not trusted.
    pub conversion: Option<TyId>,
    /// Where a `plambda`'s body is, by its first cell and the cell after
    /// its last, and its binders: the value it makes there, if made purely,
    /// is of the `poly` type over them (`generalize`).
    pub gens: Vec<(usize, usize, Vec<(crate::ast::DVar, crate::ast::Kind)>)>,
    /// The cells whose standard operation runs at its own binders, not
    /// instantiated: a standard operation's word as a value, verified
    /// generically.
    pub own_ops: Vec<usize>,
}

/// The certificates a compilation made: each word's, and each global cell's
/// type, by the word's or cell's address. Good until the heap collects.
#[derive(Default)]
pub struct Certs {
    pub words: HashMap<u64, Cert>,
    pub globals: HashMap<u64, TyId>,
    /// Each module's abstract type, by its variable: the representation its
    /// conversions are certified at. Made by `Certs::settle`, which refuses
    /// two that differ.
    pub reps: HashMap<crate::ast::DVar, TyId>,
}

impl Certs {
    /// The abstract types' representations, from the conversions'
    /// certificates: each conversion's signature is `(R) -> R`, and the type
    /// it is bound at names the variable. Two conversions of one variable at
    /// different representations are an error: the certificates would let a
    /// value of one be taken for the other.
    pub fn settle(&mut self, c: &Checker) -> Result<(), String> {
        for cert in self.words.values() {
            let (Some(t), [rep]) = (cert.conversion, &cert.params[..]) else { continue };
            let Some((_, ps, r)) = c.arena.get(c.arena.resolve(t)).as_subr() else { continue };
            for side in [ps.first().copied(), Some(r)].into_iter().flatten() {
                if let Ty::Var(v) = c.arena.get(c.arena.resolve(side)) {
                    match self.reps.insert(*v, *rep) {
                        Some(old) if c.arena.resolve(old) != c.arena.resolve(*rep) => {
                            return Err(format!("two representations certified for {}", c.show_ty(side)));
                        }
                        _ => {}
                    }
                }
            }
        }
        Ok(())
    }
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
    /// Closures made with a placeholder for a free value (a `letrec`'s, `#f`
    /// for a sibling not made yet): each closure's term, the free value,
    /// and the type it must be given (by `field!`) before the closure is
    /// used.
    pending: Vec<(Term, usize, TyId)>,
}

/// One instruction: where its cell is, its routine's name (or `None`, a
/// word run as a cell), and its operands.
struct Ins {
    at: usize,
    name: Option<&'static str>,
    ops: Vec<Value>,
}

/// Whether a certificate's operation note is an instantiation's (of a
/// callee, a value, a `proj`), not a standard operation's.
fn marker(op: &str) -> bool {
    matches!(op, "%call" | "%inst" | "%proj" | "%make")
}

/// Verify `word` against its certificate in `certs`.
pub fn verify(c: &mut Checker, heap: &Heap, certs: &Certs, word: Value) -> Outcome {
    let mut v = Verifier { c, heap, certs, out: Outcome::default(), made: 0, effect: Effect::pure(), proving: Vec::new(), gen_effects: Vec::new() };
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
    /// The values a call made that prove something (a predicate's result,
    /// `(bool (then …) (else …))`): its term, what holds where it is true and
    /// where false, and the call's arguments' terms, by position. Its
    /// `ensures`, assumed where a branch tests it (`narrow`).
    proving: Vec<(Term, Vec<crate::ast::Prop>, Vec<crate::ast::Prop>, Vec<Term>)>,
    /// The effect so far where each `plambda` body being verified started:
    /// the body's own is what is added since, which must be none.
    gen_effects: Vec<Effect>,
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
        match self.fits(v, t) {
            Some(true) => self.out.discharged += 1,
            Some(false) => {
                let msg = format!("{what}: {} is not within {}", self.show(v.ty.expect("known")), self.show(t));
                self.out.failed.push(msg);
            }
            None => self.out.open.push(format!("{what}: (: {:?} {})", v.term, self.show(t))),
        }
    }

    /// Whether `v` is of type `t`: a literal looked at, anything else by
    /// subtyping; none if `v`'s type is not known.
    fn fits(&mut self, v: &V, t: TyId) -> Option<bool> {
        if let Term::Lit(x) = v.term
            && self.inhabits(x, t)
        {
            return Some(true);
        }
        // A `poly`'s value, made of a value checked against its body with
        // its binders held abstract (no `plambda`): of the body's type.
        let is_poly = |me: &Self, t: Option<TyId>| t.is_some_and(|t| matches!(me.c.arena.get(me.c.arena.resolve(t)), Ty::Poly { .. }));
        let t = match self.c.arena.get(self.c.arena.resolve(t)).clone() {
            Ty::Poly { body, .. } if !is_poly(self, v.ty) => body,
            _ => t,
        };
        // Two `poly`s over the very same binders (a value checked against
        // the `poly` it is stored as): their bodies compared.
        let (mut s, mut t) = (v.ty?, t);
        loop {
            match (self.c.arena.get(self.c.arena.resolve(s)).clone(), self.c.arena.get(self.c.arena.resolve(t)).clone()) {
                (Ty::Poly { binders: a, body: x }, Ty::Poly { binders: b, body: y }) if a == b => (s, t) = (x, y),
                _ => break,
            }
        }
        Some(self.c.subtype(s, t))
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

    /// The procedure type a word's signature gives a closure over it: a
    /// conversion's, the type it is bound at.
    fn subr_of(&mut self, cert: &Cert) -> Option<TyId> {
        if let Some(t) = cert.conversion {
            return Some(t);
        }
        let (result, effect) = (cert.result?, cert.effect.clone()?);
        let conv = self.c.conv_default;
        let subr = self.c.arena.ty(Ty::Subr { conv, effect, params: cert.params.clone(), result });
        // Under each level's binders, the innermost first.
        let mut t = subr;
        for level in cert.poly.iter().rev() {
            t = self.c.arena.ty(Ty::Poly { binders: level.clone(), body: t });
        }
        Some(t)
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
        if self.conversion(&code, cert) {
            return;
        }
        // A dependent procedure's (`(select $k t)`, the abstract type `t` of
        // parameter `k`, a module): seen from inside, each such type is that
        // module's own abstract type, as its body was checked.
        let given = self.selects(&cert.params);
        let mut cert = cert.clone();
        for p in &mut cert.params {
            *p = self.c.instantiate_params(*p, &given);
        }
        cert.result = cert.result.map(|r| self.c.instantiate_params(r, &given));
        let cert = &cert;
        let entry = State {
            stack: cert.params.iter().enumerate().map(|(i, t)| V::new(Term::Slot(i), Some(*t))).collect(),
            pending: Vec::new(),
        };
        let notes: HashMap<usize, &Vec<Prop>> = cert.notes.iter().map(|(k, p)| (*k, p)).collect();
        // The states waiting at each later cell, from branches to it.
        let mut waiting: HashMap<usize, Vec<State>> = HashMap::new();
        let mut cur = Some(entry.clone());
        let mut i = 0;
        while i < code.len() {
            let ins = &code[i];
            i += 1;
            let mut arriving: Vec<State> = waiting.remove(&ins.at).unwrap_or_default();
            if let Some(s) = cur.take() {
                arriving.push(s);
            }
            if arriving.is_empty() {
                // Reached by no way: the code after an unconditional branch
                // that nothing branches to. Not run, so not verified.
                continue;
            }
            let at = format!("cell {} ({})", ins.at, ins.name.unwrap_or("a word"));
            let mut s = match notes.get(&ins.at) {
                Some(note) => self.assume(&arriving, note, &at),
                None => match self.join(&arriving, &at) {
                    Some(s) => s,
                    None => return,
                },
            };
            if self.generalize(cert, ins.at, &mut s, &at).is_err() || self.instances(cert, ins.at, &mut s, &at).is_err() {
                return;
            }
            // A value of a sum with no arm left (every tag tested, and none
            // was it): no way reaches here, so nothing here runs.
            if s.stack.iter().any(|v| v.ty.is_some_and(|t| matches!(self.c.arena.get(self.c.arena.resolve(t)), Ty::Sum(arms) if arms.is_empty()))) {
                continue;
            }
            let Some(name) = ins.name else {
                self.out.stopped = Some("a word run as a cell".into());
                return;
            };
            match self.idiom(&code[i - 1..], cert, &mut s, &at, &waiting) {
                Some(Ok(n)) => {
                    i += n - 1;
                    cur = Some(s);
                    continue;
                }
                Some(Err(())) => return,
                None => {}
            }
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

    /// The `plambda` bodies that end before cell `at`, innermost first: the
    /// value each made, on top, generalized over its binders, where it was
    /// made purely (its effect nothing: a `plambda` body must be pure, so
    /// that nothing depends on the binders' instances); then those that
    /// start there.
    fn generalize(&mut self, cert: &Cert, at_cell: usize, s: &mut State, at: &str) -> Result<(), ()> {
        let mut ends: Vec<&(usize, usize, Vec<(crate::ast::DVar, crate::ast::Kind)>)> = cert.gens.iter().filter(|(_, e, _)| *e == at_cell).collect();
        ends.sort_by_key(|(start, _, _)| std::cmp::Reverse(*start));
        for (_, _, binders) in ends {
            let Some(before) = self.gen_effects.pop() else {
                self.out.failed.push(format!("{at}: a `plambda` body ends that did not start"));
                return Err(());
            };
            if !self.effect.0.is_empty() {
                let msg = format!("{at}: a `plambda` body with effect {}", self.c.show_effect(&self.effect));
                self.out.failed.push(msg);
                return Err(());
            }
            self.effect = before;
            let Some(v) = s.stack.last_mut() else {
                self.out.failed.push(format!("{at}: a `plambda` body that made no value"));
                return Err(());
            };
            // Unless already over them: a lambda's word under the chain of
            // `plambda`s it is the body of (`Cert::poly`).
            if let Some(t) = v.ty {
                let mut under = self.c.arena.resolve(t);
                let mut already = false;
                while let Ty::Poly { binders: bs, body } = self.c.arena.get(under).clone() {
                    already |= bs == *binders;
                    under = self.c.arena.resolve(body);
                }
                if !already {
                    v.ty = Some(self.c.arena.ty(Ty::Poly { binders: binders.clone(), body: t }));
                    v.made = v.ty;
                }
            }
        }
        for _ in cert.gens.iter().filter(|(start, _, _)| *start == at_cell) {
            self.gen_effects.push(std::mem::replace(&mut self.effect, Effect::pure()));
        }
        Ok(())
    }

    /// The values instantiated before cell `at`, on top, in the order made:
    /// `%inst`, every binder (outermost first, as checking found them);
    /// `%proj`, the outermost level's, at its arguments.
    fn instances(&mut self, cert: &Cert, at_cell: usize, s: &mut State, at: &str) -> Result<(), ()> {
        for (_, op, ds) in cert.ops.iter().filter(|(k, op, _)| *k == at_cell && (op == "%inst" || op == "%proj")) {
            let Some(v) = s.stack.last().cloned() else {
                self.out.failed.push(format!("{at}: an instance of nothing"));
                return Err(());
            };
            let Some(t) = v.ty else { continue };
            let (kinds, inner) = match op.as_str() {
                "%inst" => self.c.binders_of(t),
                _ => match self.c.arena.get(self.c.arena.resolve(t)).clone() {
                    Ty::Poly { binders, body } => (binders, body),
                    _ => (Vec::new(), t),
                },
            };
            // Already of no binders (a literal, `nil`, of its exact type):
            // nothing to instantiate.
            if kinds.is_empty() {
                continue;
            }
            if kinds.len() != ds.len() {
                let msg = format!("{at}: {} instantiated at {} descriptions", self.show(t), ds.len());
                self.out.failed.push(msg);
                return Err(());
            }
            let map: HashMap<crate::ast::DVar, crate::ast::D> = kinds.iter().map(|(v, _)| *v).zip(ds.iter().cloned()).collect();
            let inst = self.c.subst(inner, &map);
            let top = s.stack.last_mut().expect("there");
            top.ty = Some(inst);
            top.made = Some(inst);
        }
        Ok(())
    }

    /// A standard operation compiled as an idiom, several routines, where
    /// the certificate says the operation runs at `code`'s first cell and
    /// the cells are the idiom's, as the compilers make it
    /// (`Compiler::standard_on`), no branch landing inside: the operation's
    /// triple, applied to the whole, and how many instructions it is.
    fn idiom(&mut self, code: &[Ins], cert: &Cert, s: &mut State, at: &str, waiting: &HashMap<usize, Vec<State>>) -> Option<Result<usize, ()>> {
        let (_, op, inst) = cert.ops.iter().find(|(k, op, _)| *k == code[0].at && !marker(op))?.clone();
        let lit = |v: i64| move |ins: &Ins| ins.name == Some("lit") && ins.ops[0] == Value::fixnum(v);
        let named = |r: &'static str| move |ins: &Ins| ins.name == Some(r);
        let prim = |p: &'static str, n: i64| {
            move |ins: &Ins| ins.name == Some("prim") && ins.ops[1].as_fixnum() == n && fixpt_runtime::PRIMITIVES.get(ins.ops[0].as_fixnum() as usize).is_some_and(|d| d.name == p)
        };
        let heap = self.heap;
        let unit = move |ins: &Ins| ins.name == Some("lit") && heap.is_a(ins.ops[0], ObjType::Symbol) && heap.symbol_name(ins.ops[0]) == "#u";
        type Is<'a> = Box<dyn Fn(&Ins) -> bool + 'a>;
        // Each idiom's cells, and how many values the operation takes off
        // the stack beyond its arguments (`make-array`'s 0, pushed first).
        let (cells, extra): (Vec<Is>, usize) = match op.as_str() {
            "array-ref" => (vec![Box::new(lit(2)), Box::new(named("int-add")), Box::new(named("field@"))], 0),
            "array-length" => (vec![Box::new(prim("%bloblet-fields", 1)), Box::new(lit(1)), Box::new(named("int-sub"))], 0),
            "array-set!" => (
                vec![
                    Box::new(named("swap")),
                    Box::new(lit(2)),
                    Box::new(named("int-add")),
                    Box::new(named("swap")),
                    Box::new(prim("%bloblet-set!", 3)),
                    Box::new(named("drop")),
                    Box::new(unit),
                ],
                0,
            ),
            "make-array" => (vec![Box::new(prim("%make-bloblet-filled", 3))], 1),
            // A tag or a key: a new box, of unit.
            "make-continuation-prompt-tag" | "make-escape-tag" | "make-continuation-mark-key" => (vec![Box::new(unit), Box::new(prim("%make-box", 1))], 0),
            _ => return None,
        };
        let n = cells.len();
        if code.len() < n || !cells.iter().zip(code).all(|(is, ins)| is(ins)) || code[1..n].iter().any(|ins| waiting.contains_key(&ins.at)) {
            return None;
        }
        let Some((params, result, effect)) = self.op_type(&op, &inst, 0, cert.own_ops.contains(&code[0].at)) else {
            self.out.stopped = Some(format!("`{op}`: its type, instantiated"));
            return Some(Err(()));
        };
        let mut args = Vec::new();
        for _ in 0..params.len() {
            args.push(self.pop(s, at).ok()?);
        }
        args.reverse();
        for _ in 0..extra {
            match self.pop(s, at) {
                Ok(v) if v.term == Term::Lit(Value::fixnum(0)) => {}
                _ => {
                    self.out.failed.push(format!("{at}: `{op}` without its 0"));
                    return Some(Err(()));
                }
            }
        }
        for (a, p) in args.iter().zip(&params) {
            self.holds(a, *p, at);
        }
        self.effect = self.effect.union(&effect);
        // An array made is as long as its first argument says, where its
        // type knows (`Checker::array_sized`).
        let result = match (op.as_str(), self.c.arena.get(self.c.arena.resolve(result)).clone()) {
            ("make-array", Ty::Array(t, _, r)) => {
                let size = match (&args[0].term, self.ty_of(&args[0])) {
                    (Term::Lit(k), _) if k.is_fixnum() && k.as_fixnum() >= 0 => Some(Size::lit(k.as_fixnum())),
                    (_, Some(Ty::Nat(s))) => Some(s),
                    _ => None,
                };
                size.map_or(result, |n| self.c.arena.ty(Ty::Array(t, n, r)))
            }
            _ => result,
        };
        let terms = args.into_iter().map(|a| a.term).collect();
        self.push_made(s, Some(result), Some(Term::App("op", terms)));
        Some(Ok(n))
    }

    /// Whether `code` is a conversion between a representation and its
    /// abstract type, and is certified as one rightly (a VC discharged, or
    /// failed); false if it is not one, to be verified as any word is.
    /// A conversion is the identity, `slot 0; return`, of one parameter.
    /// Certified at `(A) -> B`, one of `A` and `B` must be the other's
    /// representation:
    /// - a generative type (`define-generative`) and its unfolding;
    /// - a module's abstract type, a variable, and the representation its
    ///   conversions are certified at, each of them the same (`conversion`
    ///   on the module's `up-t` and `down-t`, signed `(R) -> R`).
    fn conversion(&mut self, code: &[Ins], cert: &Cert) -> bool {
        let identity = matches!(&code[..], [a, b] if a.name == Some("slot") && a.ops[0].as_fixnum() == 0 && b.name == Some("return"));
        if !identity || cert.params.len() != 1 {
            return false;
        }
        let (from, to) = match cert.conversion {
            Some(t) => match self.c.arena.get(self.c.arena.resolve(t)).as_subr() {
                Some((_, ps, r)) if ps.len() == 1 => (ps[0], r),
                _ => return false,
            },
            None => match cert.result {
                Some(r) => (cert.params[0], r),
                None => return false,
            },
        };
        let rep_of = |me: &mut Self, t: TyId| -> Option<TyId> {
            match me.c.arena.get(me.c.arena.resolve(t)).clone() {
                Ty::Named { which, args } if (which as usize) < me.c.generatives.len() => Some(me.c.unfold(which, &args)),
                Ty::Var(v) => me.certs.reps.get(&v).copied(),
                _ => None,
            }
        };
        let same = |me: &mut Self, a: TyId, b: TyId| me.c.subtype(a, b) && me.c.subtype(b, a);
        let ok = match (rep_of(self, to), rep_of(self, from)) {
            (Some(r), _) if same(self, r, from) => true,
            (_, Some(r)) if same(self, r, to) => true,
            _ => false,
        };
        if !ok {
            if cert.conversion.is_none() && self.c.subtype(from, to) {
                // The identity at a type it is: no conversion, verified as
                // any word is.
                return false;
            }
            let msg = format!("cell 0: a conversion from {} to {}, neither the other's representation", self.show(from), self.show(to));
            self.out.failed.push(msg);
        } else {
            self.out.discharged += 1;
        }
        true
    }

    /// What `(select $k t)` stands for, given values of `types` by
    /// position: for each that is a module, its abstract types, by name.
    fn selects(&mut self, types: &[TyId]) -> HashMap<(usize, fixpt_read::Sym), TyId> {
        let mut given = HashMap::new();
        for (k, t) in types.iter().enumerate() {
            if let Ty::Module { abs, descs, .. } = self.c.arena.get(self.c.arena.resolve(*t)).clone() {
                for (a, w) in abs {
                    given.insert((k, a), self.c.arena.ty(Ty::Var(w)));
                }
                // A type it names, transparently: that type.
                for (a, d) in descs {
                    given.entry((k, a)).or_insert(d);
                }
            }
        }
        given
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
        if arriving.iter().any(|s| s.pending != first.pending) {
            self.out.failed.push(format!("{at}: the ways in leave different closures unfinished"));
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
        Some(State { stack, pending: first.pending.clone() })
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
        self.join(&ways, at).unwrap_or(State { stack: Vec::new(), pending: Vec::new() })
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
        // While a closure is unfinished, only what finishes a `letrec`'s
        // group: no closure may run, or be kept anywhere it could be found,
        // with a free value still owed.
        if !s.pending.is_empty() && !matches!(name, "slot" | "lit" | "drop" | "closure" | "field!") {
            self.out.failed.push(format!("{at}: a closure is used before its free values are all given"));
            return Err(());
        }
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
                    // A list of a known length: a pair if longer than none.
                    Some(Ty::NList { elem, size, region }) => {
                        if size.as_lit().is_none_or(|n| n <= 0) {
                            self.out.debts.push(format!("{at}: (not (eq {:?} nil))", p.term));
                        }
                        self.reads(region);
                        let ty = if name == "pair-car" {
                            elem
                        } else {
                            match size.as_lit() {
                                Some(n) if n > 0 => self.c.arena.ty(Ty::NList { elem, size: Size::lit(n - 1), region }),
                                _ => self.c.arena.ty(Ty::NList { elem, size: Size::Finite, region }),
                            }
                        };
                        let f = if name == "pair-car" { "car" } else { "cdr" };
                        self.push_made(s, Some(ty), Some(Term::App(f, vec![p.term])));
                    }
                    // A union with a pair in it (a `datum`): that pair's
                    // parts, the pair a debt, as the machine checks it.
                    Some(Ty::Union(ms)) if ms.iter().filter(|m| matches!(self.c.arena.get(self.c.arena.resolve(**m)), Ty::Pair(..))).count() == 1 => {
                        let pair = ms.iter().find_map(|m| match self.c.arena.get(self.c.arena.resolve(*m)) {
                            Ty::Pair(a, b, r, _) => Some((*a, *b, *r)),
                            _ => None,
                        });
                        let (a, b, r) = pair.expect("one pair");
                        self.out.debts.push(format!("{at}: (shape {:?} pair)", p.term));
                        self.reads(r);
                        let f = if name == "pair-car" { "car" } else { "cdr" };
                        self.push_made(s, Some(if name == "pair-car" { a } else { b }), Some(Term::App(f, vec![p.term])));
                    }
                    // `nil` itself: the machine's test fails, safely, as the
                    // program means (a debt sure to fail).
                    Some(Ty::Nil) => {
                        self.out.debts.push(format!("{at}: (not (eq {:?} nil)), false", p.term));
                        return Ok(None);
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
                    let named = self.heap.bloblet_slot(w, fixpt_heap::layout::cellular::WORD_NAME);
                    let name = if self.heap.is_a(named, ObjType::Symbol) { self.heap.symbol_name(named) } else { "?".into() };
                    let name: String = name.chars().take_while(|c| *c != '@').collect();
                    self.out.stopped = Some(format!("a closure over a word with no certificate ({name})"));
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
                if name == "nclosure" {
                    self.out.stopped = Some("nclosure (the native convention)".into());
                    return Err(());
                }
                let made = self.fresh();
                for (j, (v, t)) in vals.iter().zip(&callee.frees).enumerate() {
                    // A placeholder, `#f` where it does not fit: the free
                    // value is owed, to be given before the closure is used.
                    if v.term == Term::Lit(Value::FALSE) && self.fits(v, *t) != Some(true) {
                        s.pending.push((made.clone(), j, *t));
                    } else {
                        self.holds(v, *t, at);
                    }
                }
                let ty = self.subr_of(&callee);
                self.push_made(s, ty, Some(made));
            }
            "call" | "tcall" | "tailcall" | "ttailcall" => {
                let n = ops[0].as_fixnum() as usize;
                let f = self.pop(s, at)?;
                let mut args = Vec::new();
                for _ in 0..n {
                    args.push(self.pop(s, at)?);
                }
                args.reverse();
                // A polymorphic callee, instantiated as the certificate says:
                // its binders, outermost first, substituted.
                let callee = match (self.ty_of(&f), cert.ops.iter().find(|(k, op, _)| *k == here && op == "%call")) {
                    (Some(Ty::Poly { .. }), Some((_, _, inst))) => {
                        let t = f.ty.expect("known");
                        let (kinds, inner) = self.c.binders_of(t);
                        if kinds.len() != inst.len() {
                            self.out.failed.push(format!("{at}: a callee of {} binders, instantiated at {}", kinds.len(), inst.len()));
                            return Err(());
                        }
                        let map: HashMap<crate::ast::DVar, crate::ast::D> = kinds.iter().map(|(v, _)| *v).zip(inst.iter().cloned()).collect();
                        let t = self.c.subst(inner, &map);
                        Some(self.c.arena.get(self.c.arena.resolve(t)).clone())
                    }
                    (t, _) => t,
                };
                let (params, result, effect) = match callee {
                    // A `vsubr`: as many values as it is called with, each
                    // its element type.
                    Some(Ty::Named { which: 0, args: ds }) if matches!(&ds[..], [crate::ast::D::Effect(_), crate::ast::D::Type(_), crate::ast::D::Type(_)]) => {
                        let [crate::ast::D::Effect(e), crate::ast::D::Type(elem), crate::ast::D::Type(r)] = &ds[..] else { unreachable!() };
                        (vec![*elem; n], *r, e.clone())
                    }
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
                // A dependent procedure's: each `(select $k t)` the abstract
                // type of argument `k`'s module.
                let arg_types: Vec<TyId> = args.iter().map(|a| a.ty.unwrap_or(self.c.void)).collect();
                let given = self.selects(&arg_types);
                let params: Vec<TyId> = params.iter().map(|p| self.c.instantiate_params(*p, &given)).collect();
                let result = self.c.instantiate_params(result, &given);
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
            "field!" => {
                // ( x obj k -- ), `k` a literal.
                let (k, o, x) = (self.pop(s, at)?, self.pop(s, at)?, self.pop(s, at)?);
                let Term::Lit(k) = k.term else {
                    self.out.stopped = Some("field! at a field not known".into());
                    return Err(());
                };
                let k = k.as_fixnum() as usize;
                // A closure's free value owed: given.
                if let Some(i) = s.pending.iter().position(|(c, j, _)| *c == o.term && CLOSURE_FREE0 + *j == k) {
                    let (_, _, t) = s.pending.remove(i);
                    self.holds(&x, t, at);
                    return Ok(Some(s.clone()));
                }
                match self.ty_of(&o) {
                    Some(Ty::Ref(t, r)) if k == 2 => {
                        self.holds(&x, t, at);
                        self.effect = self.effect.union(&Effect::atom(crate::ast::Atom::Write(r)));
                    }
                    Some(Ty::Bloblet { fields, frozen: false, region }) if k >= 2 && k - 2 < fields.len() => {
                        self.holds(&x, fields[k - 2], at);
                        self.effect = self.effect.union(&Effect::atom(crate::ast::Atom::Write(region)));
                    }
                    _ => {
                        self.out.stopped = Some("field! of what it does not know".into());
                        return Err(());
                    }
                }
            }
            "prim" if cert.ops.iter().any(|(k, op, _)| *k == here && op == "%make") => {
                let Some((_, _, ds)) = cert.ops.iter().find(|(k, op, _)| *k == here && op == "%make") else { unreachable!() };
                // Made as `own` (a module's own type), taken as `t`.
                let (t, own) = match &ds[..] {
                    [crate::ast::D::Type(t)] => (*t, *t),
                    [crate::ast::D::Type(t), crate::ast::D::Type(own)] => (*t, *own),
                    _ => {
                        self.out.failed.push(format!("{at}: data made of no type"));
                        return Err(());
                    }
                };
                let pname = fixpt_runtime::PRIMITIVES.get(ops[0].as_fixnum() as usize).map_or("?", |d| d.name);
                let n = ops[1].as_fixnum() as usize;
                if !matches!(pname, "%make-frozen" | "%make-bloblet" | "%region-make-bloblet") || n == 0 {
                    self.out.failed.push(format!("{at}: data said made by {pname}"));
                    return Err(());
                }
                let mut vals = Vec::new();
                for _ in 0..n {
                    vals.push(self.pop(s, at)?);
                }
                vals.reverse();
                if matches!(self.c.arena.get(self.c.arena.resolve(own)), Ty::Bloblet { .. }) {
                    return self.bloblet_made(&vals, own, at).map(|()| {
                        self.push_made(s, Some(own), None);
                        Some(s.clone())
                    });
                }
                let kind = vals.remove(0);
                let fields: Option<Vec<TyId>> = match (&kind.term, self.c.arena.get(self.c.arena.resolve(own)).clone()) {
                    (Term::Lit(k), Ty::Product(labels)) if *k == Value::fixnum(37) => Some(labels.iter().map(|(_, t)| *t).collect()),
                    // A module's values, as its own type lists them, unless
                    // it includes another: then its product holds the module
                    // included, and its type that module's values, reached
                    // by a path (`Pick::Path`), which this does not follow.
                    (Term::Lit(k), Ty::Module { vals: vs, descs, .. }) if *k == Value::fixnum(37) => {
                        if descs.iter().any(|(d, _)| self.c.interner.name(*d).starts_with("%hidden")) || vs.len() != vals.len() {
                            self.out.stopped = Some("a module that includes another (its values laid out apart from its type)".into());
                            return Err(());
                        }
                        Some(vs.iter().map(|(_, t)| *t).collect())
                    }
                    // A sum: its tag, a literal symbol, names an arm, whose
                    // type the value must be.
                    (Term::Lit(k), Ty::Sum(arms)) if *k == Value::fixnum(36) && vals.len() == 2 => match vals[0].term {
                        Term::Lit(tag) if self.heap.is_a(tag, ObjType::Symbol) => {
                            let name = self.heap.symbol_name(tag);
                            arms.iter().find(|(l, _)| self.c.interner.name(*l) == name).map(|(_, a)| vec![self.c.symbol, *a])
                        }
                        _ => None,
                    },
                    _ => None,
                };
                let Some(fields) = fields.filter(|f| f.len() == vals.len()) else {
                    let msg = format!("{at}: {} values made a {}", vals.len(), self.show(own));
                    self.out.failed.push(msg);
                    return Err(());
                };
                for (v, f) in vals.iter().zip(&fields) {
                    self.holds(v, *f, at);
                }
                if own != t {
                    // Packing a module's abstract types with a witness (its
                    // values typed by another module's, `counter..t`, taken as
                    // the abstract `t`): a rule this does not have yet.
                    let abs_of = |me: &Self, t: TyId| match me.c.arena.get(me.c.arena.resolve(t)) {
                        Ty::Module { abs, .. } => abs.iter().map(|(n, _)| *n).collect::<Vec<_>>(),
                        _ => Vec::new(),
                    };
                    let (mine, claimed) = (abs_of(self, own), abs_of(self, t));
                    if claimed.iter().any(|n| !mine.contains(n)) {
                        self.out.stopped = Some("a module packed with a witness for an abstract type".into());
                        return Err(());
                    }
                    let made = V::new(Term::Made(0), Some(own));
                    self.holds(&made, t, at);
                }
                // Kept as its own type, which is within the one it is taken
                // as, and is its values' layout.
                self.push_made(s, Some(own), None);
            }
            "prim" | "cons" if cert.ops.iter().any(|(k, op, _)| *k == here && !marker(op)) => {
                let (_, op, inst) = cert.ops.iter().find(|(k, op, _)| *k == here && !marker(op)).expect("found").clone();
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
                let Some((params, result, effect)) = self.op_type(&op, &inst, n, cert.own_ops.contains(&here)) else {
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
                let terms: Vec<Term> = args.into_iter().map(|a| a.term).collect();
                let made = self.fresh();
                if let Ty::Proving { then, els } = self.c.arena.get(self.c.arena.resolve(result)).clone() {
                    self.proving.push((made.clone(), then, els, terms));
                }
                self.push_made(s, Some(result), Some(made));
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
    fn op_type(&mut self, op: &str, inst: &[crate::ast::D], n: usize, own: bool) -> Option<(Vec<TyId>, TyId, Effect)> {
        let sym = self.c.interner.intern(op);
        let t = self.c.standard_type(sym)?;
        let (kinds, inner) = self.c.binders_of(t);
        // At its own binders, abstract (a standard operation's word as a
        // value, verified generically).
        let inner = match kinds.len() {
            _ if own => inner,
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

    /// A bloblet made, of type `t`, from `vals`: `make-bloblet`'s, its
    /// suffix's bytes then its fields; `rmake-bloblet`'s, a place first,
    /// whose region is the bloblet's.
    fn bloblet_made(&mut self, vals: &[V], t: TyId, at: &str) -> Result<(), ()> {
        let Ty::Bloblet { fields, frozen: false, region } = self.c.arena.get(self.c.arena.resolve(t)).clone() else {
            self.out.failed.push(format!("{at}: a bloblet made frozen"));
            return Err(());
        };
        let rest = match vals.len().checked_sub(fields.len()) {
            Some(1) => vals,
            Some(2) => {
                match self.ty_of(&vals[0]) {
                    Some(Ty::Place(r)) if r == region => {}
                    _ => {
                        self.out.failed.push(format!("{at}: a bloblet made in a place not its region's"));
                        return Err(());
                    }
                }
                &vals[1..]
            }
            _ => {
                let msg = format!("{at}: {} values made a {}", vals.len(), self.show(t));
                self.out.failed.push(msg);
                return Err(());
            }
        };
        let int = self.c.int;
        self.holds(&rest[0], int, at);
        for (v, f) in rest[1..].iter().zip(&fields) {
            self.holds(v, *f, at);
        }
        self.effect = self.effect.union(&Effect::atom(crate::ast::Atom::Alloc(region)));
        Ok(())
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
            // A module that includes another holds that module, which its
            // type's values are reached through: not followed here.
            Ty::Module { descs, .. } if descs.iter().any(|(d, _)| self.c.interner.name(*d).starts_with("%hidden")) => {
                self.out.stopped = Some("a field of a module that includes another".into());
                Err(())
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
        // A predicate's result: what it proves of its arguments, where true
        // and where false, as its type says (the call rule's `ensures`).
        if let Some((_, then, els, args)) = self.proving.iter().find(|(t, ..)| t == flag).cloned() {
            for p in if yes { then } else { els } {
                // `(length i j)`: argument `i`, a list, is as long as `j`
                // says, an `nlist` (what `certify-length` of it then says);
                // `(nat i)`: argument `i` is a natural.
                if let crate::ast::Prop::Length(i, j) = p
                    && let (Some(list), Some(len)) = (args.get(i).cloned(), args.get(j).cloned())
                {
                    let size = match &len {
                        Term::Lit(k) if k.is_fixnum() && k.as_fixnum() >= 0 => Size::lit(k.as_fixnum()),
                        _ => s.stack.iter().find(|v| v.term == len).and_then(|v| self.ty_of(v)).and_then(|t| match t {
                            Ty::Nat(n) => Some(n),
                            _ => None,
                        }).unwrap_or(Size::Finite),
                    };
                    for v in s.stack.iter_mut().filter(|v| v.term == list) {
                        let Some(ty) = v.ty else { continue };
                        if let Ty::Pair(elem, _, region, true) = self.c.arena.get(self.c.arena.resolve(ty)).clone() {
                            v.ty = Some(self.c.arena.ty(Ty::NList { elem, size: size.clone(), region }));
                        }
                    }
                    continue;
                }
                if let crate::ast::Prop::Nat(i) = p
                    && let Some(x) = args.get(i).cloned()
                {
                    let nat = self.c.arena.ty(Ty::Nat(Size::Finite));
                    for v in s.stack.iter_mut().filter(|v| v.term == x) {
                        v.ty = Some(nat);
                    }
                    continue;
                }
                let crate::ast::Prop::Shape { param, shape, negated } = p else { continue };
                let Some(arg) = args.get(param) else { continue };
                for v in s.stack.iter_mut().filter(|v| v.term == *arg) {
                    let Some(ty) = v.ty else { continue };
                    let (y, n) = self.c.narrowed_by(ty, 1u32 << shape);
                    if let Some(t) = if negated { n } else { y } {
                        v.ty = Some(t);
                    }
                }
            }
            return;
        }
        // A value tested itself: not `#f`, where true.
        if !matches!(flag, Term::App("eq", _)) {
            for v in s.stack.iter_mut().filter(|v| v.term == *flag) {
                let Some(ty) = v.ty else { continue };
                if let Ty::Union(ms) = self.c.arena.get(self.c.arena.resolve(ty)).clone() {
                    let is_false = |me: &Self, m: &TyId| matches!(me.c.arena.get(me.c.arena.resolve(*m)), Ty::False);
                    let (f, rest): (Vec<TyId>, Vec<TyId>) = ms.into_iter().partition(|m| is_false(self, m));
                    let narrowed = match (yes, &rest[..], f.is_empty()) {
                        (true, [one], _) => Some(*one),
                        (true, _, _) => Some(self.c.arena.ty(Ty::Union(rest.clone()))),
                        (false, _, false) => Some(self.c.arena.ty(Ty::False)),
                        _ => None,
                    };
                    if let Some(n) = narrowed {
                        v.ty = Some(n);
                    }
                }
            }
            return;
        }
        let Term::App("eq", args) = flag else { return };
        let [a, b] = &args[..] else { return };
        match (a, b) {
            // `not`, and the tests that end in one.
            (t, Term::Lit(f)) if f.is_false() => self.narrow(t, !yes, s),
            // `null?`: `nil` where true, and what else it may be where false,
            // by shape, as the checkers narrow (`narrowed_by`).
            (t, Term::Lit(n)) if n.is_null() => {
                let nil = crate::check::SHAPES.iter().position(|(n, _)| *n == "nil").map_or(0, |i| 1u32 << i);
                for v in s.stack.iter_mut().filter(|v| v.term == *t) {
                    let Some(ty) = v.ty else { continue };
                    let (y, n) = self.c.narrowed_by(ty, nil);
                    if let Some(t) = if yes { y } else { n } {
                        v.ty = Some(t);
                    }
                }
            }
            // A sum's tag: that arm, where true; the others, where false.
            (Term::App("field", f), Term::Lit(tag)) if f.first() == Some(&Term::Lit(Value::fixnum(2))) && self.heap.is_a(*tag, ObjType::Symbol) => {
                let scrutinee = &f[1];
                let name = self.heap.symbol_name(*tag);
                for v in s.stack.iter_mut().filter(|v| v.term == *scrutinee) {
                    let Some(ty) = v.ty else { continue };
                    if let Ty::Sum(arms) = self.c.arena.get(self.c.arena.resolve(ty)).clone() {
                        let arm: Vec<_> = arms.into_iter().filter(|(l, _)| (self.c.interner.name(*l) == name) == yes).collect();
                        v.ty = Some(self.c.arena.ty(Ty::Sum(arm)));
                    }
                }
            }
            _ => {}
        }
    }
}
