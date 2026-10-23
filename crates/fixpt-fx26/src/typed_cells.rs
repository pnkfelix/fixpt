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
use fixpt_read::Sym;
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
    /// Each parameter as bound inside the word, if not as declared: the
    /// declared type opened (a `nat`'s size named, an array's length, a
    /// module's abstract types), with the variables opened, which must be
    /// fresh: in no other type of the signature.
    pub inside: Vec<Option<(TyId, Vec<crate::ast::DVar>)>>,
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
    /// Where data made packs abstract types (a module taking in another's,
    /// `include`): each fresh abstract type, with its witness. The values are
    /// checked with each witness in its type's place; the data made has the
    /// type with them abstract.
    pub packs: Vec<(usize, Vec<(crate::ast::DVar, TyId)>)>,
    /// Each region's scope (`letregion`, `letfreeze`, `letrena`,
    /// `letreap`): its first cell, the cell after its last, its form and
    /// its variable. Closed, its effects on it are masked and its value
    /// must not mention it (`letfreeze`: frozen).
    pub regions: Vec<(usize, usize, crate::ast::RegionForm, crate::ast::DVar)>,
    /// Before which cell a `let`'s binding, in which slot, is opened as
    /// checking bound it (an array's length named): its type then, and the
    /// variables opened, fresh.
    pub opens: Vec<(usize, usize, TyId, Vec<crate::ast::DVar>)>,
    /// A standard `vsubr`'s word (`list`'s): its signature the procedure of
    /// one list this type, `(vsubr e t r)`, applies, `(subr e ((listof t
    /// acyclic)) r)`; filled in by `Certs::settle`.
    pub vsubr: Option<TyId>,
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
    /// And each standard `vsubr`'s word's signature, its type unfolded.
    pub fn settle(&mut self, c: &mut Checker) -> Result<(), String> {
        for cert in self.words.values_mut() {
            let Some(t) = cert.vsubr else { continue };
            let Some((effect, params, result)) = unfolded(c, t).and_then(|s| c.arena.get(s).as_subr()) else {
                return Err(format!("a vsubr's word signed {}", c.show_ty(t)));
            };
            (cert.params, cert.result, cert.effect) = (params, Some(result), Some(effect));
        }
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

/// `vsubr` type `t`, unfolded: `(vsubr e t r)` is `(subr e ((listof t
/// acyclic)) r)`.
fn unfolded(c: &mut Checker, t: TyId) -> Option<TyId> {
    match c.arena.get(c.arena.resolve(t)).clone() {
        Ty::Named { which: 0, args } => Some(c.unfold(0, &args)),
        _ => None,
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
    /// What the certificate claimed and the verifier took, unproved: the
    /// built-in scheduler's procedures at their forms' types. The word is
    /// verified relative to these (the design note's §7: trusted).
    pub assumed: Vec<String>,
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
    /// What is known of sizes here, as the checkers keep it
    /// (`crate::sizes::SizeFact`: `lin = 0` or `lin ≥ 0`): learned from the
    /// tests the ways here passed.
    facts: Vec<crate::sizes::SizeFact>,
    /// Blobrefs to a flat sum, each with the variant the tests the ways
    /// here passed found its tag to name.
    variants: Vec<(Term, Sym)>,
}

/// One instruction: where its cell is, its routine's name (or `None`, a
/// word run as a cell), and its operands.
struct Ins {
    at: usize,
    name: Option<&'static str>,
    ops: Vec<Value>,
}

/// The integer `t` is, if it is literals' sum, difference or product: the
/// value a literal written past a fixnum's range (`Checker::big_literal`),
/// or a negative one, is compiled to compute.
fn constant(t: &Term) -> Option<i128> {
    match t {
        Term::Lit(k) if k.is_fixnum() => Some(k.as_fixnum() as i128),
        Term::App(f @ ("+" | "-" | "*"), xs) if xs.len() == 2 => {
            let (a, b) = (constant(&xs[0])?, constant(&xs[1])?);
            match *f {
                "+" => a.checked_add(b),
                "-" => a.checked_sub(b),
                _ => a.checked_mul(b),
            }
        }
        _ => None,
    }
}

/// Whether a certificate's operation note is an instantiation's (of a
/// callee, a value, a `proj`), not a standard operation's.
fn marker(op: &str) -> bool {
    matches!(op, "%call" | "%inst" | "%proj" | "%make" | "%trust" | "%flat" | "%copy")
}

/// Verify `word` against its certificate in `certs`.
pub fn verify(c: &mut Checker, heap: &Heap, certs: &Certs, word: Value) -> Outcome {
    let mut v = Verifier { c, heap, certs, out: Outcome::default(), made: 0, effect: Effect::pure(), proving: Vec::new(), gen_effects: Vec::new(), frames: Vec::new(), region_closures: Vec::new(), relations: Vec::new() };
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
    /// The regions open, innermost last: each one's variable, form, and the
    /// effect so far where it opened (what is added since is its own).
    frames: Vec<(crate::ast::DVar, crate::ast::RegionForm, Effect)>,
    /// The closures `%region-closure` made (an `rlambda`'s): a `plambda`
    /// body that makes one may allocate, and be generalized still
    /// (`Checker::generalizable`).
    region_closures: Vec<Term>,
    /// The integer tests made (`int-eq`, `int-less`): each one's flag's
    /// term, and the sizes it compared (`(= a b)`, `(< a b)`), for what a
    /// branch on it then knows.
    relations: Vec<(Term, crate::ast::Rel, Size, Size)>,
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
        // An integer known here, of a fixed-width type: in its range, as a
        // literal checked against one is (`Checker::literal_in_range`).
        if let (Some((lo, hi)), Some(k)) = (self.c.fixed_expected(t), constant(&v.term))
            && (lo..=hi).contains(&k)
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
        // Two `poly`s over binders of the same kinds (a value checked
        // against the `poly` it is stored as): their bodies compared, the
        // second's binders renamed to the first's, as the checker checks a
        // `plambda` against its signature.
        let (mut s, mut t) = (v.ty?, t);
        loop {
            match (self.c.arena.get(self.c.arena.resolve(s)).clone(), self.c.arena.get(self.c.arena.resolve(t)).clone()) {
                (Ty::Poly { binders: a, body: x }, Ty::Poly { binders: b, body: y })
                    if a.len() == b.len() && a.iter().zip(&b).all(|((_, j), (_, k))| j == k) =>
                {
                    (s, t) = (x, self.c.renamed(y, &b, &a));
                }
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
            // A scalar by its name: `f64` the flat names is the base type.
            Ty::Base(b) if self.c.interner.name(b) == "f64" => self.heap.is_a(x, ObjType::Flonum),
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
        // (Through each parameter as bound inside: a module parameter's
        // abstract types named for it, `o..t`, as the body was checked.)
        let bound: Vec<TyId> = cert.params.iter().enumerate().map(|(i, p)| cert.inside.get(i).and_then(|o| o.as_ref()).map_or(*p, |(t, _)| *t)).collect();
        let given = self.selects(&bound);
        // The signature as written, before its selects are filled in: what
        // an opened variable must not be in.
        let written: Vec<TyId> = cert.params.iter().chain(&cert.frees).chain(cert.result.iter()).copied().collect();
        let mut cert = cert.clone();
        for p in &mut cert.params {
            *p = self.c.instantiate_params(*p, &given);
        }
        cert.result = cert.result.map(|r| self.c.instantiate_params(r, &given));
        let cert = &cert;
        // Each parameter opened as the body binds it: within its declared
        // type, the variables opened fresh.
        let mut slot_types = cert.params.clone();
        for (i, opened) in cert.inside.iter().enumerate() {
            let Some((inner, vars)) = opened else { continue };
            let declared = cert.params[i];
            let inner = self.c.instantiate_params(*inner, &given);
            if vars.iter().any(|v| written.iter().any(|t| self.c.mentions_var(*t, *v))) {
                self.out.failed.push(format!("parameter {i} opened at a variable not fresh"));
                return;
            }
            if !self.c.subtype(inner, declared) {
                let msg = format!("parameter {i} opened as {}, not within {}", self.show(inner), self.show(declared));
                self.out.failed.push(msg);
                return;
            }
            slot_types[i] = inner;
        }
        let entry = State {
            stack: slot_types.iter().enumerate().map(|(i, t)| V::new(Term::Slot(i), Some(*t))).collect(),
            pending: Vec::new(),
            facts: Vec::new(),
            variants: Vec::new(),
        };
        let notes: HashMap<usize, &Vec<Prop>> = cert.notes.iter().map(|(k, p)| (*k, p)).collect();
        // The states waiting at each later cell, from branches to it.
        let mut waiting: HashMap<usize, Vec<State>> = HashMap::new();
        let mut cur = Some(entry.clone());
        let mut i = 0;
        while i < code.len() {
            let ins = &code[i];
            i += 1;
            // The regions that close here: the way out of their bodies.
            cur = match self.close_regions(cert, ins.at, cur) {
                Ok(c) => c,
                Err(()) => return,
            };
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
            if self.generalize(cert, ins.at, &mut s, &at).is_err() || self.instances(cert, ins.at, &mut s, &at).is_err() || self.opens(cert, ins.at, &mut s, &at).is_err() {
                return;
            }
            // The regions that open here, the outermost first.
            // (Among those of one start and end, the certificate lists the
            // inner first, as their ends are met.)
            let mut opening: Vec<(usize, &(usize, usize, crate::ast::RegionForm, crate::ast::DVar))> =
                cert.regions.iter().enumerate().filter(|(_, (start, ..))| *start == ins.at).collect();
            opening.sort_by_key(|(k, (_, end, ..))| (std::cmp::Reverse(*end), std::cmp::Reverse(*k)));
            for (_, (_, _, form, r)) in opening {
                let before = std::mem::replace(&mut self.effect, Effect::pure());
                self.frames.push((*r, *form, before));
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
            match self.flat(&code[i - 1..], cert, &mut s, &at, &waiting) {
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
        // Regions whose bodies left by `return` only, closing past the last
        // cell: their effects masked.
        let past = code.last().map_or(0, |ins| ins.at + 1 + ins.ops.len());
        if self.close_regions(cert, past, None).is_err() {
            return;
        }
        if cur.is_some() {
            self.out.failed.push("the last cell falls through".into());
        }
        if let Some(latent) = &cert.effect {
            let effect = self.masked(&code, cert, &slot_types);
            if !effect.within(latent) {
                let msg = format!("effect {} is not within the latent {}", self.c.show_effect(&effect), self.c.show_effect(latent));
                self.out.open.push(msg);
            }
        }
    }

    /// The word's effect, masked as the checkers mask a lambda's body
    /// (`Checker::mask`): an atom kept if its region is seen from outside,
    /// in the type of something the word is given (a parameter, a free
    /// value, a global its cells name) or a global's own; in its result's
    /// type, only allocation and control; otherwise nothing outside can
    /// tell, and it is dropped.
    fn masked(&mut self, code: &[Ins], cert: &Cert, slot_types: &[TyId]) -> Effect {
        use crate::ast::{Atom, Region};
        let mut seen: Vec<TyId> = slot_types.iter().chain(&cert.frees).copied().collect();
        for ins in code {
            if matches!(ins.name, Some("global" | "global!"))
                && let Some(t) = self.certs.globals.get(&ins.ops[0].raw())
            {
                seen.push(*t);
            }
        }
        let mut visible = std::collections::HashSet::new();
        for t in seen {
            self.c.regions_in(t, &mut visible);
        }
        let mut in_result = std::collections::HashSet::new();
        if let Some(r) = cert.result {
            self.c.regions_in(r, &mut in_result);
        }
        let kept = self
            .effect
            .0
            .iter()
            .copied()
            .filter(|a| match a.region() {
                None => true,
                Some(r @ Region::Frozen(Some(p), _)) if !matches!(a, Atom::Write(_)) => {
                    let place = Region::Var(p);
                    visible.contains(&r) || visible.contains(&place) || ((in_result.contains(&r) || in_result.contains(&place)) && matches!(a, Atom::Alloc(_)))
                }
                Some(Region::Frozen(..)) => true,
                Some(Region::Global(_) | Region::Globals) => true,
                Some(r) if visible.contains(&r) => true,
                Some(r) if in_result.contains(&r) => matches!(a, Atom::Alloc(_) | Atom::Goto(_) | Atom::Comefrom(_)),
                Some(_) => false,
            })
            .collect();
        Effect(kept)
    }

    /// The regions whose scopes end before cell `at`, innermost first, closed
    /// on `cur`, the way out of their bodies: each one's own effect, its
    /// atoms on it masked (none may be `comefrom`: no continuation is
    /// captured into a region that is gone), joined to the effect outside;
    /// the value its body made closed (`close_value`).
    fn close_regions(&mut self, cert: &Cert, at_cell: usize, mut cur: Option<State>) -> Result<Option<State>, ()> {
        let mut ending: Vec<(usize, &(usize, usize, crate::ast::RegionForm, crate::ast::DVar))> =
            cert.regions.iter().enumerate().filter(|(_, (_, end, ..))| *end == at_cell).collect();
        ending.sort_by_key(|(k, (start, ..))| (std::cmp::Reverse(*start), *k));
        for (_, (_, _, _, r)) in ending {
            let at = format!("cell {at_cell}");
            let Some((fr, form, before)) = self.frames.pop() else {
                self.out.failed.push(format!("{at}: a region closes that did not open"));
                return Err(());
            };
            if fr != *r {
                self.out.failed.push(format!("{at}: regions close out of order"));
                return Err(());
            }
            let own = std::mem::replace(&mut self.effect, before);
            let region = crate::ast::Region::Var(*r);
            if own.0.contains(&crate::ast::Atom::Comefrom(region)) {
                self.out.failed.push(format!("{at}: a continuation captured into a region that closes"));
                return Err(());
            }
            let written = own.0.iter().any(|a| matches!(a, crate::ast::Atom::Write(g) | crate::ast::Atom::Init(g) if *g == region));
            let masked = Effect(own.0.iter().copied().filter(|a| a.region() != Some(region)).collect());
            self.effect = self.effect.union(&masked);
            if let Some(s) = cur.as_mut()
                && let Some(v) = s.stack.last_mut()
                && let Some(t) = v.ty
            {
                let t = self.close_value(t, *r, form, written, &at)?;
                v.ty = Some(t);
                v.made = Some(t);
            }
        }
        Ok(cur)
    }

    /// A value leaving region `r`'s scope: of a type that does not mention
    /// it; from a `letfreeze`, one that cannot still write it, `r` frozen
    /// (`acyclic` if the body wrote nothing in it).
    fn close_value(&mut self, t: TyId, r: crate::ast::DVar, form: crate::ast::RegionForm, written: bool, at: &str) -> Result<TyId, ()> {
        let region = crate::ast::Region::Var(r);
        if let crate::ast::RegionForm::Freeze(into) = form {
            if self.c.writes_in(t, region) {
                let msg = format!("{at}: a `letfreeze`'s value that could still write its region: {}", self.show(t));
                self.out.failed.push(msg);
                return Err(());
            }
            let map = HashMap::from([(r, crate::ast::D::Region(crate::ast::Region::Frozen(into, !written)))]);
            return Ok(self.c.subst(t, &map));
        }
        let mut in_t = std::collections::HashSet::new();
        self.c.regions_in(t, &mut in_t);
        if in_t.contains(&region) {
            let msg = format!("{at}: a value of {} leaves its region's scope", self.show(t));
            self.out.failed.push(msg);
            return Err(());
        }
        Ok(t)
    }

    /// A value returned from inside regions still open: closed through
    /// each, the innermost first, as if their scopes ended here.
    fn returned(&mut self, v: &V, at: &str) -> Result<V, ()> {
        let mut v = v.clone();
        for k in (0..self.frames.len()).rev() {
            let (r, form, _) = self.frames[k].clone();
            let region = crate::ast::Region::Var(r);
            let inside = self.frames[k + 1..].iter().fold(self.effect.clone(), |e, (_, _, b)| e.union(b));
            let written = inside.0.iter().any(|a| matches!(a, crate::ast::Atom::Write(g) | crate::ast::Atom::Init(g) if *g == region));
            if let Some(t) = v.ty {
                v.ty = Some(self.close_value(t, r, form, written, at)?);
            }
        }
        Ok(v)
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
            // Pure, as the value restriction has it; or an `rlambda`'s
            // closure, made by allocating only: it holds nothing mutable.
            let rlambda = s.stack.last().is_some_and(|v| self.region_closures.contains(&v.term))
                && self.effect.0.iter().all(|a| matches!(a, crate::ast::Atom::Alloc(_)));
            if !self.effect.0.is_empty() && !rlambda {
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

    /// The `let` bindings opened before cell `at`: each slot's value of a
    /// type with sizes not known (an array's length) taken as one with them
    /// named, fresh: in no type the signature or the state has. Its type,
    /// those named `finite`, must hold the value.
    fn opens(&mut self, cert: &Cert, at_cell: usize, s: &mut State, at: &str) -> Result<(), ()> {
        for (_, slot, opened, vars) in cert.opens.iter().filter(|(k, ..)| *k == at_cell) {
            let Some(v) = s.stack.get(*slot).cloned() else {
                self.out.failed.push(format!("{at}: no slot {slot} to open"));
                return Err(());
            };
            let mut elsewhere: Vec<TyId> = cert.params.iter().chain(&cert.frees).chain(cert.result.iter()).copied().collect();
            elsewhere.extend(s.stack.iter().filter_map(|w| w.ty));
            if vars.iter().any(|x| elsewhere.iter().any(|t| self.c.mentions_var(*t, *x))) {
                self.out.failed.push(format!("{at}: slot {slot} opened at a variable not fresh"));
                return Err(());
            }
            let unnamed: HashMap<crate::ast::DVar, crate::ast::D> = vars.iter().map(|x| (*x, crate::ast::D::Size(Size::Finite))).collect();
            let unopened = self.c.subst(*opened, &unnamed);
            self.holds(&v, unopened, at);
            for w in s.stack.iter_mut().filter(|w| w.term == v.term) {
                w.ty = Some(*opened);
                w.made = Some(*opened);
            }
        }
        Ok(())
    }

    /// The values instantiated before cell `at`, on top, in the order made:
    /// `%inst`, every binder (outermost first, as checking found them);
    /// `%proj`, the outermost level's, at its arguments.
    fn instances(&mut self, cert: &Cert, at_cell: usize, s: &mut State, at: &str) -> Result<(), ()> {
        // A trusted claim: the value on top taken at the type it names, an
        // assumption.
        for (_, _, ds) in cert.ops.iter().filter(|(k, op, _)| *k == at_cell && op == "%trust") {
            let ([crate::ast::D::Type(t)], Some(top)) = (&ds[..], s.stack.last_mut()) else {
                self.out.failed.push(format!("{at}: a trusted claim of nothing"));
                return Err(());
            };
            top.ty = Some(*t);
            top.made = Some(*t);
            let msg = format!("{at}: the scheduler's procedure at its form's type, {}", self.show(*t));
            self.out.assumed.push(msg);
        }
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

    /// A bloblet's suffix or a blobref read, written or moved (`TODO.md`
    /// §77), as the compiler runs it (`Compiler::bloblet`): the checker's
    /// own rule for the form (`Checker::blobref_rule`), on the operands'
    /// types, and the operand the compiler gives the primitive for the
    /// layout the same as the rule's. A new blobref's flat is the one the
    /// certificate says (`%flat`), which the type it was checked against
    /// said; its bytes checked to lie in the suffix, at run time, by the
    /// cells after it (`%fx26-suffix-fits`), no branch landing between. How
    /// many instructions it is, or none if the first is no such primitive.
    fn flat(&mut self, code: &[Ins], cert: &Cert, s: &mut State, at: &str, waiting: &HashMap<usize, Vec<State>>) -> Option<Result<usize, ()>> {
        use crate::ast::{Atom, BlobletOp};
        use crate::check::Datum;
        let ins = &code[0];
        if ins.name != Some("prim") {
            return None;
        }
        let pname = fixpt_runtime::PRIMITIVES.get(ins.ops[0].as_fixnum() as usize).map(|d| d.name)?;
        let n = ins.ops[1].as_fixnum() as usize;
        let op = match (pname, n) {
            ("%suffix-ref", 2) => BlobletOp::RefAt,
            ("%suffix-ref+", 2) => BlobletOp::RefAdd,
            ("%suffix-ref-owner", 1) => BlobletOp::RefOwner,
            ("%suffix-ref-offset", 1) => BlobletOp::RefOffset,
            ("%fx26-suffix-ref-index", 3) => BlobletOp::RefIndex,
            ("%fx26-suffix-ref-length", 2) => BlobletOp::RefLength,
            ("%fx26-suffix-ref-get", 2) => BlobletOp::RefGet,
            ("%fx26-suffix-ref-set!", 3) => BlobletOp::RefSet,
            ("%fx26-flat-variant!", 3) => BlobletOp::RefVariant,
            ("%bloblet-byte", 2) => BlobletOp::Byte,
            ("%bloblet-set-byte!", 3) => BlobletOp::SetByte,
            ("%bloblet-bytes", 1) => BlobletOp::Bytes,
            ("%bloblet-set!", 3) => BlobletOp::Set(0),
            ("%fx26-flat-tag", 2) => return Some(self.flat_tag(s, at).map(|()| 1)),
            // A flat sum's tag that no arm has: an error at run time.
            ("%fx26-flat-no-arm", 1) => {
                let _ = self.pop(s, at).ok()?;
                let void = self.c.void;
                self.push_made(s, Some(void), None);
                return Some(Ok(1));
            }
            _ => return None,
        };
        let int = self.c.int;
        let mut vals = Vec::new();
        for _ in 0..n {
            vals.push(self.pop(s, at).ok()?);
        }
        vals.reverse();
        let fail = |me: &mut Self, why: String| {
            me.out.failed.push(format!("{at}: {why}"));
            Some(Err(()))
        };
        // A bloblet's own: its suffix's bytes, or a field written.
        if matches!(op, BlobletOp::Byte | BlobletOp::SetByte | BlobletOp::Bytes | BlobletOp::Set(_)) {
            let Some(Ty::Bloblet { fields, frozen, region }) = self.ty_of(&vals[0]) else {
                return fail(self, format!("{pname} of no bloblet"));
            };
            let result = match op {
                BlobletOp::Bytes => Some(int),
                BlobletOp::Byte => {
                    self.holds(&vals[1], int, at);
                    self.effect = self.effect.union(&Effect::atom(Atom::Read(region)));
                    Some(int)
                }
                BlobletOp::SetByte => {
                    self.holds(&vals[1], int, at);
                    self.holds(&vals[2], int, at);
                    self.effect = self.effect.union(&Effect::atom(Atom::Write(region)));
                    None
                }
                _ => {
                    let field = match vals[1].term {
                        Term::Lit(k) if k.is_fixnum() && k.as_fixnum() >= 2 => fields.get(k.as_fixnum() as usize - 2).copied(),
                        _ => None,
                    };
                    let Some(t) = field.filter(|_| !frozen) else {
                        return fail(self, "a bloblet's field written, of no field it has, or frozen".into());
                    };
                    self.holds(&vals[2], t, at);
                    self.effect = self.effect.union(&Effect::atom(Atom::Write(region)));
                    None
                }
            };
            // What a mutator gives is dropped (`unit_after`): of no type.
            self.push_made(s, result, None);
            return Some(Ok(1));
        }
        let Some(xt) = vals[0].ty else {
            return fail(self, format!("{pname} of a value of no known type"));
        };
        // A blobref moved by a literal, with no flat said: to a flat
        // product's field at that offset, or to the variant of a flat sum
        // the tag was found to be (`tagcase`).
        let wanted = cert.ops.iter().find(|(k, op, _)| *k == ins.at && op == "%flat").map(|(_, _, ds)| ds.clone());
        if op == BlobletOp::RefAdd && wanted.is_none() {
            let (Some((b, f)), Term::Lit(k)) = (self.c.blobref_parts(xt), &vals[1].term) else {
                return fail(self, "a blobref moved, to no flat said".into());
            };
            let k = k.as_fixnum();
            let g = match self.c.arena.get(self.c.arena.resolve(f)).clone() {
                Ty::Product(ps) => ps.iter().find_map(|(l, _)| self.c.flat_field(f, *l).filter(|(o, _)| *o as i64 == k).map(|(_, g)| g)),
                _ => match (self.c.flat_sum_layout(f), s.variants.iter().find(|(t, _)| *t == vals[0].term)) {
                    (Some((code, _, _, variants)), Some((_, l))) if code >> 8 == k => variants.iter().find(|(m, _)| m == l).map(|(_, g)| *g),
                    _ => None,
                },
            };
            let Some(g) = g else {
                return fail(self, format!("a {} moved {k} bytes, to no field or variant known", self.show(xt)));
            };
            let t = self.c.blobref_of(b, g);
            self.push_made(s, Some(t), None);
            return Some(Ok(1));
        }
        let wanted = match wanted.as_deref() {
            Some([crate::ast::D::Type(t)]) => self.c.blobref_parts(*t).map(|(_, f)| f),
            _ => None,
        };
        // A variant's label, and whether it is a number.
        let label = match (op, &vals.get(2).map(|v| &v.term)) {
            (BlobletOp::RefVariant, Some(Term::Lit(l))) if self.heap.is_a(*l, ObjType::Symbol) => Some((self.c.interner.intern(&self.heap.symbol_name(*l)), false)),
            (BlobletOp::RefVariant, Some(Term::Lit(l))) if l.is_fixnum() => Some((self.c.interner.intern(&l.as_fixnum().to_string()), true)),
            _ => None,
        };
        let rule = match self.c.blobref_rule(op, xt, wanted, label) {
            Ok(r) => r,
            Err((_, why)) => return fail(self, why),
        };
        // The operands after the first: the layout's, which the compiler
        // gives after the index and before the rest (`Compiler::bloblet`),
        // and the form's own; a variant's label is the form's, not a value
        // of a type.
        let (given, rest): (Option<&V>, Vec<&V>) = match op {
            BlobletOp::RefIndex => (Some(&vals[2]), vec![&vals[1]]),
            BlobletOp::RefLength | BlobletOp::RefGet | BlobletOp::RefVariant => (Some(&vals[1]), Vec::new()),
            BlobletOp::RefSet => (Some(&vals[1]), vec![&vals[2]]),
            _ => (None, vals[1..].iter().collect()),
        };
        if let Some(d) = rule.datum.filter(|d| !matches!(d, Datum::Fits(_)))
            && given.map(|v| &v.term) != Some(&Term::Lit(Value::fixnum(d.operand())))
        {
            return fail(self, format!("{pname} given another layout than its, {}", d.operand()));
        }
        if rest.len() != rule.rest.len() {
            return fail(self, format!("{pname} with {} values", n));
        }
        for (v, t) in rest.into_iter().zip(&rule.rest) {
            self.holds(v, *t, at);
        }
        for a in &rule.effect {
            self.effect = self.effect.union(&Effect::atom(a.clone()));
        }
        self.push_made(s, Some(rule.result), None);
        // A new blobref's bytes checked to lie in the suffix, where it
        // takes more than the one its offset already does.
        match rule.datum {
            Some(Datum::Fits(size)) if size > 1 => {
                let fits = |ins: &Ins| {
                    ins.name == Some("prim")
                        && ins.ops[1].as_fixnum() == 2
                        && fixpt_runtime::PRIMITIVES.get(ins.ops[0].as_fixnum() as usize).is_some_and(|d| d.name == "%fx26-suffix-fits")
                };
                let checked = matches!(code, [_, k, f, ..] if k.name == Some("lit") && k.ops[0] == Value::fixnum(size as i64) && fits(f))
                    && code[1..3].iter().all(|ins| !waiting.contains_key(&ins.at));
                if !checked {
                    return fail(self, format!("a new blobref of {size} bytes, not checked to fit"));
                }
                Some(Ok(3))
            }
            _ => Some(Ok(1)),
        }
    }

    /// `( r k -- tag )`: a flat sum's tag, read from the blobref `r` to it
    /// by the layout's code `k` (`Checker::flat_sum_layout`), of the
    /// owner's region; a test of it teaches which variant `r` points to
    /// (`narrow`).
    fn flat_tag(&mut self, s: &mut State, at: &str) -> Result<(), ()> {
        let (k, r) = (self.pop(s, at)?, self.pop(s, at)?);
        let layout = r.ty.and_then(|t| self.c.blobref_parts(t)).and_then(|(b, f)| Some((b, self.c.flat_sum_layout(f)?.0)));
        let Some((b, _)) = layout.filter(|(_, code)| k.term == Term::Lit(Value::fixnum(*code))) else {
            self.out.failed.push(format!("{at}: a flat sum's tag, of no flat sum, or by another layout"));
            return Err(());
        };
        match self.c.arena.get(self.c.arena.resolve(b)).clone() {
            Ty::Bloblet { region, .. } => self.reads(region),
            _ => {
                self.out.failed.push(format!("{at}: a flat sum's tag, of an owner of no region known"));
                return Err(());
            }
        }
        s.stack.push(V::new(Term::App("flat-tag", vec![r.term]), None));
        Ok(())
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
        // The facts every way in has.
        let facts = first.facts.iter().filter(|f| arriving.iter().all(|s| s.facts.iter().any(|g| g.eq == f.eq && g.lin == f.lin))).cloned().collect();
        let variants = first.variants.iter().filter(|v| arriving.iter().all(|s| s.variants.contains(v))).cloned().collect();
        Some(State { stack, pending: first.pending.clone(), facts, variants })
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
        self.join(&ways, at).unwrap_or(State { stack: Vec::new(), pending: Vec::new(), facts: Vec::new(), variants: Vec::new() })
    }

    fn pop(&mut self, s: &mut State, at: &str) -> Result<V, ()> {
        s.stack.pop().ok_or_else(|| self.out.failed.push(format!("{at}: the stack is empty")))
    }

    fn push_made(&mut self, s: &mut State, ty: Option<TyId>, term: Option<Term>) {
        let term = term.unwrap_or_else(|| self.fresh());
        s.stack.push(V::new(term, ty));
    }

    /// `v`'s size, if it is a natural of a known one, or a literal.
    fn size_of(&self, v: &V) -> Option<Size> {
        if let Term::Lit(k) = v.term
            && k.is_fixnum()
            && k.as_fixnum() >= 0
        {
            return Some(Size::lit(k.as_fixnum()));
        }
        match self.ty_of(v) {
            Some(Ty::Nat(s)) if !matches!(s, Size::Finite) => Some(s),
            _ => None,
        }
    }

    /// `f` asked of the checker with `facts` as what it knows of sizes: its
    /// own procedures for them (`size_nonneg`, Fourier–Motzkin), on the
    /// facts the ways here learned.
    fn with_facts<T>(&mut self, facts: &[crate::sizes::SizeFact], f: impl FnOnce(&mut Checker) -> T) -> T {
        let outer = std::mem::replace(&mut self.c.size_facts, facts.to_vec());
        let r = f(self.c);
        self.c.size_facts = outer;
        r
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
                // as `nat_arith` does, a difference only where what is known
                // here shows it no less than 0.
                let ty = match (self.size_of(&a), self.size_of(&b)) {
                    (Some(x), Some(y)) => match self.with_facts(&s.facts, |c| c.nat_arith(f, &x, &y)) {
                        Some(n) => Some(self.c.arena.ty(Ty::Nat(n))),
                        None => Some(int),
                    },
                    _ => Some(int),
                };
                self.push_made(s, ty, Some(Term::App(f, vec![a.term, b.term])));
            }
            "int-less" | "int-eq" => {
                let (b, a) = (self.pop(s, at)?, self.pop(s, at)?);
                self.holds(&a, int, at);
                self.holds(&b, int, at);
                let f = if name == "int-less" { "<" } else { "=" };
                let flag = Term::App(f, vec![a.term.clone(), b.term.clone()]);
                if let (Some(x), Some(y)) = (self.size_of(&a), self.size_of(&b)) {
                    let rel = if name == "int-less" { crate::ast::Rel::Lt } else { crate::ast::Rel::Eq };
                    self.relations.push((flag.clone(), rel, x, y));
                }
                self.push_made(s, Some(bool_), Some(flag));
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
                    let called = self.returned(&V::new(Term::App("call", vec![f.term]), Some(result)), at)?;
                    match cert.result {
                        Some(want) => self.holds(&called, want, at),
                        None => self.out.failed.push(format!("{at}: a tail call from a word with no result")),
                    }
                    return Ok(None);
                }
                self.push_made(s, Some(result), None);
            }
            "return" => {
                let r = self.pop(s, at)?;
                let r = self.returned(&r, at)?;
                match cert.result {
                    Some(want) => self.holds(&r, want, at),
                    None => self.out.failed.push(format!("{at}: a return from a word with no result")),
                }
                return Ok(None);
            }
            "exit" => return Ok(None),
            // `( tag handler thunk -- r )`: the tag's type says the rest.
            "prompt" => {
                let (thunk, handler, tag) = (self.pop(s, at)?, self.pop(s, at)?, self.pop(s, at)?);
                // A `prompt-tag`'s bound on what the body does; an escape-only
                // tag's, none (`ESCAPE_TAG`), as `synth_prompt` has them.
                let (answer, payload, effect) = match self.ty_of(&tag) {
                    Some(Ty::PromptTag { answer, payload, effect, .. }) => (answer, payload, effect),
                    Some(Ty::Named { which: crate::check::ESCAPE_TAG_INDEX, args }) => match args[..] {
                        [crate::ast::D::Type(a), crate::ast::D::Type(h), _] => (a, h, Effect::pure()),
                        _ => unreachable!("an escape tag's three descriptions"),
                    },
                    _ => {
                        self.out.stopped = Some("a prompt whose tag's type is not known".into());
                        return Err(());
                    }
                };
                let subr = |me: &Self, v: &V| v.ty.and_then(|t| me.c.arena.get(me.c.arena.resolve(t)).as_subr());
                match (subr(self, &thunk), subr(self, &handler)) {
                    (Some((te, tps, tr)), Some((he, hps, hr))) if tps.is_empty() && hps.len() == 1 => {
                        for (r, what) in [(tr, "the prompt's thunk's result"), (hr, "its handler's result")] {
                            self.holds(&V::new(Term::App("result", Vec::new()), Some(r)), answer, &format!("{at}: {what}"));
                        }
                        self.holds(&V::new(Term::App("payload", Vec::new()), Some(payload)), hps[0], &format!("{at}: the handler's parameter"));
                        self.effect = self.effect.union(&te).union(&he).union(&effect);
                    }
                    _ => {
                        self.out.failed.push(format!("{at}: a prompt's thunk or handler is no procedure of the arity it must be"));
                        return Err(());
                    }
                }
                self.push_made(s, Some(answer), None);
            }
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
                    // A module's values, as the type made lists them: its
                    // items' product (an `include`'s value the module
                    // included), or its own, picked from that by the paths
                    // checking found, each value checked here as it is.
                    (Term::Lit(k), Ty::Module { vals: vs, .. }) if *k == Value::fixnum(37) => Some(vs.iter().map(|(_, t)| *t).collect()),
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
                // Its layout: its own type's, or, a module checked against a
                // type of fewer values (width), that type's, picked into.
                let (fields, layout) = match fields.filter(|f| f.len() == vals.len()) {
                    Some(f) => (f, own),
                    None => match self.c.arena.get(self.c.arena.resolve(t)).clone() {
                        Ty::Module { vals: vs, .. } if vs.len() == vals.len() && own != t => (vs.iter().map(|(_, t)| *t).collect(), t),
                        _ => {
                            let msg = format!("{at}: {} values made a {}", vals.len(), self.show(own));
                            self.out.failed.push(msg);
                            return Err(());
                        }
                    },
                };
                // Each value at its field's type, its packed abstract types
                // their witnesses.
                let packs: HashMap<crate::ast::DVar, crate::ast::D> =
                    cert.packs.iter().filter(|(k, _)| *k == here).flat_map(|(_, ps)| ps.iter().map(|(w, x)| (*w, crate::ast::D::Type(*x)))).collect();
                for (v, f) in vals.iter().zip(&fields) {
                    let f = if packs.is_empty() { *f } else { self.c.subst(*f, &packs) };
                    self.holds(v, f, at);
                }
                if layout == t {
                    self.push_made(s, Some(t), None);
                    return Ok(Some(s.clone()));
                }
                // Made as its own type (or the values picked), which must be
                // within the one it is taken as: module subtyping, which
                // packs an abstract type with the type the module gives it
                // (`counter..t` for `t`).
                if own != t {
                    let made = V::new(Term::Made(0), Some(own));
                    self.holds(&made, t, at);
                }
                self.push_made(s, Some(t), None);
            }
            "prim" | "cons" | "abort" | "callcc" | "callcomp" | "callone" | "withmark" | "withmark-tail" | "firstmark" | "currentmarks" | "marksof"
                if cert.ops.iter().any(|(k, op, _)| *k == here && !marker(op)) =>
            {
                let (_, op, inst) = cert.ops.iter().find(|(k, op, _)| *k == here && !marker(op)).expect("found").clone();
                let pname = match name {
                    "prim" => fixpt_runtime::PRIMITIVES.get(ops[0].as_fixnum() as usize).map_or("?", |d| d.name),
                    other => other,
                };
                // The cell must run the operation, as the compilers' table
                // has it (`lower::STANDARD`; the few the compiler runs by
                // their own names; and control, each its routine,
                // `Compiler::standard_on`).
                let runs = pname == op
                    || crate::cellular::standard_primitive(&op) == Some(pname)
                    || matches!(
                        (op.as_str(), pname),
                        ("new", "%make-box")
                            | ("char->string", "string")
                            | ("abort-current-continuation" | "escape", "abort")
                            | ("cwcc", "callcc")
                            | ("call-with-composable-continuation", "callcomp")
                            | ("call-with-oneshot-continuation", "callone")
                            | ("with-mark", "withmark" | "withmark-tail")
                            | ("first-mark", "firstmark")
                            | ("current-marks", "currentmarks")
                            | ("marks-of", "marksof")
                    );
                if !runs {
                    self.out.failed.push(format!("{at}: said to run `{op}`, and runs {pname}"));
                    return Err(());
                }
                // A routine takes as many values as the operation has
                // parameters; `prim` says how many, `cons` two.
                let n = match name {
                    "prim" => ops[1].as_fixnum() as usize,
                    "cons" => 2,
                    _ => match self.op_type(&op, &inst, 0, cert.own_ops.contains(&here)) {
                        Some((params, _, _)) => params.len(),
                        None => 0,
                    },
                };
                // `(certify-length v k)`: `v` as the `nlist` of length `k` a
                // test of its length has just found it (`narrow`'s
                // `Prop::Length`), its region acyclic, as the checker types it
                // (`synth_app`); at run time, `v`.
                if op == "certify-length" && n == 2 {
                    let (k, v) = (self.pop(s, at)?, self.pop(s, at)?);
                    let found = match (self.ty_of(&v), self.size_of(&k)) {
                        (Some(Ty::NList { elem, size, region }), Some(n)) if size == n => Some((elem, size, region)),
                        _ => None,
                    };
                    let Some((elem, size, region)) = found else {
                        self.out.failed.push(format!("{at}: a length certified that no test found"));
                        return Err(());
                    };
                    let region = match region {
                        crate::ast::Region::Frozen(p, _) => crate::ast::Region::Frozen(p, true),
                        r => r,
                    };
                    let t = self.c.arena.ty(Ty::NList { elem, size, region });
                    self.push_made(s, Some(t), Some(v.term));
                    return Ok(Some(s.clone()));
                }
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
                // In tail position: its result is the word's.
                if name == "withmark-tail" {
                    match cert.result {
                        Some(want) => self.holds(&V::new(Term::App("with-mark", Vec::new()), Some(result)), want, at),
                        None => self.out.failed.push(format!("{at}: a tail call from a word with no result")),
                    }
                    return Ok(None);
                }
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
                match pname {
                    // An arena or a reap entered: its place, the region
                    // open innermost.
                    "%region-enter" | "%reap-enter" => match self.frames.last() {
                        Some((r, form, _)) if form.enter() == Some(pname) => {
                            let place = self.c.arena.ty(Ty::Place(crate::ast::Region::Var(*r)));
                            self.push_made(s, Some(place), None);
                        }
                        _ => {
                            self.out.failed.push(format!("{at}: {pname} where no such region opens"));
                            return Err(());
                        }
                    },
                    // An `rlambda`'s closure, made in a place: `( place fv … w
                    // -- c )`, as `closure`'s, its type's latent effect
                    // reading the place's region (calling it reads the
                    // closure), making it allocating there.
                    "%region-closure" => {
                        let n = ops[1].as_fixnum() as usize;
                        let w = self.pop(s, at)?;
                        let Term::Lit(word) = w.term else {
                            self.out.failed.push(format!("{at}: a region closure over no word"));
                            return Err(());
                        };
                        let Some(callee) = self.certs.words.get(&word.raw()).cloned() else {
                            self.out.stopped = Some("a closure over a word with no certificate".into());
                            return Err(());
                        };
                        let mut vals = Vec::new();
                        for _ in 0..n.saturating_sub(2) {
                            vals.push(self.pop(s, at)?);
                        }
                        vals.reverse();
                        let place = self.pop(s, at)?;
                        let Some(Ty::Place(region)) = self.ty_of(&place) else {
                            self.out.failed.push(format!("{at}: a region closure made in no place"));
                            return Err(());
                        };
                        if callee.frees.len() != vals.len() {
                            self.out.failed.push(format!("{at}: a closure over {} values, of a word that has {}", vals.len(), callee.frees.len()));
                            return Err(());
                        }
                        let made = self.fresh();
                        for (j, (v, t)) in vals.iter().zip(&callee.frees).enumerate() {
                            if v.term == Term::Lit(Value::FALSE) && self.fits(v, *t) != Some(true) {
                                s.pending.push((made.clone(), j, *t));
                            } else {
                                self.holds(v, *t, at);
                            }
                        }
                        let mut cert = callee.clone();
                        cert.effect = cert.effect.map(|e| e.union(&Effect::atom(crate::ast::Atom::Read(region))));
                        let ty = self.subr_of(&cert);
                        self.effect = self.effect.union(&Effect::atom(crate::ast::Atom::Alloc(region)));
                        self.region_closures.push(made.clone());
                        self.push_made(s, ty, Some(made));
                    }
                    // `( v place -- v )`: left, keeping the body's value.
                    "%region-exit" => {
                        let (v, place) = (self.pop(s, at)?, self.pop(s, at)?);
                        match (self.ty_of(&place), self.frames.last()) {
                            (Some(Ty::Place(crate::ast::Region::Var(g))), Some((r, _, _))) if g == *r => s.stack.push(v),
                            _ => {
                                self.out.failed.push(format!("{at}: %region-exit of no region open"));
                                return Err(());
                            }
                        }
                    }
                    // A list copied (`list`'s, `apply`'s): fresh, so of any
                    // region, and of elements of any type the original's
                    // are within, as the certificate says (`%copy`); the
                    // original read. A cyclic one is an error at run time.
                    "%fx26-list-copy" => {
                        let v = self.pop(s, at)?;
                        // Said as a list type, or as the `vsubr` it is given
                        // to, by its descriptions (`apply`'s): the list that
                        // one takes.
                        let said = cert.ops.iter().find(|(k, op, _)| *k == here && op == "%copy").map(|(_, _, ds)| ds.clone());
                        let want = match said.as_deref() {
                            Some([crate::ast::D::Type(t)]) => Some(*t),
                            Some(ds @ [_, _, _]) => {
                                let vsubr = self.c.arena.ty(Ty::Named { which: 0, args: ds.to_vec() });
                                unfolded(self.c, vsubr).and_then(|u| self.c.arena.get(u).as_subr()).and_then(|(_, ps, _)| ps.first().copied())
                            }
                            _ => None,
                        };
                        let parts = |me: &Self, t: TyId| match me.c.arena.get(me.c.arena.resolve(t)).clone() {
                            Ty::Pair(e, _, r, true) | Ty::NList { elem: e, region: r, .. } => Some((Some(e), r)),
                            Ty::Nil => Some((None, crate::ast::Region::Frozen(None, true))),
                            _ => None,
                        };
                        let (Some(want), Some((from, g))) = (want, v.ty.and_then(|t| parts(self, t))) else {
                            self.out.failed.push(format!("{at}: a list copied, of no list, or to no list type said"));
                            return Err(());
                        };
                        let Some((Some(to), r)) = parts(self, want) else {
                            self.out.failed.push(format!("{at}: a list copied to a {}", self.show(want)));
                            return Err(());
                        };
                        if let Some(from) = from {
                            self.holds(&V::new(Term::App("element", vec![v.term.clone()]), Some(from)), to, at);
                        }
                        self.reads(g);
                        if !r.is_frozen() {
                            self.effect = self.effect.union(&Effect::atom(crate::ast::Atom::Alloc(r)));
                        }
                        self.push_made(s, Some(want), None);
                    }
                    // A procedure of one list made a `vsubr`, which gives it
                    // the list of its arguments: `(vsubr e t r)` is
                    // `(subr e ((listof t acyclic)) r)`.
                    "%fx26-vlambda" => {
                        let v = self.pop(s, at)?;
                        // Over a polymorphic word (`list`'s): a `vsubr` under
                        // the same binders.
                        let mut levels = Vec::new();
                        let mut inner = v.ty;
                        while let Some(Ty::Poly { binders, body }) = inner.map(|t| self.c.arena.get(self.c.arena.resolve(t)).clone()) {
                            levels.push(binders);
                            inner = Some(body);
                        }
                        let parts = inner.and_then(|t| self.c.arena.get(self.c.arena.resolve(t)).as_subr()).and_then(|(e, ps, r)| match ps[..] {
                            [l] => match self.c.arena.get(self.c.arena.resolve(l)) {
                                Ty::Pair(t, ..) => Some((e, *t, r)),
                                _ => None,
                            },
                            _ => None,
                        });
                        let Some((e, t, r)) = parts else {
                            self.out.failed.push(format!("{at}: a vsubr made of no procedure of a list"));
                            return Err(());
                        };
                        let vsubr = self.c.arena.ty(Ty::Named { which: 0, args: vec![crate::ast::D::Effect(e), crate::ast::D::Type(t), crate::ast::D::Type(r)] });
                        let as_subr = unfolded(self.c, vsubr).expect("a vsubr");
                        self.holds(&V::new(v.term.clone(), inner), as_subr, at);
                        let made = levels.into_iter().rev().fold(vsubr, |body, binders| self.c.arena.ty(Ty::Poly { binders, body }));
                        self.push_made(s, Some(made), None);
                    }
                    _ => {
                        self.out.stopped = Some(format!("prim {pname}"));
                        return Err(());
                    }
                }
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
            Ty::Module { vals, .. } if k >= 2 && k - 2 < vals.len() => Ok(Some(vals[k - 2].1)),
            // A `vsubr`, `%vlambda`'s closure: its free value the procedure
            // of one list it applies (`apply`'s idiom).
            Ty::Named { which: 0, .. } if k == CLOSURE_FREE0 => Ok(unfolded(self.c, o.ty.expect("known"))),
            _ => {
                fail(self);
                Err(())
            }
        }
    }

    /// What a branch on `flag` tells the way where it is true (`yes`) or
    /// false: narrowing, from what the flag's term says it tested.
    fn narrow(&mut self, flag: &Term, yes: bool, s: &mut State) {
        // An integer test of sizes: what it holding, or not, says of them,
        // as the checkers' facts (`sizes.rs`'s `rel_facts`).
        if let Some((_, rel, a, b)) = self.relations.iter().find(|(t, ..)| t == flag).cloned() {
            use crate::ast::Rel;
            let ge = |lin: Size| crate::sizes::SizeFact { lin, eq: false };
            let learned: Vec<crate::sizes::SizeFact> = match (rel, yes) {
                (Rel::Eq, true) => vec![crate::sizes::SizeFact { lin: a.add_scaled(&b, -1), eq: true }],
                // Not equal, a natural and 0: the natural at least 1.
                (Rel::Eq, false) if b == Size::lit(0) => vec![ge(a.plus(-1))],
                (Rel::Eq, false) if a == Size::lit(0) => vec![ge(b.plus(-1))],
                (Rel::Eq, false) => Vec::new(),
                (Rel::Lt, true) => vec![ge(b.add_scaled(&a, -1).plus(-1))],
                (Rel::Lt, false) => vec![ge(a.add_scaled(&b, -1))],
                (Rel::Le, true) => vec![ge(b.add_scaled(&a, -1))],
                (Rel::Le, false) => vec![ge(a.add_scaled(&b, -1).plus(-1))],
                // (The verifier's tests make no `≠`; `int-eq` false is it.)
                (Rel::Ne, _) => Vec::new(),
            };
            s.facts.extend(learned.into_iter().filter(|f| !matches!(f.lin, Size::Finite)));
            return;
        }
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
                // `(acyclic i)`: argument `i`'s frozen data has no cycle, its
                // regions acyclic (what `certify-acyclic` then says).
                if let crate::ast::Prop::Acyclic(i) = p
                    && let Some(x) = args.get(i).cloned()
                {
                    for v in s.stack.iter_mut().filter(|v| v.term == x) {
                        if let Some(t) = v.ty {
                            v.ty = Some(self.c.finitized(t));
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
            // A flat sum's tag: the variant named, where true.
            (Term::App("flat-tag", r), Term::Lit(l)) if yes => {
                let label = match *l {
                    l if l.is_fixnum() => l.as_fixnum().to_string(),
                    l if self.heap.is_a(l, ObjType::Symbol) => self.heap.symbol_name(l).to_string(),
                    _ => return,
                };
                let label = self.c.interner.intern(&label);
                s.variants.push((r[0].clone(), label));
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
