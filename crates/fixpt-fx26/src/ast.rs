//! Descriptions and expressions.
//!
//! **Descriptions** are FX's word for what an expression is *described by* —
//! regions, effects and types, one kind each (`K ::= region | effect | type`).
//! They live in an arena so that a recursive type from `dletrec` can be a
//! cycle of ids, as FX-87's circular types were cycles of conses.
//!
//! **Effects** are kept in normal form: a set of atoms. `pure` is the empty
//! set and `maxeff` is union, so `(maxeff e (maxeff e pure))` and `e` are the
//! same value — the normalisation PLDI '89 relies on when it says the latent
//! effect of `twice`'s inner lambda is `e` (p. 3).

use fixpt_read::{Span, Sym};
use std::collections::BTreeSet;

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Kind {
    Region,
    Effect,
    Type,
}

/// A description variable, bound by `poly`, `plambda` or a projection's
/// substitution. Identity is the number; the name is for printing.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct DVar(pub u32);

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Region {
    /// `@name`.
    Const(Sym),
    Var(DVar),
}

/// One indivisible piece of an effect.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Atom {
    Read(Region),
    Write(Region),
    Alloc(Region),
    /// May not return to its continuation: control may go to a continuation
    /// captured in this region.
    Goto(Region),
    /// May keep its continuation for later use.
    Comefrom(Region),
    /// An effect variable.
    Var(DVar),
}

impl Atom {
    pub fn region(self) -> Option<Region> {
        match self {
            Atom::Read(r) | Atom::Write(r) | Atom::Alloc(r) | Atom::Goto(r) | Atom::Comefrom(r) => {
                Some(r)
            }
            Atom::Var(_) => None,
        }
    }
}

/// An effect in normal form.
#[derive(Clone, PartialEq, Eq, Hash, Default, Debug)]
pub struct Effect(pub BTreeSet<Atom>);

impl Effect {
    pub fn pure() -> Effect {
        Effect::default()
    }
    pub fn atom(a: Atom) -> Effect {
        Effect([a].into_iter().collect())
    }
    pub fn is_pure(&self) -> bool {
        self.0.is_empty()
    }
    pub fn union(&self, other: &Effect) -> Effect {
        Effect(self.0.union(&other.0).copied().collect())
    }
    /// Subeffecting: every atom of `self` is in `other`.
    pub fn within(&self, other: &Effect) -> bool {
        self.0.is_subset(&other.0)
    }
    pub fn contains(&self, a: Atom) -> bool {
        self.0.contains(&a)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct TyId(pub u32);

#[derive(Clone, Debug)]
pub enum Ty {
    /// A type named in the initial environment: `int`, `bool`, `char`,
    /// `string`, `unit`.
    Base(Sym),
    /// The bottom type: the type of a call that never returns — to a
    /// continuation, here — and a subtype of every type.
    Void,
    Var(DVar),
    Subr { effect: Effect, params: Vec<TyId>, result: TyId },
    Poly { binders: Vec<(DVar, Kind)>, body: TyId },
    Ref(TyId, Region),
    Pair(TyId, TyId, Region),
    /// `(prompt-tag A H D R)`: a tag in region `R` whose prompts deliver an
    /// `A`, whose aborts carry an `H`, and whose delimited computations have
    /// effect at most `D`, besides their control effects on `R`.
    PromptTag { answer: TyId, payload: TyId, effect: Effect, region: Region },
    /// `(composable T A D R)`: a composable continuation captured up to a
    /// prompt for a tag of type `(prompt-tag A H D R)`, waiting for a `T`.
    /// It is a subroutine — see [`Ty::as_subr`] — and also a value whose marks
    /// can be read.
    Composable { arg: TyId, answer: TyId, effect: Effect, region: Region },
    /// `(mark-key T R)`: a continuation-mark key in region `R` for marks of
    /// type `T`.
    MarkKey(TyId, Region),
    /// A forwarding slot, for building recursive types: `dletrec` allocates
    /// one per name, parses the bodies against them, then fills them in.
    Link(Option<TyId>),
}

impl Ty {
    /// What calling a value of this type does, if it can be called: its
    /// latent effect, parameters and result. A composable continuation runs
    /// the rest of its prompt's body, so its latent effect is the tag's bound
    /// together with the control effects on the tag's region.
    pub fn as_subr(&self) -> Option<(Effect, Vec<TyId>, TyId)> {
        match self {
            Ty::Subr { effect, params, result } => Some((effect.clone(), params.clone(), *result)),
            Ty::Composable { arg, answer, effect, region } => {
                let mut e = effect.clone();
                e.0.insert(Atom::Goto(*region));
                e.0.insert(Atom::Comefrom(*region));
                Some((e, vec![*arg], *answer))
            }
            _ => None,
        }
    }
}

/// A description in argument position — what `proj` supplies.
#[derive(Clone, Debug)]
pub enum D {
    Region(Region),
    Effect(Effect),
    Type(TyId),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct ExpId(pub u32);

#[derive(Clone, Debug)]
pub enum Exp {
    Var(Sym),
    Int(i64),
    Bool(bool),
    Str(String),
    Unit,
    Lambda { params: Vec<(Sym, TyId)>, body: ExpId },
    App { fun: ExpId, args: Vec<ExpId> },
    PLambda { binders: Vec<(DVar, Kind)>, body: ExpId },
    Proj { body: ExpId, args: Vec<D> },
    If { test: ExpId, then: ExpId, els: ExpId },
    Letrec { bindings: Vec<(Sym, TyId, ExpId)>, body: ExpId },
    /// Derived: `(let ((x e)) b)` is `((lambda ((x T)) b) e)` with `T`
    /// synthesised from `e`.
    Let { bindings: Vec<(Sym, ExpId)>, body: ExpId },
    /// Derived: a sequence, each value but the last discarded.
    Begin(Vec<ExpId>),
    /// `(prompt tag body handler)`: evaluate `body` delimited by a prompt for
    /// `tag`; an abort to `tag` inside it calls `handler` with the value.
    Prompt { tag: ExpId, body: ExpId, handler: ExpId },
}

#[derive(Default)]
pub struct Arena {
    tys: Vec<Ty>,
    exps: Vec<(Span, Exp)>,
    /// Names of description variables, for printing.
    dvar_names: Vec<Sym>,
}

impl Arena {
    pub fn ty(&mut self, t: Ty) -> TyId {
        self.tys.push(t);
        TyId(self.tys.len() as u32 - 1)
    }

    /// Follow forwarding links to the type itself.
    pub fn resolve(&self, mut id: TyId) -> TyId {
        while let Ty::Link(Some(next)) = self.tys[id.0 as usize] {
            id = next;
        }
        id
    }

    pub fn get(&self, id: TyId) -> &Ty {
        &self.tys[self.resolve(id).0 as usize]
    }

    /// The node at `id` itself, without following links.
    pub fn get_raw(&self, id: TyId) -> &Ty {
        &self.tys[id.0 as usize]
    }

    pub fn set_link(&mut self, slot: TyId, to: TyId) {
        self.tys[slot.0 as usize] = Ty::Link(Some(to));
    }

    pub fn exp(&mut self, span: Span, e: Exp) -> ExpId {
        self.exps.push((span, e));
        ExpId(self.exps.len() as u32 - 1)
    }

    pub fn exp_at(&self, id: ExpId) -> &Exp {
        &self.exps[id.0 as usize].1
    }

    pub fn span_of(&self, id: ExpId) -> Span {
        self.exps[id.0 as usize].0
    }

    pub fn dvar(&mut self, name: Sym) -> DVar {
        self.dvar_names.push(name);
        DVar(self.dvar_names.len() as u32 - 1)
    }

    pub fn dvar_name(&self, v: DVar) -> Sym {
        self.dvar_names[v.0 as usize]
    }

    /// How much has been allocated, to [`reset`](Self::reset) to later.
    pub fn mark(&self) -> ArenaMark {
        ArenaMark { tys: self.tys.len(), exps: self.exps.len(), dvars: self.dvar_names.len() }
    }

    /// Forget everything allocated since `mark`. Sound only if nothing older
    /// was changed to point at it since, which holds for a check that is
    /// being thrown away: links are only ever set on slots made in the same
    /// parse.
    pub fn reset(&mut self, mark: ArenaMark) {
        self.tys.truncate(mark.tys);
        self.exps.truncate(mark.exps);
        self.dvar_names.truncate(mark.dvars);
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ArenaMark {
    tys: usize,
    exps: usize,
    dvars: usize,
}
