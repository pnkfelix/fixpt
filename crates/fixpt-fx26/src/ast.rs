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
    /// A place, where data is allocated; every place is also a region
    /// (`docs/research/places-and-regions.md`).
    Place,
    Effect,
    Type,
    /// A type whose values are data: structural, immutable, not generative,
    /// holding no procedure; what may be read, printed, checked for cycles
    /// and sent (`docs/research/generative-types.md`, §3). Every data type
    /// is a type.
    Data,
    /// A list's length (`docs/research/sizes.md`): a natural, or `finite`.
    Size,
    /// How a procedure is called (`docs/research/native-conventions.md`).
    Conv,
}

/// How a procedure is called: a cellular closure, run by an inner
/// interpreter; native code, run by being called; either of FX-26's own,
/// which a call finds out from the value (`fx`); or a variable of kind
/// `conv` (`docs/research/native-conventions.md`).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Conv {
    Cellular,
    Native,
    Fx,
    Var(DVar),
}

impl Conv {
    /// Whether a procedure called in `self` may be used as one called in
    /// `want`: the same convention, or any of FX-26's own as `fx`.
    pub fn fits(self, want: Conv) -> bool {
        self == want || (want == Conv::Fx && !matches!(self, Conv::Var(_)))
    }
}

impl Kind {
    /// Whether a description of kind `self` may stand where one of kind
    /// `want` is expected: the same kind, or a place for a region.
    pub fn fits(self, want: Kind) -> bool {
        self == want || (self == Kind::Place && want == Kind::Region) || (self == Kind::Data && want == Kind::Type)
    }
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
    /// `(const p)`: the region of data frozen into place `p` (`const`,
    /// `None`, for the heap), which nothing may write; what a `letfreeze`
    /// gives its region's data as it ends. Reading it, and making data at
    /// it, are pure; it won't outlive `p` (`docs/research/places-and-regions.md`).
    /// `(finite p)`, when the flag is set: frozen data that was never
    /// written, only built, and so is finite: no cycle runs through it.
    Frozen(Option<DVar>, bool),
    /// `heap`: the collected heap, a place that never ends.
    Heap,
    /// `(globals g)`: the binding of the global `g`, which reading `g` reads
    /// and defining it writes. Only in effects: `(read (globals f g))` is
    /// `(maxeff (read (globals f)) (read (globals g)))`.
    Global(Sym),
    /// `@globals`: every global's binding, past and future; each
    /// `(globals g)` is within it.
    Globals,
}

impl Region {
    /// `a ≤ b` for frozen data: the same, or finite data seen as possibly
    /// cyclic, in one place.
    pub fn frozen_le(a: Region, b: Region) -> bool {
        a == b || matches!((a, b), (Region::Frozen(p, true), Region::Frozen(q, false)) if p == q)
    }

    /// Whether this is frozen data's region, in whatever place.
    pub fn is_frozen(self) -> bool {
        matches!(self, Region::Frozen(..))
    }

    /// Whether this is globals' bindings: `(globals g)` or `@globals`.
    pub fn is_globals(self) -> bool {
        matches!(self, Region::Global(_) | Region::Globals)
    }
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
    /// Reads an I-cell in this region, which waits for its one write: it
    /// must stay after writes to the region, but commutes with other reads.
    Await(Region),
    /// May run for an unbounded time: a recursive call, a call of a closure
    /// that may have been fetched from the store, or through a recursive
    /// type. It has no region, so nothing masks it
    /// (`docs/research/type-and-effect-directions.md`, R6).
    Spin,
    /// An effect variable.
    Var(DVar),
}

impl Atom {
    pub fn region(self) -> Option<Region> {
        match self {
            Atom::Read(r) | Atom::Write(r) | Atom::Alloc(r) | Atom::Goto(r) | Atom::Comefrom(r) | Atom::Await(r) => {
                Some(r)
            }
            Atom::Var(_) | Atom::Spin => None,
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
    /// Subeffecting: every atom of `self` is in `other`, or, if it reads or
    /// writes one global, `other` does so to `@globals`.
    pub fn within(&self, other: &Effect) -> bool {
        self.0.iter().all(|a| {
            other.0.contains(a)
                || match a {
                    Atom::Read(Region::Global(_)) => other.0.contains(&Atom::Read(Region::Globals)),
                    Atom::Write(Region::Global(_)) => other.0.contains(&Atom::Write(Region::Globals)),
                    _ => false,
                }
        })
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
    Subr { conv: Conv, effect: Effect, params: Vec<TyId>, result: TyId },
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
    /// FX-91's `(productof (label T) …)`: an immutable record. Immutable, so
    /// in no region, and making one is pure; at run time a frozen bloblet
    /// with a field per label, in order.
    Product(Vec<(Sym, TyId)>),
    /// FX-91's `(sumof (tag T) …)`: an immutable tagged union; at run time
    /// a frozen bloblet of the tag, as a symbol, and the value.
    Sum(Vec<(Sym, TyId)>),
    /// `(arrayof T R)`: a bloblet in region `R` with any number of fields,
    /// all of type `T`, read and written by index.
    Array(TyId, Region),
    /// `(icell T R)`: an I-cell in region `R` (Arvind's I-structures): empty
    /// until its one write of a `T`, and never changed after.
    ICell(TyId, Region),
    /// `(place R)`: the memory that region `R` is allocated in, as a value:
    /// what `letrena` and `letreap` bind their region's name to, and what
    /// `rcons` allocates in (`docs/research/places-and-regions.md`).
    Place(Region),
    /// `(nat s)`: a natural, exactly the size `s`; `nat` is `(nat finite)`,
    /// some natural. Every `nat` is an `int` (`docs/research/sizes.md`, N5d).
    Nat(Size),
    /// `(bloblet (fields T…) R)`: a bloblet in region `R` whose fields have
    /// the types `T…`, with a suffix of bytes (`docs/object-model.md`).
    /// `(bloblet (frozen T…) R)` is one whose fields have been frozen: they
    /// cannot change, so reading one is pure.
    Bloblet { fields: Vec<TyId>, frozen: bool, region: Region },
    /// A forwarding slot, for building recursive types: `dletrec` allocates
    /// one per name, parses the bodies against them, then fills them in.
    Link(Option<TyId>),
    /// A generative type applied to its descriptions: `(name d …)`, where
    /// `name` is the `which`th `define-generative`. Equal only to itself, by
    /// its variance, and never unfolded to be compared; looked through by
    /// every analysis of what a value holds (`docs/research/generative-types.md`).
    Named { which: u32, args: Vec<D> },
    /// `(nlist T size)`: a list frozen at `region` (always `acyclic`) with
    /// `size` elements, or some number if `size` is `finite`
    /// (`docs/research/sizes.md`).
    NList { elem: TyId, size: Size, region: Region },
}

/// A list's length, as far as it is known: some number (`finite`), or a
/// linear expression in size variables, `k + Σ cᵢ·vᵢ`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Size {
    Finite,
    Lin { k: i64, terms: Vec<(DVar, i64)> },
}

impl Size {
    pub fn lit(k: i64) -> Size {
        Size::Lin { k, terms: Vec::new() }
    }

    /// The literal this is, if it is one.
    pub fn as_lit(&self) -> Option<i64> {
        match self {
            Size::Lin { k, terms } if terms.is_empty() => Some(*k),
            _ => None,
        }
    }

    /// `self + d`; `finite` stays `finite`.
    pub fn plus(&self, d: i64) -> Size {
        match self {
            Size::Finite => Size::Finite,
            Size::Lin { k, terms } => Size::Lin { k: k + d, terms: terms.clone() },
        }
    }
}

/// How a generative type's parameter may vary: `(name d …) ≤ (name d′ …)`
/// when each `d` is related to `d′` so.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Variance {
    Co,
    Contra,
    Inv,
}

impl Ty {
    /// What calling a value of this type does, if it can be called: its
    /// latent effect, parameters and result. A composable continuation runs
    /// the rest of its prompt's body, so its latent effect is the tag's bound
    /// together with the control effects on the tag's region.
    pub fn as_subr(&self) -> Option<(Effect, Vec<TyId>, TyId)> {
        match self {
            Ty::Subr { effect, params, result, .. } => Some((effect.clone(), params.clone(), *result)),
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

/// What a region form makes besides the region (`docs/research/places-and-regions.md`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RegionForm {
    /// `letregion`: nothing; a name for analysis only.
    Region,
    /// `letfreeze`: nothing either; its region's data is frozen as it
    /// ends, into the place given (`None`, the heap).
    Freeze(Option<DVar>),
    /// `letrena`: an arena, reclaimed only when the body ends.
    Arena,
    /// `letreap`: a heap of its own, which the collector collects too.
    Reap,
}

impl RegionForm {
    /// The form's keyword.
    pub fn keyword(self) -> &'static str {
        match self {
            RegionForm::Region => "letregion",
            RegionForm::Freeze(_) => "letfreeze",
            RegionForm::Arena => "letrena",
            RegionForm::Reap => "letreap",
        }
    }
    /// The primitive that makes its place, if it makes one.
    pub fn enter(self) -> Option<&'static str> {
        match self {
            RegionForm::Region | RegionForm::Freeze(_) => None,
            RegionForm::Arena => Some("%region-enter"),
            RegionForm::Reap => Some("%reap-enter"),
        }
    }
}

/// A description in argument position — what `proj` supplies.
#[derive(Clone, Debug)]
pub enum D {
    Region(Region),
    Effect(Effect),
    Type(TyId),
    Size(Size),
    Conv(Conv),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct ExpId(pub u32);

#[derive(Clone, Debug)]
pub enum Exp {
    Var(Sym),
    Int(i64),
    Bool(bool),
    Str(String),
    Char(char),
    /// `'name`: a symbol.
    Symbol(Sym),
    Unit,
    /// A parameter's type may be left out when the `lambda` is checked
    /// against a type that supplies it.
    Lambda { params: Vec<(Sym, Option<TyId>)>, body: ExpId },
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
    /// `(letregion r body …)`, `(letrena r body …)` or `(letreap r body
    /// …)`: a region that lives while `body` runs. `r` is a region
    /// variable, in scope in the body's types; nothing that outlives the
    /// body may mention it. A `letregion`'s is for analysis only, its data
    /// in the heap; the other two also make a place for it, whose value `r`
    /// names in the body (`form`).
    LetRegion { form: RegionForm, region: DVar, body: ExpId },
    /// `(rlambda r (param …) body …)`: the `lambda`, its closure made in
    /// the region `r` names (`region`, an expression of type `(place R)`).
    /// Calling it reads the closure, so its latent effect has `(read R)`.
    RLambda { region: ExpId, lambda: ExpId },
    /// `(the type expression)`: check the expression against the type.
    The { ty: TyId, exp: ExpId },
    /// `(convention C expression)`: the procedure converted to `C`.
    Convention { conv: Conv, exp: ExpId },
    /// The bloblet forms, which are syntax because a field's index must be
    /// known to know its type.
    Bloblet { op: BlobletOp, args: Vec<ExpId> },
    /// `(product (label e) …)`.
    Product(Vec<(Sym, ExpId)>),
    /// `(extract e label)`.
    Extract(ExpId, Sym),
    /// `(sum tag e)`.
    Sum(Sym, ExpId),
    /// `(tagcase e (tag x body) … [(else y body)])`: each arm sees the
    /// value its tag carries; `else` sees the sum of the tags not named.
    TagCase { scrutinee: ExpId, arms: Vec<Arm>, els: Option<(Sym, ExpId)> },
}

/// One arm of a `tagcase`.
#[derive(Clone, Debug)]
pub struct Arm {
    pub tag: Sym,
    pub bind: ArmBind,
    pub body: ExpId,
}

/// What an arm binds: the value, or, when the value is a product, its
/// fields in order, `(tag (a b) body)`.
#[derive(Clone, Debug)]
pub enum ArmBind {
    Value(Sym),
    Fields(Vec<Sym>),
}

impl Arm {
    pub fn names(&self) -> Vec<Sym> {
        match &self.bind {
            ArmBind::Value(x) => vec![*x],
            ArmBind::Fields(xs) => xs.clone(),
        }
    }
}

/// A bloblet form. Field `i` is the program's `i`th field, counted from 0;
/// the object model calls it field `i + 2`, after the trailer.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BlobletOp {
    /// `(make-bloblet bytes e …)`: a new bloblet with these fields and a
    /// suffix of `bytes` zero bytes.
    Make,
    /// `(rmake-bloblet r bytes e …)`: the same, in the region `r` names.
    RMake,
    /// `(bloblet-ref b i)`.
    Ref(usize),
    /// `(bloblet-set! b i e)`.
    Set(usize),
    /// `(bloblet-freeze b)`: the same bloblet, its fields frozen.
    Freeze,
    /// `(bloblet-byte b i)`.
    Byte,
    /// `(bloblet-set-byte! b i n)`.
    SetByte,
    /// `(bloblet-bytes b)`: how many bytes the suffix has.
    Bytes,
}

impl BlobletOp {
    pub const NAMES: &[&str] =
        &["make-bloblet", "rmake-bloblet", "bloblet-ref", "bloblet-set!", "bloblet-freeze", "bloblet-byte", "bloblet-set-byte!", "bloblet-bytes"];
}

#[derive(Default)]
pub struct Arena {
    tys: Vec<Ty>,
    exps: Vec<(Span, Exp)>,
    /// Names of description variables, for printing.
    dvar_names: Vec<Sym>,
    /// Whether each description variable is a place.
    dvar_places: Vec<bool>,
    /// Which description variables are of kind `data`.
    dvar_data: Vec<bool>,
    /// Each region binder's bound, if it has one: `(r region p)`, a region
    /// that won't outlive `p` (`docs/research/places-and-regions.md`).
    dvar_bounds: Vec<Option<Region>>,
    /// The region and place variables bound around each one's binder, which
    /// it won't outlive: the order of lifetimes, by nesting.
    dvar_outer: Vec<Vec<DVar>>,
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
        self.dvar_places.push(false);
        self.dvar_data.push(false);
        self.dvar_bounds.push(None);
        self.dvar_outer.push(Vec::new());
        DVar(self.dvar_names.len() as u32 - 1)
    }

    /// A description variable of kind `kind`.
    pub fn dvar_of(&mut self, name: Sym, kind: Kind) -> DVar {
        let v = self.dvar(name);
        self.dvar_places[v.0 as usize] = kind == Kind::Place;
        self.dvar_data[v.0 as usize] = kind == Kind::Data;
        v
    }

    /// Give region binder `v` a bound: a region it won't outlive.
    pub fn set_bound(&mut self, v: DVar, b: Region) {
        self.dvar_bounds[v.0 as usize] = Some(b);
    }
    /// The bound of region binder `v`, if it has one.
    pub fn bound(&self, v: DVar) -> Option<Region> {
        self.dvar_bounds[v.0 as usize]
    }
    /// Record the region and place variables bound around `v`'s binder.
    pub fn set_outer(&mut self, v: DVar, outer: Vec<DVar>) {
        self.dvar_outer[v.0 as usize] = outer;
    }

    /// `a ≤ b`: region `a` won't outlive region `b`. The same; `b` a
    /// constant (which never ends: `@name`, a fresh region, `const`); `b`
    /// bound around `a`'s binder; or `a`'s bound won't outlive `b`.
    pub fn outlived(&self, a: Region, b: Region) -> bool {
        if a == b || !matches!(b, Region::Var(_)) {
            return true;
        }
        if let Region::Frozen(Some(p), _) = a {
            return self.outlived(Region::Var(p), b);
        }
        let (Region::Var(v), Region::Var(w)) = (a, b) else { return false };
        self.dvar_outer[v.0 as usize].contains(&w) || self.bound(v).is_some_and(|c| c != a && self.outlived(c, b))
    }

    /// Whether region `r` is a place: a variable bound as one.
    /// Whether `v` is a type variable of kind `data`.
    pub fn is_data_var(&self, v: DVar) -> bool {
        self.dvar_data[v.0 as usize]
    }

    pub fn is_place(&self, r: Region) -> bool {
        matches!(r, Region::Heap) || matches!(r, Region::Var(v) if self.dvar_places[v.0 as usize])
    }

    /// The region and place variables bound around `v`'s binder.
    pub fn outer(&self, v: DVar) -> &[DVar] {
        &self.dvar_outer[v.0 as usize]
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
        self.dvar_places.truncate(mark.dvars);
        self.dvar_data.truncate(mark.dvars);
        self.dvar_bounds.truncate(mark.dvars);
        self.dvar_outer.truncate(mark.dvars);
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ArenaMark {
    tys: usize,
    exps: usize,
    dvars: usize,
}

impl ArenaMark {
    /// The first expression id allocated after the mark.
    pub fn exps(&self) -> u32 {
        self.exps as u32
    }
}
