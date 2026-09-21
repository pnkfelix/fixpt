//! FX-87's descriptions and expressions.
//!
//! # Three kinds, not two
//!
//! FX-91 has types and effects. FX-87 has types, effects *and* **regions**, and
//! the third one is not a detail: an effect is `(read r)` for some region, a
//! mutable type carries the region it lives in, and `poly` can abstract over a
//! region as easily as over a type. `kind-check.lisp` exists to keep the three
//! apart, so [`Kind`] is checked rather than assumed.
//!
//! # Checking, not inference
//!
//! The other difference that shapes everything here. FX-91 *infers* types by
//! unification, so its arena needs forwarding pointers and a union-find. FX-87
//! *checks* types that the programmer wrote down, so nothing is ever
//! substituted into a node after it is built — which means no forwarding, and
//! an arena that is append-only apart from [`Arena::fill`].
//!
//! What FX-87 has instead is **subtyping**: `int` where `float` was wanted,
//! `pure` where an effect was allowed, a smaller region where a larger one was.
//! That lives in [`subtype`](crate::subtype), and it is why the arena has to
//! support cycles — see below.
//!
//! # Cyclic descriptions
//!
//! `type-check.lisp` builds recursive types by mutation, with `set-car!`, and
//! compares them with a `trail` of pairs already being compared so the
//! comparison terminates. A list of integers really is a type that contains
//! itself.
//!
//! An arena gets that for free: a cycle is a [`DescId`] that points back at an
//! ancestor, which is an ordinary `u32`. [`Arena::hole`] allocates a node whose
//! contents arrive later, so a type can refer to itself before it exists. The
//! same property is what lets the unparser print one as `dletrec`.

use fixpt_read::{Span, Sym};

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct DescId(pub u32);

impl DescId {
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ExpId(pub u32);

impl ExpId {
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// What sort of thing a description is.
///
/// `dfunc` is a description *constructor* — `listof` is
/// `(dfunc (type region) type)` — so a kind is a small tree rather than an
/// enum of three.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Kind {
    Type,
    Effect,
    Region,
    DFunc(Vec<Kind>, Box<Kind>),
}

impl Kind {
    pub fn name(&self) -> &'static str {
        match self {
            Kind::Type => "type",
            Kind::Effect => "effect",
            Kind::Region => "region",
            Kind::DFunc(..) => "dfunc",
        }
    }
}

/// A description: a type, an effect, or a region.
///
/// One enum for all three, as in `syntax.lisp`, because they mix — `(read r)`
/// is an effect holding a region, `(ref t r)` a type holding both. The kind
/// checker is what keeps them straight.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Desc {
    /// A description variable, bound by `poly`, `plambda` or a `dfunc` binder.
    Var(Sym),

    // ------------------------------------------------------------- types
    /// A named constructor applied to arguments: `int`, `(ref t r)`,
    /// `(pairof t t r)`, `(string r)`, `(listof t r)`, `(promise e t)`.
    ///
    /// Held uniformly rather than as one variant each, because
    /// `standard.lisp` defines most of them in FX-87 itself — they are library,
    /// not language, and a checker that enumerated them would have to be edited
    /// to add one.
    Con(Sym, Vec<DescId>),
    /// `(subr effect (arg…) result)`
    Subr { effect: DescId, args: Vec<DescId>, result: DescId },
    /// `(vsubr effect fixed… rest result)` — a variable-arity subroutine.
    Vsubr { effect: DescId, args: Vec<DescId>, rest: DescId, result: DescId },
    /// `(poly ((v kind)…) body)`
    Poly { binders: Vec<Binder>, body: DescId },
    /// `(recordof ((field type)…) region)`
    RecordOf { fields: Vec<(Sym, DescId)>, region: DescId },
    /// `(oneof ((tag type)…) region)`
    OneOf { variants: Vec<(Sym, DescId)>, region: DescId },

    // ----------------------------------------------------------- effects
    Pure,
    Read(DescId),
    Write(DescId),
    Alloc(DescId),
    /// `(maxeff e…)` — the least upper bound. Kept flattened and deduplicated,
    /// because `effect-less-1?` says outright that it assumes that.
    MaxEff(Vec<DescId>),

    // ----------------------------------------------------------- regions
    /// `(runion r…)`
    RUnion(Vec<DescId>),

    // ------------------------------------------ description abstraction
    /// `(dlambda ((v kind)…) body)` — how `listof` is defined.
    DAbs { binders: Vec<Binder>, body: DescId },
    /// `(f d…)` where `f` is of `dfunc` kind.
    DApp { fun: DescId, args: Vec<DescId> },

    /// A node whose contents are not filled in yet. Only ever transient: a
    /// recursive type is built by allocating one of these, building the body
    /// that refers to it, and then filling it.
    Hole,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Binder {
    pub name: Sym,
    pub kind: Kind,
}

/// The expression language.
///
/// The kernel of `syntax.lisp`. Everything else — `let`, `let*`, `cond`, `do`,
/// `and`, `or` — is sugar that [`sugar`](crate::sugar) removes before this is
/// built, exactly as `sugar.lisp` does.
#[derive(Clone, PartialEq, Debug)]
pub enum Exp {
    Int(i64),
    Float(u64),
    Char(char),
    Str(String),
    Bool(bool),
    /// `#u`
    Unit,
    Symbol(Sym),
    /// `'()` and other quoted data.
    Quote(fixpt_read::Syntax),
    Var(Sym),
    /// `(the effect type exp)` or `(the type exp)`
    The { effect: Option<DescId>, ty: DescId, body: ExpId },
    If { test: ExpId, then: ExpId, els: ExpId },
    Begin(Vec<ExpId>),
    /// `(lambda ((x type)…) body)`; a parameter may name the region it lives
    /// in, as `(x type @!)`.
    Lambda { params: Vec<Param>, body: ExpId },
    /// `(let ((x exp)…) body)` — the initialisers cannot see the bindings.
    Let { bindings: Vec<Binding>, body: ExpId },
    /// `(letrec ((f exp)…) body)` — they can.
    Letrec { bindings: Vec<Binding>, body: ExpId },
    /// `(plambda ((v kind)…) body)`
    PLambda { binders: Vec<Binder>, body: ExpId },
    /// `(proj exp d…)` — instantiate a `poly`.
    Proj { body: ExpId, args: Vec<DescId> },
    App { fun: ExpId, args: Vec<ExpId> },
    SetBang { name: Sym, value: ExpId },

    // ---------------------------------------------------- standard forms
    // `standard.lisp` gives these their own checking rules rather than types
    // in the environment, because each needs its own relationship between the
    // region it lives in and the effect it costs.
    /// `(record ((field exp)…) [region])`
    Record { fields: Vec<(Sym, ExpId)>, region: Option<DescId> },
    /// `(select rec field)`
    Select { rec: ExpId, field: Sym },
    /// `(record-set! rec field value)`
    RecordSet { rec: ExpId, field: Sym, value: ExpId },
    /// `(one oneof-type tag exp)`
    One { ty: DescId, tag: Sym, value: ExpId },
    /// `(tagcase (v exp [region]) (tag body…)… [(else body…)])`
    TagCase { var: Sym, scrutinee: ExpId, region: Option<DescId>, clauses: Vec<TagClause> },
    /// `(one-set! exp tag value)`
    OneSet { target: ExpId, tag: Sym, value: ExpId },
    /// `(delay exp)`
    Delay(ExpId),
    /// `(vlambda (name type [region]) body…)` — variable arity.
    VLambda { name: Sym, ty: DescId, region: Option<DescId>, body: ExpId },
    /// `(do ((var init [step] [region])…) (test result…) body…)`
    ///
    /// Not expanded into a `letrec` loop the way Scheme's is, because FX-87's
    /// `lambda` needs written parameter types and `do` writes none: the loop
    /// variables take their types from their *initialisers*, which only the
    /// checker knows. So it stays a form of its own, as it does in the
    /// reference.
    Do { bindings: Vec<DoBinding>, test: ExpId, result: ExpId, body: Option<ExpId> },
}

#[derive(Clone, PartialEq, Debug)]
pub struct DoBinding {
    pub name: Sym,
    pub init: ExpId,
    /// Absent when the variable does not change each time round.
    pub step: Option<ExpId>,
    pub region: Option<DescId>,
}

/// One arm of a `tagcase`. `tag` is `None` for `else`.
#[derive(Clone, PartialEq, Debug)]
pub struct TagClause {
    pub tag: Option<Sym>,
    pub body: ExpId,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Param {
    pub name: Sym,
    pub ty: DescId,
    /// `(x int @!)` — the region the *binding* lives in, which is what makes it
    /// mutable. Not part of the parameter's type: the reference takes the
    /// subroutine's argument type from the second element alone, so
    /// `(lambda ((x int @!)) …)` is a `(subr … (int) …)`. The region instead
    /// contributes `(alloc r)` to the body's effect, and is what `set!` needs
    /// in order to charge a `(write r)`.
    pub region: Option<DescId>,
}

/// One binding of a `let` or `letrec`, which may also name a region.
#[derive(Clone, PartialEq, Debug)]
pub struct Binding {
    pub name: Sym,
    pub value: ExpId,
    pub region: Option<DescId>,
}

/// Descriptions and expressions, each in their own arena.
///
/// Separate arenas, unlike FX-91's single one: FX-87 descriptions never contain
/// expressions. `select` there was a *dependent* type — a type computed from a
/// module value — and that is what forced the two together. FX-87 has no such
/// thing, so keeping them apart costs nothing and means a `DescId` can never be
/// confused for an `ExpId`.
#[derive(Default)]
pub struct Arena {
    descs: Vec<Desc>,
    exps: Vec<Exp>,
    exp_spans: Vec<Span>,
    /// The source form each expression came from.
    ///
    /// Kept because FX-87's checking-failure messages *quote* the offending
    /// form — `Cannot type-check (if 1 2 3)` — and those messages are recorded
    /// in the conformance goldens, so reproducing them is not decoration. A
    /// span would not do: sugar is expanded during parsing, so several nodes
    /// share one span and a synthesized node has none of its own.
    exp_source: Vec<Option<fixpt_read::Syntax>>,
}

impl Arena {
    pub fn new() -> Arena {
        Arena::default()
    }

    pub fn desc(&mut self, d: Desc) -> DescId {
        self.descs.push(d);
        DescId(self.descs.len() as u32 - 1)
    }

    /// A description that does not exist yet, to be [`fill`](Arena::fill)ed
    /// once the body that refers to it has been built. This is how a recursive
    /// type is tied.
    pub fn hole(&mut self) -> DescId {
        self.desc(Desc::Hole)
    }

    pub fn fill(&mut self, id: DescId, d: Desc) {
        debug_assert!(
            matches!(self.descs[id.index()], Desc::Hole),
            "only a hole may be filled, or a description would change under something"
        );
        self.descs[id.index()] = d;
    }

    #[inline]
    pub fn get(&self, id: DescId) -> &Desc {
        &self.descs[id.index()]
    }

    pub fn exp(&mut self, span: Span, e: Exp) -> ExpId {
        self.exps.push(e);
        self.exp_spans.push(span);
        self.exp_source.push(None);
        ExpId(self.exps.len() as u32 - 1)
    }

    /// Remember the source form an expression was read from.
    pub fn set_source(&mut self, id: ExpId, source: fixpt_read::Syntax) {
        self.exp_source[id.index()] = Some(source);
    }

    pub fn source(&self, id: ExpId) -> Option<&fixpt_read::Syntax> {
        self.exp_source[id.index()].as_ref()
    }

    #[inline]
    pub fn exp_at(&self, id: ExpId) -> &Exp {
        &self.exps[id.index()]
    }

    #[inline]
    pub fn span(&self, id: ExpId) -> Span {
        self.exp_spans[id.index()]
    }

    pub fn desc_count(&self) -> usize {
        self.descs.len()
    }

    // ------------------------------------------------------- conveniences
    /// A nullary constructor, such as `int`.
    pub fn con0(&mut self, name: Sym) -> DescId {
        self.desc(Desc::Con(name, Vec::new()))
    }

    /// Build a `maxeff` in the normal form `eval-maxeff` produces:
    ///
    /// ```text
    /// (maxeff (alloc (runion …)) (read (runion …)) (write (runion …)) …)
    /// ```
    ///
    /// One atom per constructor, each over the union of its regions, in that
    /// order, with anything else — effect variables — last. `pure` is dropped
    /// and a single member is unwrapped.
    ///
    /// This is not tidiness. `effect-less-1?` states that it assumes a
    /// flattened, redundancy-free argument, and the conformance goldens record
    /// the normalised form exactly, down to the order of the union's members.
    pub fn maxeff(&mut self, parts: Vec<DescId>) -> DescId {
        let mut allocs = Vec::new();
        let mut reads = Vec::new();
        let mut writes = Vec::new();
        let mut others: Vec<DescId> = Vec::new();

        let mut stack = parts;
        stack.reverse();
        while let Some(p) = stack.pop() {
            match self.get(p).clone() {
                Desc::Pure => {}
                Desc::MaxEff(inner) => {
                    for x in inner.into_iter().rev() {
                        stack.push(x);
                    }
                }
                Desc::Alloc(r) => self.add_region(&mut allocs, r),
                Desc::Read(r) => self.add_region(&mut reads, r),
                Desc::Write(r) => self.add_region(&mut writes, r),
                _ => {
                    if !others.iter().any(|q| self.same(*q, p)) {
                        others.push(p);
                    }
                }
            }
        }

        let mut out = Vec::new();
        for (regions, make) in [
            (allocs, Desc::Alloc as fn(DescId) -> Desc),
            (reads, Desc::Read as fn(DescId) -> Desc),
            (writes, Desc::Write as fn(DescId) -> Desc),
        ] {
            if regions.is_empty() {
                continue;
            }
            let r = self.runion(regions);
            out.push(self.desc(make(r)));
        }
        out.extend(others);
        match out.len() {
            0 => self.desc(Desc::Pure),
            1 => out[0],
            _ => self.desc(Desc::MaxEff(out)),
        }
    }

    /// Add a region to a group, flattening a union and skipping duplicates.
    fn add_region(&mut self, group: &mut Vec<DescId>, r: DescId) {
        match self.get(r).clone() {
            Desc::RUnion(parts) => {
                for p in parts {
                    self.add_region(group, p);
                }
            }
            _ => {
                if !group.iter().any(|q| self.same(*q, r)) {
                    group.push(r);
                }
            }
        }
    }

    /// One region, or the union of several, in the order given.
    ///
    /// Order matters and is not arbitrary. An effect the checker *gathers*
    /// keeps the order its regions were met in, while a union written in source
    /// is flattened by `eval-rexp`, whose right fold prepends and therefore
    /// reverses it — so `(runion @red @blue)` as an ascription reports as
    /// `(runion @blue @red)`. The reversal belongs to evaluation, not here.
    pub fn runion(&mut self, mut regions: Vec<DescId>) -> DescId {
        if regions.len() == 1 {
            return regions.pop().expect("length checked");
        }
        self.desc(Desc::RUnion(regions))
    }

    /// Structural equality, cycle-safe.
    ///
    /// Needed even for deduplication: two `(read @!)` nodes built at different
    /// times are different `DescId`s and the same effect.
    pub fn same(&self, a: DescId, b: DescId) -> bool {
        self.same_seen(a, b, &mut Vec::new())
    }

    fn same_seen(&self, a: DescId, b: DescId, trail: &mut Vec<(DescId, DescId)>) -> bool {
        if a == b {
            return true;
        }
        // The `trail` of `type-check.lisp`: assume the pair equal while
        // proving it, so a cycle terminates instead of recurring forever.
        if trail.contains(&(a, b)) {
            return true;
        }
        trail.push((a, b));
        let result = match (self.get(a), self.get(b)) {
            (Desc::Var(x), Desc::Var(y)) => x == y,
            (Desc::Con(x, xs), Desc::Con(y, ys)) => {
                x == y && xs.len() == ys.len() && self.all_same(xs, ys, trail)
            }
            (
                Desc::Subr { effect: e1, args: a1, result: r1 },
                Desc::Subr { effect: e2, args: a2, result: r2 },
            ) => {
                self.same_seen(*e1, *e2, trail)
                    && a1.len() == a2.len()
                    && self.all_same(a1, a2, trail)
                    && self.same_seen(*r1, *r2, trail)
            }
            (
                Desc::Vsubr { effect: e1, args: a1, rest: s1, result: r1 },
                Desc::Vsubr { effect: e2, args: a2, rest: s2, result: r2 },
            ) => {
                self.same_seen(*e1, *e2, trail)
                    && a1.len() == a2.len()
                    && self.all_same(a1, a2, trail)
                    && self.same_seen(*s1, *s2, trail)
                    && self.same_seen(*r1, *r2, trail)
            }
            (
                Desc::Poly { binders: b1, body: y1 },
                Desc::Poly { binders: b2, body: y2 },
            )
            | (
                Desc::DAbs { binders: b1, body: y1 },
                Desc::DAbs { binders: b2, body: y2 },
            ) => b1 == b2 && self.same_seen(*y1, *y2, trail),
            (
                Desc::RecordOf { fields: f1, region: g1 },
                Desc::RecordOf { fields: f2, region: g2 },
            )
            | (
                Desc::OneOf { variants: f1, region: g1 },
                Desc::OneOf { variants: f2, region: g2 },
            ) => {
                f1.len() == f2.len()
                    && f1.iter().zip(f2).all(|((n1, t1), (n2, t2))| {
                        n1 == n2 && self.same_seen(*t1, *t2, trail)
                    })
                    && self.same_seen(*g1, *g2, trail)
            }
            (Desc::Pure, Desc::Pure) => true,
            (Desc::Read(x), Desc::Read(y))
            | (Desc::Write(x), Desc::Write(y))
            | (Desc::Alloc(x), Desc::Alloc(y)) => self.same_seen(*x, *y, trail),
            (Desc::MaxEff(xs), Desc::MaxEff(ys)) | (Desc::RUnion(xs), Desc::RUnion(ys)) => {
                // Order-insensitive: a maxeff and a runion are sets.
                xs.len() == ys.len()
                    && xs.iter().all(|x| ys.iter().any(|y| self.same_seen(*x, *y, trail)))
            }
            (Desc::DApp { fun: f1, args: a1 }, Desc::DApp { fun: f2, args: a2 }) => {
                self.same_seen(*f1, *f2, trail)
                    && a1.len() == a2.len()
                    && self.all_same(a1, a2, trail)
            }
            _ => false,
        };
        trail.pop();
        result
    }

    fn all_same(&self, xs: &[DescId], ys: &[DescId], trail: &mut Vec<(DescId, DescId)>) -> bool {
        xs.iter().zip(ys).all(|(x, y)| self.same_seen(*x, *y, trail))
    }
}
