//! Checking the kernel: a type and an effect for every expression.
//!
//! The rules are KFX's (PLDI '89, p. 3), n-ary as FX-87 writes them:
//!
//! * a variable, a literal, a `lambda` and a `plambda` are pure;
//! * an application's effect is the operator's, the arguments', and the
//!   operator's latent effect, combined;
//! * a `plambda`'s body must be pure;
//! * `proj` substitutes descriptions for a `poly`'s binders.
//!
//! **Masking** is applied at every expression that combines effects —
//! application, `lambda` (whose masked body effect becomes the latent
//! effect), `let`, `letrec`, `begin`, `if`, `proj` — as FX-87's reference does
//! (`erase-effect`, called from `desc-of-begin`, `-lambda`, `-letrec`, `-app`
//! in `type-check.lisp`). The rule for each region `r` of an effect:
//!
//! * if `r` appears in the type of a free variable, everything on `r` stays;
//! * otherwise everything on `r` goes — except that when `r` appears in the
//!   result type, `(alloc r)` stays (FX-87: the cell escapes), and so do
//!   `(goto r)` and `(comefrom r)` (PLDI '89, p. 6: a control effect is masked
//!   only if the expression neither imports variables nor returns values whose
//!   types mention `r` — stricter than FX-87's rule for reads and writes, and
//!   p. 7 shows why).
//!
//! **Prompts** delimit control on their tag's region, under a condition of
//! their own: see `synth_prompt`.

use crate::ast::{Arena, Arm, ArmBind, Atom, BlobletOp, Conv, D, DVar, EArg, Effect, Exp, ExpId, Kind, Region, RegionForm, Size, Ty, TyId, Variance};
use crate::error::{FxError, R};
use crate::parse::DScope;
use fixpt_read::{Interner, Reader, Sym, Syntax, SyntaxProfile};
use std::collections::{HashMap, HashSet};

/// `vsubr`'s declaration: generative type 0, in both checkers.
pub const VSUBR: &str = "(vsubr (e effect +) (t type -) (r type +)) (subr e ((listof t acyclic)) r)";
/// A flat array's element layout (Q6), generative type 1: what `t` is kept
/// as, a number at run time; nothing sees inside it.
pub const FLATLAYOUT: &str = "(flatlayout (t type)) int";
/// A flat array (`flatarrayof`, Q6), generative type 2: an array to
/// safety's analyses (its regions), opaque to anything else; its elements
/// raw at run time, as its layout says.
pub const FLATARRAYOF: &str = "(flatarrayof (t type) (r region)) (arrayof t r)";
/// A kind of key that has identity (Q5), generative type 3: `k`, a mutable
/// object at `r`, which only the standard dictionaries (`pair-identity` and
/// kin) are made for; nothing at run time.
pub const IDENTITY: &str = "(identity (k type) (r region)) int";
/// A table keyed by identity (Q5), generative type 4: keys `k` at `kr`,
/// values `v`, the table in `r`; to safety's analyses, entries of both in
/// `r`, and opaque to anything else (`fixpt_runtime::eqtable`).
pub const EQTABLE: &str = "(eqtable (k type) (v type) (kr region) (r region)) (arrayof (pairof k v r) r)";

/// A `define-generative`: its name, parameters, their variance, and the
/// representation, a type over the parameters.
#[derive(Clone, Debug)]
pub struct Generative {
    pub name: Sym,
    pub params: Vec<(DVar, Kind)>,
    pub variance: Vec<Variance>,
    pub rep: TyId,
}

pub struct Checker {
    pub arena: Arena,
    pub interner: Interner,
    /// Value variables in scope, innermost last.
    pub env: Vec<(Sym, TyId)>,
    /// Description names in scope while parsing, innermost last.
    pub(crate) dscope: Vec<(Sym, DScope)>,
    /// The region and place variables bound around what is being parsed,
    /// by expressions (not types): the order of lifetimes, by nesting.
    pub(crate) lifetimes: Vec<DVar>,
    /// The regions `letfreeze`s are freezing, innermost last, each with
    /// whether anything has written it: data never written is finite.
    pub(crate) freezing: Vec<(DVar, bool)>,
    /// Bindings of known procedures, by name and place in `env`: those a
    /// `define`, `letrec`, `define-rec`, or a `let` of a `lambda` made. A
    /// call of one runs code the checker has seen; a call of anything else
    /// might run a closure fetched from the store. By binding, not by name
    /// and type, so a parameter that shadows one is not taken for it
    /// (`docs/research/soundness-findings.md`, F1); forgotten as its scope
    /// ends (`Checker::truncate_env`).
    pub(crate) known: HashSet<(Sym, usize)>,
    /// The bindings of the recursive groups whose lambdas are being checked:
    /// a call of one of them there is recursion, and so `spin`.
    pub(crate) recursive: Vec<(Sym, TyId)>,
    pub(crate) base: HashMap<Sym, TyId>,
    pub(crate) void: TyId,
    pub(crate) int: TyId,
    bool_: TyId,
    string: TyId,
    unit: TyId,
    char_: TyId,
    f64_: TyId,
    symbol: TyId,
    /// How deep in abbreviation expansions parsing is, to stop one that
    /// mentions itself.
    pub(crate) expanding: u32,
    /// The type families being expanded, each with the descriptions given
    /// it and the slot its type will fill: a use inside with the same
    /// descriptions is that slot, a knot (regular recursion).
    pub(crate) knots: Vec<(Sym, Vec<crate::parse::FamilyArg>, TyId)>,
    /// While the REPL asks what goes where the cursor is
    /// (`Checker::describe_hole`), the names the hole is read as; `None`
    /// otherwise, so that no program ever sees a hole.
    pub(crate) holes: Option<crate::top::Holes>,
    /// What the hole was found to want, once checking reached it.
    pub(crate) hole_hint: Option<String>,
    /// Why each member of a recursive group that may not end may not: said
    /// when its declared type leaves out `spin`.
    pub(crate) spin_why: Vec<((Sym, TyId), String)>,
    /// Every `define-generative`, by number.
    pub(crate) generatives: Vec<Generative>,
    /// The generative types whose insides the definition being checked may
    /// see: its own `up-name` and `down-name`.
    pub(crate) transparent: Vec<u32>,
    /// The definitions still to come that may see inside a generative type.
    pub(crate) inside: Vec<(Sym, u32)>,
    /// The bindings of generative types' conversions, which are the
    /// identity: size-change looks through them.
    pub(crate) conversions: Vec<(Sym, TyId)>,
    /// The lemmas proved so far (`crate::lemma`), which subtyping uses
    /// when its rules alone do not relate two types.
    pub(crate) lemmas: Vec<crate::lemma::Lemma>,
    /// The lemma a `proves` type being read states, for the definition it
    /// declares.
    pub(crate) pending_lemma: Option<crate::lemma::Lemma>,
    /// The variables `acyclic?` has just found acyclic, in the branch where
    /// it did: each by name and by which binding it is (its place in `env`).
    pub(crate) certified: Vec<(Sym, usize)>,
    /// The same for `nat?`: the variables it has just found no less than 0.
    pub(crate) certified_nats: Vec<(Sym, usize)>,
    /// The same for `length-is?`: each variable, its binding, and the
    /// length it was found to have.
    pub(crate) certified_lengths: Vec<(Sym, usize, Size)>,
    /// The sizes given to `nat` variables of no known size, innermost last
    /// (`Checker::name_nat`).
    pub(crate) skolems: Vec<DVar>,
    /// Of those, the ones made for a module's abstract types as it was
    /// bound (`Checker::name_module`): not forgotten, but kept from leaving.
    pub(crate) module_vars: HashSet<DVar>,
    /// The description-function variables that are a module's abstract
    /// type constructors, whose representations no one outside can see:
    /// what is given to one is kept, cautiously, everywhere (`knot_in`).
    pub(crate) abstract_funs: HashSet<DVar>,
    /// While a type's `select`s are resolved (`Checker::resolve_selects`):
    /// what each is; empty otherwise.
    pub(crate) select_map: HashMap<(Sym, Sym), TyId>,
    /// While a dependent procedure's parameters are given (`Checker::
    /// instantiate_params`): what each `(select $k t)` is; empty otherwise.
    pub(crate) param_map: HashMap<(usize, Sym), TyId>,
    /// The program's convention (set by [`Checker::with_convention`]):
    /// what a subroutine type that names none has, and what a convention
    /// nothing solves defaults to
    /// (`docs/research/native-conventions.md`). Cellular unless asked.
    pub conv_default: Conv,
    /// What the branches being checked have learned about sizes
    /// (`crate::sizes`).
    pub(crate) size_facts: Vec<crate::sizes::SizeFact>,
    /// How many fresh regions inference has made, for naming the next.
    pub(crate) fresh_regions: u32,
    /// How many entries of `env` are the initial environment's.
    pub(crate) standard_len: usize,
    /// How many description names the standard environment has.
    pub(crate) standard_dscope: usize,
    /// While a module read from a file is checked (`load-module`, M7): the
    /// bindings, and the description names, past the standard ones and
    /// before it, which it may not see.
    pub(crate) hidden: Option<((usize, usize), (usize, usize))>,
    /// Modules read from files: each one's path and text, and the file id
    /// its spans have.
    pub(crate) loaded: HashMap<ExpId, (String, String, fixpt_read::FileId)>,
    /// How many module files have been read: the next one's number, in the
    /// order they are begun, a file a loaded file loads after it, as the
    /// driver supplies them to the parser written in FX-26 (`syn.rs`).
    pub(crate) files_read: u32,
    /// Where a `load-module`'s relative path is from: the program's own
    /// directory, when it was read from a file; else the current one.
    pub base_dir: Option<std::path::PathBuf>,
    /// While a program's types are declared ahead (`declare_ahead`), each
    /// abbreviation's slot, made before any is read so that they may name
    /// each other in any order; and those filled, to check once all are.
    pub(crate) ahead: Vec<(Sym, TyId)>,
    pub(crate) ahead_filled: Vec<(TyId, fixpt_read::Span)>,
    /// What checking proved about each expression, for lowering to carry.
    pub facts: NodeFacts,
    /// The regions `private-regions` made this program's own.
    pub private_regions: Vec<Region>,
    /// Mask at every expression, as the rules say. Off only to observe an
    /// effect *before* masking, which is what some of the paper's claims are
    /// about.
    pub masking: bool,
    /// Globals broken by an incompatible redefinition of one they use
    /// (`Fx26Session`'s redefinition): by name, the index in `env` of the
    /// binding broken, and why. A use of it is an error until the name is
    /// defined again.
    pub(crate) broken: HashMap<Sym, (usize, String)>,
    /// The definitions checked so far, oldest first, each the latest of its
    /// names: what a redefinition finds the users of a name in
    /// (`Checker::top_defining`).
    pub(crate) defs: Vec<crate::top::Definition>,
    /// Whether a redefinition that makes a new global leaves the
    /// definitions that use the name as they are, out of date, instead of
    /// checking them again (`Checker::top_defining`): what the REPL asks
    /// for, re-running them when told (`,rerun-outdated`).
    pub defer_reruns: bool,
    /// The definitions out of date (`defer_reruns`): each one's names, and
    /// the names it uses that were defined again since, at new globals.
    pub(crate) outdated: Vec<(Vec<Sym>, Vec<Sym>)>,
    /// Whether naming a global reads its binding, `(read (globals g))`, as
    /// the language will say once every program says so (off until then).
    pub globals_effects: bool,
    /// Where in `env` the globals are: the bindings top-level definitions
    /// made.
    pub(crate) global_slots: HashSet<usize>,
}

/// What checking proved about expressions, keyed by expression. Lowering
/// turns these into `%fx-note` claims (`crate::lower`).
#[derive(Clone, Debug, Default)]
pub struct NodeFacts {
    /// Each expression's effect, after masking.
    pub effects: HashMap<ExpId, Effect>,
    /// Applications whose operator is a standard binding, by name. The
    /// initial environment cannot be assigned, so the operator is known.
    pub standard_operator: HashMap<ExpId, Sym>,
    /// Expressions that allocate, where masking removed every allocation
    /// and the value is first-order data (`Checker::first_order`): nothing
    /// they allocate outlives them.
    pub no_escape: HashSet<ExpId>,
    /// Each `extract`'s field, by position: lowering needs it, and only the
    /// product's type says it.
    pub field_index: HashMap<ExpId, usize>,
    /// Procedures converted to another convention, by the checker or by
    /// `(convention C e)`: the convention each is converted to, and how
    /// many arguments the procedure takes.
    pub converted: HashMap<ExpId, (Conv, usize)>,
    /// Applications of `apply` whose list is at `acyclic`: the variadic
    /// procedure may have that list itself, since nothing can write it.
    /// Every other `apply` copies its list.
    pub apply_shares: HashSet<ExpId>,
    /// Each `with`'s module's values, in order: lowering binds them.
    pub with_vals: HashMap<ExpId, Vec<Sym>>,
    /// Modules given where a type with fewer values, or the same in
    /// another order, is wanted: for each value the wanted type has, its
    /// position in the module given. Made into a module of that layout.
    pub reshaped: HashMap<ExpId, Vec<usize>>,
}

impl NodeFacts {
    /// Forget everything about expressions from `first` on.
    pub(crate) fn forget_from(&mut self, first: u32) {
        self.effects.retain(|e, _| e.0 < first);
        self.standard_operator.retain(|e, _| e.0 < first);
        self.no_escape.retain(|e| e.0 < first);
        self.field_index.retain(|e, _| e.0 < first);
        self.with_vals.retain(|e, _| e.0 < first);
        self.reshaped.retain(|e, _| e.0 < first);
        self.converted.retain(|e, _| e.0 < first);
        self.apply_shares.retain(|e| e.0 < first);
    }

    /// What the compilers give `%fx26-convert` for `e`'s conversion: its
    /// arity times 4, plus 1 to make it `cellular` or 2 to make it
    /// `native`. None if `e` is not converted to one of those; a
    /// conversion to `fx` or to a binder does nothing at run time.
    /// Whether `e`'s value is changed as it is given: converted to a
    /// convention, or a module reshaped.
    pub fn changed(&self, e: ExpId) -> bool {
        self.converted.contains_key(&e) || self.reshaped.contains_key(&e)
    }

    pub fn conversion_code(&self, e: ExpId) -> Option<i64> {
        match self.converted.get(&e)? {
            (Conv::Cellular, n) => Some(4 * *n as i64 + 1),
            (Conv::Native, n) => Some(4 * *n as i64 + 2),
            _ => None,
        }
    }
}

/// What checking an expression found.
#[derive(Clone, Debug)]
pub struct Checked {
    pub ty: TyId,
    pub effect: Effect,
    /// The expression checked, for lowering.
    pub exp: ExpId,
}

impl Default for Checker {
    fn default() -> Checker {
        Checker::new()
    }
}

impl Checker {
    /// A checker with the initial environment of `crate::standard`.
    pub fn new() -> Checker {
        Checker::with_convention(Conv::Cellular)
    }

    /// A checker whose program's convention is `conv`: every subroutine
    /// type that names none has it, the standard environment's included
    /// (`--calling-convention`).
    pub fn with_convention(conv: Conv) -> Checker {
        let mut interner = Interner::new();
        let mut arena = Arena::default();
        let mut base = HashMap::new();
        let mut basic = |name: &str| {
            let sym = interner.intern(name);
            let t = arena.ty(Ty::Base(sym));
            base.insert(sym, t);
            t
        };
        let int = basic("int");
        let bool_ = basic("bool");
        let string = basic("string");
        let unit = basic("unit");
        let char_ = basic("char");
        // A Scheme datum, as a reader produces: opaque, and immutable, so
        // building one is no effect.
        basic("datum");
        // A symbol: interned, so compared by identity, and immutable.
        let symbol = basic("symbol");
        // Cellular code, for the compiler written in FX-26: a word (`tword`,
        // since the reader has a `word` of its own), a cell of one, and a
        // global's cell. Opaque; made by the `wcell-` and
        // `make-` constants and checked when a word is made.
        basic("tword");
        basic("wcell");
        basic("wglobal");
        // The fixed-width integers: an `i32` or `u32` is the fixnum it stands
        // for, an `i64` or `u64` the exact integer (PLAN.md, Q2 b). After
        // the others, in the order `check-types.fx` makes them: type ids agree.
        for fixed in ["i32", "u32", "i64", "u64"] {
            basic(fixed);
        }
        // IEEE binary64 and binary32 (`docs/fx26.md`, "Floats"): a boxed
        // flonum, and an immediate of its own.
        let f64_ = basic("f64");
        basic("f32");
        let void = arena.ty(Ty::Void);
        let mut c = Checker {
            arena,
            interner,
            env: Vec::new(),
            dscope: Vec::new(),
            lifetimes: Vec::new(),
            freezing: Vec::new(),
            known: HashSet::new(),
            recursive: Vec::new(),
            base,
            void,
            int,
            bool_,
            string,
            unit,
            char_,
            f64_,
            symbol,
            expanding: 0,
            knots: Vec::new(),
            holes: None,
            hole_hint: None,
            spin_why: Vec::new(),
            generatives: Vec::new(),
            transparent: Vec::new(),
            inside: Vec::new(),
            conversions: Vec::new(),
            lemmas: Vec::new(),
            pending_lemma: None,
            certified: Vec::new(),
            certified_nats: Vec::new(),
            certified_lengths: Vec::new(),
            size_facts: Vec::new(),
            skolems: Vec::new(),
            module_vars: HashSet::new(),
            abstract_funs: HashSet::new(),
            select_map: HashMap::new(),
            param_map: HashMap::new(),
            conv_default: conv,
            fresh_regions: 0,
            standard_len: 0,
            standard_dscope: 0,
            hidden: None,
            loaded: HashMap::new(),
            files_read: 0,
            base_dir: None,
            ahead: Vec::new(),
            ahead_filled: Vec::new(),
            facts: NodeFacts::default(),
            private_regions: Vec::new(),
            masking: true,
            broken: HashMap::new(),
            defs: Vec::new(),
            defer_reruns: false,
            outdated: Vec::new(),
            globals_effects: true,
            global_slots: HashSet::new(),
        };
        // FX-87's variadic procedure type, `(vsubr E T R)`: the first
        // generative type, in both checkers, whose insides nothing sees
        // (no `up-` or `down-`: a `vsubr` is called with its arguments, not
        // their list). `vlambda` makes one; `apply` calls one on a list.
        for decl in [VSUBR, FLATLAYOUT, FLATARRAYOF, IDENTITY, EQTABLE] {
            let forms = c.read(decl).expect("reads");
            c.define_generative(&forms[0], &forms[1]).unwrap_or_else(|e| panic!("`{decl}` is wrong: {e}"));
        }
        for (name, ty) in crate::standard::ENTRIES {
            c.bind(name, ty).unwrap_or_else(|e| panic!("the standard type of `{name}` is wrong: {e}"));
        }
        c.standard_len = c.env.len();
        c.standard_dscope = c.dscope.len();
        c
    }

    fn read(&mut self, text: &str) -> R<Vec<Syntax>> {
        let mut interner = std::mem::take(&mut self.interner);
        let r = Reader::new(text, fixpt_read::FileId(0), SyntaxProfile::FX26, &mut interner).read_all();
        self.interner = interner;
        r.map_err(|e| FxError::at(e.span, e.message))
    }

    /// Bind `name` to a value of the type written `ty` — how the initial
    /// environment is built, and how a test supplies an example's free
    /// variables.
    pub fn bind(&mut self, name: &str, ty: &str) -> R<()> {
        let forms = self.read(ty)?;
        let [form] = &forms[..] else {
            return Err(FxError::at(fixpt_read::Span::new(fixpt_read::FileId(0), 0, 0), "one type"));
        };
        let t = self.parse_type(form)?;
        let sym = self.interner.intern(name);
        self.env.push((sym, t));
        Ok(())
    }

    /// Check the one expression written `text`.
    pub fn check_str(&mut self, text: &str) -> R<Checked> {
        let forms = self.read(text)?;
        let [form] = &forms[..] else {
            return Err(FxError::at(fixpt_read::Span::new(fixpt_read::FileId(0), 0, 0), "one expression"));
        };
        let e = self.parse_exp(form)?;
        let (ty, effect) = self.synth(e)?;
        Ok(Checked { ty, effect, exp: e })
    }

    /// A type written as text, for comparing against.
    pub fn type_of_str(&mut self, text: &str) -> R<TyId> {
        let forms = self.read(text)?;
        let [form] = &forms[..] else {
            return Err(FxError::at(fixpt_read::Span::new(fixpt_read::FileId(0), 0, 0), "one type"));
        };
        self.parse_type(form)
    }

    /// An effect written as text.
    pub fn effect_of_str(&mut self, text: &str) -> R<Effect> {
        let forms = self.read(text)?;
        self.parse_effect(&forms[0])
    }

    /// The region written as text.
    pub fn region_of_str(&mut self, text: &str) -> R<Region> {
        let forms = self.read(text)?;
        self.parse_region(&forms[0])
    }

    pub(crate) fn bool_ty(&self) -> TyId {
        self.bool_
    }

    /// What `s` is where it is used: its innermost binding; nothing, if that
    /// is a global broken by a redefinition (`broken`).
    pub(crate) fn lookup(&self, s: Sym) -> Option<TyId> {
        let hidden = self.hidden.map(|(e, _)| e);
        let i = (0..self.env.len()).rev().find(|i| self.env[*i].0 == s && !hidden.is_some_and(|(a, b)| (a..b).contains(i)))?;
        if self.broken.get(&s).is_some_and(|(b, _)| *b == i) {
            return None;
        }
        Some(self.env[i].1)
    }

    /// The type of the global `s` as defined now, broken or not.
    pub fn global_type(&self, s: Sym) -> Option<TyId> {
        self.env.iter().rposition(|(n, _)| *n == s).filter(|i| *i >= self.standard_len).map(|i| self.env[i].1)
    }

    /// Where the environment is now, to go back to (`rollback`).
    pub fn mark(&self) -> usize {
        self.env.len()
    }

    /// The environment as it was at `mark`: what was bound since, unbound.
    pub fn rollback(&mut self, mark: usize) {
        self.truncate_env(mark);
        self.broken.retain(|_, (i, _)| *i < mark);
    }

    /// The global `s`, as defined now, broken: a use of it is an error
    /// saying `why`, until it is defined again.
    pub fn break_global(&mut self, s: Sym, why: String) {
        if let Some(i) = self.env.iter().rposition(|(n, _)| *n == s) {
            self.broken.insert(s, (i, why));
        }
    }

    /// Whether the global `s` is broken, and why.
    pub fn broken_why(&self, s: Sym) -> Option<&str> {
        let i = self.env.iter().rposition(|(n, _)| *n == s)?;
        self.broken.get(&s).filter(|(b, _)| *b == i).map(|(_, w)| w.as_str())
    }

    // ------------------------------------------------------------ synthesis
    /// What `e` is, and what evaluating it does.
    pub fn synth(&mut self, e: ExpId) -> R<(TyId, Effect)> {
        if self.holes.is_some() {
            self.at_hole(e, None)?;
        }
        let (t, eff) = self.synth_node(e)?;
        let eff = self.frozen(e, eff)?;
        self.facts.effects.insert(e, eff.clone());
        Ok((t, eff))
    }

    /// A `letrec`: its group checked at the types declared, then its body,
    /// checked against `expected` where one is given (as a `let`'s is), or
    /// synthesised.
    pub(crate) fn letrec(&mut self, e: ExpId, bindings: &[(Sym, TyId, ExpId)], body: ExpId, expected: Option<TyId>) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let mut resolved = Vec::new();
        for (n, t, init) in bindings {
            resolved.push((*n, self.resolve_selects(*t, span)?, *init));
        }
        self.letrec_with(e, &resolved, body, expected, true)
    }

    /// [`letrec`](Self::letrec), and if a procedure of the group does not
    /// check at its type, and `infer`, the group again at its types with
    /// the globals each reads found, as `define*` finds them
    /// ([`letrec_found`](Self::letrec_found)); the first error if that
    /// finds nothing new.
    fn letrec_with(&mut self, e: ExpId, bindings: &[(Sym, TyId, ExpId)], body: ExpId, expected: Option<TyId>, infer: bool) -> R<(TyId, Effect)> {
        let depth = self.env.len();
        self.env.extend(bindings.iter().map(|(n, t, _)| (*n, *t)));
        self.known.extend(bindings.iter().enumerate().map(|(i, (n, _, _))| (*n, depth + i)));
        let rdepth = self.recursive.len();
        // Only lambdas: then nothing runs before every binding
        // exists, and no one sees the knot tied.
        if let Some((n, _, init)) = bindings.iter().find(|(_, _, init)| !self.is_lambda(*init)) {
            self.truncate_env(depth);
            return Err(FxError::at(self.arena.span_of(*init), letrec_not_lambda(self.interner.name(*n))));
        }
        // A group whose every run ends needs no `spin`.
        self.note_termination(bindings);
        // An error, and whether a procedure of the group made it.
        let r = (|| {
            let mut eff = Effect::pure();
            for (n, t, init) in bindings {
                let ie = self.check(*init, *t).map_err(|err| (self.declared_error(*n, *t, *init, err), true))?;
                eff = eff.union(&ie);
            }
            // The body's calls of the group are not recursion.
            self.recursive.truncate(rdepth);
            let (bt, be) = match expected {
                Some(want) => (want, self.check(body, want).map_err(|err| (err, false))?),
                None => self.synth(body).map_err(|err| (err, false))?,
            };
            Ok((bt, eff.union(&be)))
        })();
        self.recursive.truncate(rdepth);
        self.truncate_env(depth);
        let (t, eff) = match r {
            Ok(r) => r,
            Err((err, true)) if infer => match self.letrec_found(bindings) {
                Some(found) => return self.letrec_with(e, &found, body, expected, false),
                None => return Err(err),
            },
            Err((err, _)) => return Err(err),
        };
        let eff = self.mask(e, &eff, t);
        Ok((t, eff))
    }

    /// A `letrec` group's types with the globals each procedure reads put
    /// in its latent effect, as `define*` finds them for a definition: each
    /// checked as though its type said it read any global, and the globals
    /// its body read taken, again until the group's calls of each other
    /// add none. `None` if that fails, or adds nothing.
    fn letrec_found(&mut self, bindings: &[(Sym, TyId, ExpId)]) -> Option<Vec<(Sym, TyId, ExpId)>> {
        let any = Effect::atom(Atom::Read(Region::Globals));
        let mut types: Vec<TyId> = bindings.iter().map(|b| b.1).collect();
        for _ in 0..=bindings.len() + 1 {
            let depth = self.env.len();
            self.env.extend(bindings.iter().zip(&types).map(|((n, _, _), t)| (*n, *t)));
            self.known.extend(bindings.iter().enumerate().map(|(i, (n, _, _))| (*n, depth + i)));
            let rdepth = self.recursive.len();
            let group: Vec<(Sym, TyId, ExpId)> = bindings.iter().zip(&types).map(|((n, _, x), t)| (*n, *t, *x)).collect();
            self.note_termination(&group);
            let mut next = Vec::new();
            let mut ok = true;
            for (i, (_, declared, init)) in bindings.iter().enumerate() {
                let wide = self.with_latent(types[i], &any).unwrap_or(types[i]);
                if self.check(*init, wide).is_err() {
                    ok = false;
                    break;
                }
                let reads = self.globals_read_by(*init);
                next.push(self.with_latent(*declared, &reads).unwrap_or(*declared));
            }
            self.recursive.truncate(rdepth);
            self.truncate_env(depth);
            if !ok {
                return None;
            }
            let same = |a: &[TyId], b: &[TyId]| a.iter().zip(b).all(|(x, y)| self.latent_of(*x) == self.latent_of(*y));
            if same(&next, &types) {
                let declared: Vec<TyId> = bindings.iter().map(|b| b.1).collect();
                if same(&next, &declared) {
                    return None;
                }
                return Some(bindings.iter().zip(next).map(|((n, _, x), t)| (*n, t, *x)).collect());
            }
            types = next;
        }
        None
    }

    /// The latent effect of `t`, a `subr` under any `poly`s.
    pub(crate) fn latent_of(&self, t: TyId) -> Option<Effect> {
        match self.arena.get(self.arena.resolve(t)) {
            Ty::Poly { body, .. } => self.latent_of(*body),
            Ty::Subr { effect, .. } => Some(effect.clone()),
            _ => None,
        }
    }

    /// The second line of an "is expected here" message, where `got` and
    /// `want` are procedures: the atoms of `got`'s latent effect that
    /// `want`'s does not cover, which the two whole types can bury.
    pub(crate) fn effect_delta(&self, got: TyId, want: TyId) -> String {
        let (Some(g), Some(w)) = (self.latent_of(got), self.latent_of(want)) else { return String::new() };
        let beyond = Effect(g.0.into_iter().filter(|a| !Effect::atom(*a).within(&w)).collect());
        if beyond.is_pure() { String::new() } else { format!("\n  beyond what is expected, it has {}", self.show_effect(&beyond)) }
    }

    /// `eff` with what it does to data frozen in the heap taken out, since
    /// reading it and making it are pure; or an error, if it writes frozen
    /// data. What it does to data frozen into a place stays: the place
    /// ends, and the atom is what ties a closure that reads the data to it
    /// (`docs/research/soundness-findings.md`, F2), until masking removes
    /// it where the place is no longer seen.
    pub(crate) fn frozen(&self, e: ExpId, eff: Effect) -> R<Effect> {
        if !eff.0.iter().any(|a| a.region().is_some_and(Region::is_frozen)) {
            return Ok(eff);
        }
        if eff.0.iter().any(|a| matches!(a, Atom::Write(r) if r.is_frozen())) {
            return Err(FxError::at(self.arena.span_of(e), "this writes frozen data, whose region is `const`"));
        }
        let in_heap = |r: &Region| matches!(r, Region::Frozen(None, _));
        Ok(Effect(eff.0.into_iter().filter(|a| !matches!(a, Atom::Read(r) | Atom::Alloc(r) | Atom::Await(r) if in_heap(r))).collect()))
    }

    /// A summary of each expression's effect, for a compiler, by where it
    /// starts and ends, each a stronger claim on what the code may do than
    /// the one before, so that the greater of two is the safe one: 0 pure
    /// (no atom at all, so no `spin` either), 1 reads only, 2 anything
    /// else, 3 anything else that may also keep its continuation for later
    /// (`comefrom`), write a global, or do what an effect variable stands
    /// for, which a global's value may change across. Where two expressions
    /// have one span, the greater. `check-types.fx`'s `checked-effects` says the
    /// same.
    pub fn effect_summaries(&self) -> HashMap<(u32, u32), u8> {
        let mut out: HashMap<(u32, u32), u8> = HashMap::new();
        for (e, eff) in &self.facts.effects {
            let s = if eff.is_pure() {
                0
            } else if eff.0.iter().all(|a| matches!(a, Atom::Read(_))) {
                1
            } else if eff.0.iter().any(|a| matches!(a, Atom::Comefrom(_) | Atom::Var(_) | Atom::App(_) | Atom::Write(Region::Global(_) | Region::Globals))) {
                3
            } else {
                2
            };
            let span = self.arena.span_of(*e);
            let k = out.entry((span.start, span.end)).or_insert(s);
            *k = (*k).max(s);
        }
        out
    }

    /// Whether `s`, where it is used, is the initial environment's binding.
    pub(crate) fn is_standard(&self, s: Sym) -> bool {
        self.env.iter().rposition(|(n, _)| *n == s).is_some_and(|i| i < self.standard_len)
    }

    fn synth_node(&mut self, e: ExpId) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        match self.arena.exp_at(e).clone() {
            Exp::Var(s) => match self.lookup(s) {
                Some(t) => Ok((t, self.naming_effect(s, t))),
                None => match self.broken_why(s) {
                    Some(why) => Err(FxError::at(span, format!("`{}` is broken, {why}: define it again to use it", self.interner.name(s)))),
                    None => Err(FxError::at(span, format!("unbound variable `{}`", self.interner.name(s)))),
                },
            },
            Exp::Int(_) => Ok((self.int, Effect::pure())),
            Exp::Bool(_) => Ok((self.bool_, Effect::pure())),
            Exp::Str(_) => Ok((self.string, Effect::pure())),
            Exp::Char(_) => Ok((self.char_, Effect::pure())),
            Exp::Float(_) => Ok((self.f64_, Effect::pure())),
            Exp::Symbol(_) => Ok((self.symbol, Effect::pure())),
            Exp::Unit => Ok((self.unit, Effect::pure())),
            Exp::Lambda { .. } => self.synth_lambda(e, None),
            Exp::RLambda { region, lambda } => self.synth_rlambda(e, region, lambda, None),
            Exp::App { fun, args } => self.synth_app(e, fun, &args, None),
            Exp::The { ty, exp } => {
                let ty = self.resolve_selects(ty, span)?;
                let eff = self.check(exp, ty)?;
                Ok((ty, eff))
            }
            Exp::Convention { conv, exp } => {
                let (t, eff) = self.synth(exp)?;
                let t = self.arena.resolve(t);
                let Ty::Subr { conv: from, effect, params, result } = self.arena.get(t).clone() else {
                    return Err(FxError::at(span, format!("`convention` takes a procedure, and this is a {}", self.show_ty(t))));
                };
                if from != conv {
                    self.convert_at(e, conv, params.len());
                }
                Ok((self.arena.ty(Ty::Subr { conv, effect, params, result }), eff))
            }
            Exp::PLambda { binders, body } => {
                let (t, eff) = self.synth(body)?;
                if !self.generalizable(body, &eff) {
                    return Err(FxError::at(span, format!("a `plambda` body must be pure, and this one has {}", self.show_effect(&eff))));
                }
                Ok((self.arena.ty(Ty::Poly { binders, body: t }), eff))
            }
            Exp::Proj { body, args } => {
                let (t, eff) = self.synth(body)?;
                let Ty::Poly { binders, body: inner } = self.arena.get(t).clone() else {
                    return Err(FxError::at(span, format!("`proj` needs a polymorphic value, not a {}", self.show_ty(t))));
                };
                if binders.len() != args.len() {
                    return Err(FxError::at(span, format!("this `poly` binds {} description(s); `proj` gave {}", binders.len(), args.len())));
                }
                let mut map = HashMap::new();
                for ((v, k), d) in binders.iter().zip(args) {
                    // A function given as a `select`: resolved first.
                    let d = match d {
                        D::Fun(f) | D::Type(f) if matches!(k, Kind::Arrow(_)) && matches!(self.arena.get(f), Ty::Select(..)) => {
                            D::Fun(self.resolve_selects(f, span)?)
                        }
                        d => d,
                    };
                    if !self.d_fits(&d, *k) {
                        let word = self.kind_word(*k);
                        return Err(FxError::at(span, format!("`{}` is bound as a {word}, and the description given is not one", self.interner.name(self.arena.dvar_name(*v)))));
                    }
                    map.insert(*v, d);
                }
                self.check_bounds(&binders, &map, span)?;
                self.check_finite_sizes(&binders, &map, inner, span)?;
                let result = self.subst(inner, &map);
                self.no_knot(result, span)?;
                let eff = self.mask(e, &eff, result);
                Ok((result, eff))
            }
            Exp::If { test, then, els } => {
                let (tt, te) = self.synth(test)?;
                if !self.subtype(tt, self.bool_) {
                    return Err(FxError::at(self.arena.span_of(test), "an `if` test must be a bool"));
                }
                let certified = self.acyclic_test(test);
                self.certified.extend(certified);
                let lengths = self.length_test(test);
                self.certified_lengths.extend(lengths.clone());
                let nats = self.nat_test(test);
                self.certified_nats.extend(nats);
                let (yes, no) = self.test_facts(test);
                let depth = self.size_facts.len();
                self.size_facts.extend(yes);
                let a = self.synth(then);
                self.size_facts.truncate(depth);
                if certified.is_some() {
                    self.certified.pop();
                }
                if lengths.is_some() {
                    self.certified_lengths.pop();
                }
                if nats.is_some() {
                    self.certified_nats.pop();
                }
                let (a, ae) = a?;
                self.size_facts.extend(no);
                let b = self.synth(els);
                self.size_facts.truncate(depth);
                let (b, be) = b?;
                let t = if self.subtype(a, b) {
                    b
                } else if self.subtype(b, a) {
                    a
                } else if let Some(t) = self.nat_join(a, b) {
                    t
                } else {
                    return Err(FxError::at(span, format!("the branches are a {} and a {}", self.show_ty(a), self.show_ty(b))));
                };
                let eff = self.mask(e, &te.union(&ae).union(&be), t);
                Ok((t, eff))
            }
            Exp::Letrec { bindings, body } => self.letrec(e, &bindings, body, None),
            Exp::Let { bindings, body } => {
                let mut eff = Effect::pure();
                let mut bound = Vec::new();
                // Where the bindings will be in `env`.
                let base = self.env.len();
                for (i, (n, init)) in bindings.iter().enumerate() {
                    let (t, ie) = self.synth(*init)?;
                    eff = eff.union(&ie);
                    if self.is_lambda(*init) {
                        self.known.insert((*n, base + i));
                    }
                    bound.push((*n, t));
                }
                let depth = self.env.len();
                let named = self.skolems.len();
                for (n, t) in bound {
                    let t = self.name_nat(n, t);
                    self.env.push((n, t));
                }
                let r = self.synth(body);
                self.truncate_env(depth);
                let r = r.and_then(|(t, be)| Ok((self.forget_nats(named, t, span)?, be)));
                self.skolems.truncate(named);
                let (t, be) = r?;
                let eff = self.mask(e, &eff.union(&be), t);
                Ok((t, eff))
            }
            Exp::Prompt { tag, body, handler } => self.synth_prompt(e, tag, body, handler),
            Exp::Module(items) => self.synth_module(e, &items),
            Exp::With { module, body } => self.synth_with(e, module, body),
            // The region's name is a variable too, of type `(place r)`,
            // when the form makes a place: to allocate in (`rcons`).
            Exp::LetRegion { form, region, body } => {
                let name = self.arena.dvar_name(region);
                let rt = self.arena.ty(Ty::Place(Region::Var(region)));
                let depth = self.env.len();
                if !matches!(form, RegionForm::Region | RegionForm::Freeze(_)) {
                    self.env.push((name, rt));
                }
                if matches!(form, RegionForm::Freeze(_)) {
                    self.freezing.push((region, false));
                }
                let r = self.synth(body);
                let written = if matches!(form, RegionForm::Freeze(_)) { self.freezing.pop().expect("pushed").1 } else { true };
                self.truncate_env(depth);
                let (t, eff) = r?;
                // A `letfreeze`'s value leaves with its region's data frozen:
                // `r` made `const`, unless something in it could still write.
                let t = if let RegionForm::Freeze(into) = form {
                    if self.writes_in(t, Region::Var(region)) {
                        let name = self.interner.name(name);
                        return Err(FxError::at(span, format!("the value of `letfreeze {name}` could still write its region's data: its type is {}", self.show_ty(t))));
                    }
                    self.subst(t, &HashMap::from([(region, D::Region(Region::Frozen(into, !written)))]))
                } else {
                    t
                };
                self.close_region(e, form.keyword(), region, t, eff)
            }
            Exp::Bloblet { op, args } => self.synth_bloblet(e, op, &args, None),
            Exp::Product(fields) => {
                let mut eff = Effect::pure();
                let mut tys = Vec::new();
                for (l, x) in &fields {
                    let (t, xe) = self.synth(*x)?;
                    eff = eff.union(&xe);
                    tys.push((*l, t));
                }
                let t = self.arena.ty(Ty::Product(tys));
                let eff = self.mask(e, &eff, t);
                Ok((t, eff))
            }
            Exp::Extract(x, label) => {
                let (pt, eff) = self.synth(x)?;
                let Ty::Product(fields) = self.arena.get(pt).clone() else {
                    return Err(FxError::at(self.arena.span_of(x), format!("a product is expected here, and this is a {}", self.show_ty(pt))));
                };
                let Some(i) = fields.iter().position(|(l, _)| *l == label) else {
                    return Err(FxError::at(span, format!("a {} has no `{}`", self.show_ty(pt), self.interner.name(label))));
                };
                self.facts.field_index.insert(e, i);
                let t = fields[i].1;
                let eff = self.mask(e, &eff, t);
                Ok((t, eff))
            }
            Exp::Sum(tag, x) => {
                let (t, eff) = self.synth(x)?;
                let t = self.arena.ty(Ty::Sum(vec![(tag, t)]));
                let eff = self.mask(e, &eff, t);
                Ok((t, eff))
            }
            Exp::TagCase { scrutinee, arms, els } => self.synth_tagcase(e, scrutinee, &arms, &els, None),
            Exp::Begin(items) => {
                let mut eff = Effect::pure();
                let mut last = self.unit;
                for i in &items {
                    let (t, ie) = self.synth(*i)?;
                    eff = eff.union(&ie);
                    last = t;
                }
                let eff = self.mask(e, &eff, last);
                Ok((last, eff))
            }
        }
    }

    // --------------------------------------------------------------- masking
    /// Remove from `effect` what cannot be observed outside expression `e`,
    /// whose type is `result`. See the module docs for the rule.
    /// `(letrena r …)`'s or `(letreap r …)`'s body, of type `t` and effect
    /// `eff`, closed: its
    /// value may not mention `r`, and no continuation captured in it may
    /// outlive it; what it does to `r` is masked, as nothing outside can
    /// name `r`.
    pub(crate) fn close_region(&mut self, e: ExpId, form: &str, r: DVar, t: TyId, eff: Effect) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let name = self.interner.name(self.arena.dvar_name(r)).to_string();
        let mut in_t = HashSet::new();
        self.regions_in(t, &mut in_t);
        if in_t.contains(&Region::Var(r)) {
            return Err(FxError::at(span, region_escapes(form, &name, &self.show_ty(t))));
        }
        let masked = self.mask(e, &eff, t);
        if masked.0.iter().any(|a| matches!(a, Atom::Comefrom(_))) {
            return Err(FxError::at(span, region_captured(form, &name, &self.show_effect(&masked))));
        }
        Ok((t, masked))
    }

    /// Whether a `plambda` body `x` with effect `eff` may be generalized:
    /// pure, as the value restriction has it; or an `rlambda`, under
    /// ascriptions and other `plambda`s, whose effect only allocates. Making
    /// a closure makes no mutable data a type could be generalized over: it
    /// holds only variables bound outside.
    pub(crate) fn generalizable(&self, mut x: ExpId, eff: &Effect) -> bool {
        if eff.is_pure() {
            return true;
        }
        loop {
            match self.arena.exp_at(x) {
                Exp::PLambda { body, .. } | Exp::The { exp: body, .. } => x = *body,
                Exp::RLambda { .. } => return eff.0.iter().all(|a| matches!(a, Atom::Alloc(_))),
                _ => return false,
            }
        }
    }

    /// An `rlambda`'s type: its `lambda`'s, told `expected`'s parameter and
    /// result types if it is a subroutine's, with `(read R)` in its latent
    /// effect, since calling it reads the closure; making it allocates in
    /// `R`, the region `region` names.
    pub(crate) fn synth_rlambda(&mut self, e: ExpId, region: ExpId, lambda: ExpId, expected: Option<TyId>) -> R<(TyId, Effect)> {
        let (rt, reff) = self.synth(region)?;
        let Ty::Place(g) = self.arena.get(rt).clone() else {
            return Err(FxError::at(self.arena.span_of(region), format!("a region is expected here, and this is a {}", self.show_ty(rt))));
        };
        let hint = expected.and_then(|t| self.arena.get(t).as_subr());
        let (lt, _) = match hint {
            Some((_, want, result)) => {
                let Exp::Lambda { params, .. } = self.arena.exp_at(lambda) else { unreachable!("parsed") };
                if want.len() != params.len() {
                    let span = self.arena.span_of(e);
                    return Err(FxError::at(span, format!("a subroutine of {} parameter(s) is expected, and this `rlambda` has {}", want.len(), params.len())));
                }
                self.synth_lambda_as(lambda, Some(&want), Some(result))?
            }
            None => self.synth_lambda(lambda, None)?,
        };
        let Ty::Subr { conv, mut effect, params, result } = self.arena.get(lt).clone() else { unreachable!("a lambda's type") };
        effect.0.insert(Atom::Read(g));
        let t = self.arena.ty(Ty::Subr { conv, effect, params, result });
        let eff = reff.union(&Effect::atom(Atom::Alloc(g)));
        let eff = self.mask(e, &eff, t);
        Ok((t, eff))
    }

    /// Whether `x` is a lambda, under any type abstractions and ascriptions.
    /// Naming `s`: pure, but for a member of a recursive group that may not
    /// end, named in the group. Called, the call says `spin`; given away,
    /// whoever calls it could loop through it, so naming it does.
    pub(crate) fn naming_effect(&self, s: Sym, t: TyId) -> Effect {
        let mut e = Effect::pure();
        if self.recursive.contains(&(s, t)) {
            e.0.insert(Atom::Spin);
        }
        if self.globals_effects && self.env.iter().rposition(|(n, _)| *n == s).is_some_and(|i| self.global_slots.contains(&i)) {
            e.0.insert(Atom::Read(Region::Global(s)));
        }
        e
    }

    /// Bind `name`, at top level, to a value of type `t`: a global.
    pub(crate) fn push_global(&mut self, name: Sym, t: TyId) {
        let t = self.name_module(name, t);
        self.global_slots.insert(self.env.len());
        self.env.push((name, t));
    }

    /// Whether the group `bindings` ends; if not, its members are recursion
    /// that says `spin`, and why is kept for an error.
    pub(crate) fn note_termination(&mut self, bindings: &[(Sym, TyId, ExpId)]) {
        if let Err(why) = self.termination(bindings) {
            for (n, t, _) in bindings {
                self.recursive.push((*n, *t));
                self.spin_why.push(((*n, *t), why.clone()));
            }
        }
    }

    /// An error checking `init` against `t`, the type `n` is declared: at
    /// `init` itself it says so, and, if it is about `spin` and `n`'s group
    /// may not end, why not.
    pub(crate) fn declared_error(&self, n: Sym, t: TyId, init: ExpId, err: FxError) -> FxError {
        if err.span != self.arena.span_of(init) {
            return err;
        }
        let mut msg = format!("`{}` is declared a {}: {}", self.interner.name(n), self.show_ty(t), err.message);
        if err.message.contains("spin")
            && let Some((_, why)) = self.spin_why.iter().rev().find(|(k, _)| *k == (n, t))
        {
            msg.push_str(&format!("; it may not end: {why}"));
        }
        FxError::at(err.span, msg)
    }

    pub fn is_lambda(&self, mut x: ExpId) -> bool {
        loop {
            match self.arena.exp_at(x) {
                Exp::PLambda { body, .. } | Exp::The { exp: body, .. } => x = *body,
                Exp::Lambda { .. } | Exp::RLambda { .. } => return true,
                _ => return false,
            }
        }
    }

    pub(crate) fn mask(&mut self, e: ExpId, effect: &Effect, result: TyId) -> Effect {
        // A write to a region a `letfreeze` is freezing, noted before
        // masking could hide it: that region's data may be cyclic.
        for (v, written) in self.freezing.iter_mut() {
            if effect.0.contains(&Atom::Write(Region::Var(*v))) {
                *written = true;
            }
        }
        if !self.masking || effect.is_pure() {
            return effect.clone();
        }
        let mut visible = HashSet::new();
        for v in self.free_vars(e) {
            if let Some(t) = self.lookup(v) {
                self.regions_in(t, &mut visible);
            }
        }
        let mut in_result = HashSet::new();
        self.regions_in(result, &mut in_result);
        let kept = effect
            .0
            .iter()
            .copied()
            .filter(|a| match a.region() {
                None => true,
                // Reading data frozen into a place, or awaiting it, is
                // masked as what is done to the place is: where nothing
                // outside sees the place.
                Some(r @ Region::Frozen(Some(p), _)) if !matches!(a, Atom::Write(_)) => {
                    let place = Region::Var(p);
                    visible.contains(&r)
                        || visible.contains(&place)
                        || ((in_result.contains(&r) || in_result.contains(&place)) && matches!(a, Atom::Alloc(_)))
                }
                // What else is done to frozen data is never masked: writing
                // it is an error wherever it happens (`frozen`).
                Some(Region::Frozen(..)) => true,
                // Globals' bindings are seen everywhere: never masked.
                Some(Region::Global(_) | Region::Globals) => true,
                Some(r) if visible.contains(&r) => true,
                Some(r) if in_result.contains(&r) => {
                    matches!(a, Atom::Alloc(_) | Atom::Goto(_) | Atom::Comefrom(_))
                }
                Some(_) => false,
            })
            .collect();
        let kept = Effect(kept);
        let allocates = |x: &Effect| x.0.iter().any(|a| matches!(a, Atom::Alloc(_)));
        // Masking alone does not show the allocation dead: a closure in
        // the value may hold it, its type saying nothing of the region
        // (`docs/research/soundness-findings.md`, F6). A value of data whose
        // type names the region of all it reaches holds none of it.
        if allocates(effect) && !allocates(&kept) && self.first_order(result) {
            self.facts.no_escape.insert(e);
        }
        kept
    }

    /// Whether a value of type `t` reaches only storage its type names:
    /// data, references, arrays, cells and bloblets of such, with no
    /// procedure, continuation, tag, key, generative type or type variable
    /// anywhere that could hold what its type does not say.
    fn first_order(&self, t: TyId) -> bool {
        let mut seen = HashSet::new();
        let mut stack = vec![t];
        while let Some(t) = stack.pop() {
            let t = self.arena.resolve(t);
            if !seen.insert(t) {
                continue;
            }
            match self.arena.get(t) {
                Ty::Base(_) | Ty::Nat(_) | Ty::Void | Ty::Place(_) => {}
                Ty::Pair(a, b, _) => stack.extend([*a, *b]),
                Ty::NList { elem: a, .. } | Ty::Ref(a, _) | Ty::Array(a, _) | Ty::ICell(a, _) => stack.push(*a),
                Ty::Bloblet { fields, .. } => stack.extend(fields),
                Ty::Product(ps) | Ty::Sum(ps) => stack.extend(ps.iter().map(|(_, x)| *x)),
                _ => return false,
            }
        }
        true
    }

    /// The value variables free in `e`.
    pub(crate) fn free_vars(&self, e: ExpId) -> Vec<Sym> {
        let mut out = Vec::new();
        self.free_into(e, &mut Vec::new(), &mut out);
        out
    }

    pub(crate) fn free_into(&self, e: ExpId, bound: &mut Vec<Sym>, out: &mut Vec<Sym>) {
        match self.arena.exp_at(e).clone() {
            Exp::Var(s) => {
                if !bound.contains(&s) && !out.contains(&s) {
                    out.push(s);
                }
            }
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => {}
            Exp::Lambda { params, body } => {
                let depth = bound.len();
                bound.extend(params.iter().map(|(n, _)| *n));
                self.free_into(body, bound, out);
                bound.truncate(depth);
            }
            Exp::App { fun, args } => {
                self.free_into(fun, bound, out);
                for a in args {
                    self.free_into(a, bound, out);
                }
            }
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } => self.free_into(body, bound, out),
            Exp::RLambda { region, lambda } => {
                self.free_into(region, bound, out);
                self.free_into(lambda, bound, out);
            }
            Exp::LetRegion { region, body, .. } => {
                bound.push(self.arena.dvar_name(region));
                self.free_into(body, bound, out);
                bound.pop();
            }
            Exp::If { test, then, els } => {
                for x in [test, then, els] {
                    self.free_into(x, bound, out);
                }
            }
            Exp::Letrec { bindings, body } => {
                let depth = bound.len();
                bound.extend(bindings.iter().map(|(n, _, _)| *n));
                for (_, _, init) in &bindings {
                    self.free_into(*init, bound, out);
                }
                self.free_into(body, bound, out);
                bound.truncate(depth);
            }
            // Every item sees every name, as a `letrec*`'s (`crate::modorder`).
            Exp::Module(items) => {
                let depth = bound.len();
                for item in &items {
                    match item {
                        crate::ast::ModItem::Abs { up, down, .. } => bound.extend([*up, *down]),
                        crate::ast::ModItem::Desc { .. } => {}
                        crate::ast::ModItem::Val { name, .. } => bound.push(*name),
                        crate::ast::ModItem::Rec(group) => bound.extend(group.iter().map(|(n, _, _)| *n)),
                    }
                }
                for item in &items {
                    match item {
                        crate::ast::ModItem::Val { init, .. } => self.free_into(*init, bound, out),
                        crate::ast::ModItem::Rec(group) => {
                            for (_, _, init) in group {
                                self.free_into(*init, bound, out);
                            }
                        }
                        _ => {}
                    }
                }
                bound.truncate(depth);
            }
            // The names the module gives, once it is checked; before, none,
            // so that what may be its values counts as free.
            Exp::With { module, body } => {
                if !bound.contains(&module) && !out.contains(&module) {
                    out.push(module);
                }
                let depth = bound.len();
                bound.extend(self.facts.with_vals.get(&e).into_iter().flatten().copied());
                self.free_into(body, bound, out);
                bound.truncate(depth);
            }
            Exp::Let { bindings, body } => {
                for (_, init) in &bindings {
                    self.free_into(*init, bound, out);
                }
                let depth = bound.len();
                bound.extend(bindings.iter().map(|(n, _)| *n));
                self.free_into(body, bound, out);
                bound.truncate(depth);
            }
            Exp::Begin(items) => {
                for i in items {
                    self.free_into(i, bound, out);
                }
            }
            Exp::Prompt { tag, body, handler } => {
                for x in [tag, body, handler] {
                    self.free_into(x, bound, out);
                }
            }
            Exp::The { exp, .. } | Exp::Convention { exp, .. } => self.free_into(exp, bound, out),
            Exp::Bloblet { args, .. } => {
                for a in args {
                    self.free_into(a, bound, out);
                }
            }
            Exp::Product(fields) => {
                for (_, x) in fields {
                    self.free_into(x, bound, out);
                }
            }
            Exp::Extract(x, _) | Exp::Sum(_, x) => self.free_into(x, bound, out),
            Exp::TagCase { scrutinee, arms, els } => {
                self.free_into(scrutinee, bound, out);
                for arm in &arms {
                    let depth = bound.len();
                    bound.extend(arm.names());
                    self.free_into(arm.body, bound, out);
                    bound.truncate(depth);
                }
                if let Some((y, body)) = els {
                    bound.push(y);
                    self.free_into(body, bound, out);
                    bound.pop();
                }
            }
        }
    }

    /// Every region mentioned in type `t`, following recursive types once.
    pub fn regions_in(&self, t: TyId, out: &mut HashSet<Region>) {
        let mut seen = HashSet::new();
        self.regions_walk(t, &mut seen, out);
        // Frozen data mentions the place it is in.
        let places: Vec<Region> = out.iter().filter_map(|r| match r {
            Region::Frozen(Some(p), _) => Some(Region::Var(*p)),
            _ => None,
        }).collect();
        out.extend(places);
    }

    fn regions_walk(&self, t: TyId, seen: &mut HashSet<TyId>, out: &mut HashSet<Region>) {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return;
        }
        match self.arena.get(t).clone() {
            Ty::Base(_) | Ty::Nat(_) | Ty::Void | Ty::Var(_) | Ty::Link(None) | Ty::Select(..) | Ty::ParamSel(..) => {}
            Ty::Link(Some(_)) => unreachable!("resolved"),
            // A description function applied, which cannot be looked into:
            // what it was given; a function, what its body names.
            Ty::App { args: ds, .. } => {
                for d in &ds {
                    for x in self.d_types(d) {
                        self.regions_walk(x, seen, out);
                    }
                    out.extend(self.d_regions(d));
                }
            }
            Ty::Lam { body, .. } => {
                for x in self.d_types(&body) {
                    self.regions_walk(x, seen, out);
                }
                out.extend(self.d_regions(&body));
            }
            Ty::Module { descs, vals, .. } => {
                for (_, x) in descs.iter().chain(&vals) {
                    self.regions_walk(*x, seen, out);
                }
            }
            Ty::Subr { effect, params, result, .. } => {
                out.extend(effect.0.iter().filter_map(|a| a.region()));
                for p in params {
                    self.regions_walk(p, seen, out);
                }
                self.regions_walk(result, seen, out);
            }
            Ty::Poly { body, .. } => self.regions_walk(body, seen, out),
            Ty::Ref(a, r) | Ty::Array(a, r) | Ty::ICell(a, r) => {
                out.insert(r);
                self.regions_walk(a, seen, out);
            }
            Ty::Place(r) => {
                out.insert(r);
            }
            Ty::Pair(a, b, r) => {
                out.insert(r);
                self.regions_walk(a, seen, out);
                self.regions_walk(b, seen, out);
            }
            Ty::PromptTag { answer: a, payload: b, effect, region: r }
            | Ty::Composable { arg: b, answer: a, effect, region: r } => {
                out.insert(r);
                out.extend(effect.0.iter().filter_map(|x| x.region()));
                self.regions_walk(a, seen, out);
                self.regions_walk(b, seen, out);
            }
            Ty::MarkKey(t, r) => {
                out.insert(r);
                self.regions_walk(t, seen, out);
            }
            Ty::Bloblet { fields, region, .. } => {
                out.insert(region);
                for f in fields {
                    self.regions_walk(f, seen, out);
                }
            }
            Ty::Product(parts) | Ty::Sum(parts) => {
                for (_, t) in parts {
                    self.regions_walk(t, seen, out);
                }
            }
            Ty::NList { elem, region, .. } => {
                out.insert(region);
                self.regions_walk(elem, seen, out);
            }
            // Transparent to safety: what its representation holds, its
            // parameters' regions standing for what it was given.
            Ty::Named { which, args } => {
                let mut inner = HashSet::new();
                self.regions_walk(self.generatives[which as usize].rep, seen, &mut inner);
                out.extend(inner.into_iter().filter(|r| !self.is_generative_param(*r)));
                for d in args {
                    match d {
                        D::Type(t) => self.regions_walk(t, seen, out),
                        D::Region(r) => {
                            out.insert(r);
                        }
                        D::Effect(e) => out.extend(e.0.iter().filter_map(|a| a.region())),
                        D::Conv(_) => {}
                        D::Size(_) => {}
                        D::Fun(_) => {
                            for x in self.d_types(&d) {
                                self.regions_walk(x, seen, out);
                            }
                            out.extend(self.d_regions(&d));
                        }
                    }
                }
            }
        }
    }

    /// The regions of everything in `t` that can be written: storage a
    /// generative type's representation may keep what it was given in.
    fn storage_regions(&self, t: TyId, seen: &mut HashSet<TyId>, out: &mut Vec<Region>) {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return;
        }
        let add = |r: Region, out: &mut Vec<Region>| {
            if !out.contains(&r) {
                out.push(r);
            }
        };
        let kids: Vec<TyId> = match self.arena.get(t).clone() {
            Ty::Ref(a, r) | Ty::Array(a, r) | Ty::ICell(a, r) | Ty::MarkKey(a, r) => {
                add(r, out);
                vec![a]
            }
            Ty::Pair(a, b, r) => {
                if !r.is_frozen() {
                    add(r, out);
                }
                vec![a, b]
            }
            Ty::Bloblet { fields, frozen, region } => {
                if !frozen {
                    add(region, out);
                }
                fields
            }
            Ty::Subr { params, result, .. } => params.into_iter().chain([result]).collect(),
            Ty::NList { elem, .. } => vec![elem],
            Ty::Poly { body, .. } => vec![body],
            Ty::Product(ps) | Ty::Sum(ps) => ps.into_iter().map(|(_, x)| x).collect(),
            Ty::PromptTag { answer: a, payload: b, .. } | Ty::Composable { arg: a, answer: b, .. } => vec![a, b],
            Ty::Named { which, args } => [self.generatives[which as usize].rep]
                .into_iter()
                .chain(args.iter().flat_map(|d| self.d_types(d)))
                .collect(),
            Ty::App { args, .. } => args.iter().flat_map(|d| self.d_types(d)).collect(),
            _ => vec![],
        };
        for k in kids {
            self.storage_regions(k, seen, out);
        }
    }

    /// Whether `t` is data: built only from base types, `datum`, products
    /// and sums, and pairs and bloblets that are frozen, of data; and type
    /// variables of kind `data`. No procedure, no storage that can be
    /// written, no generative type.
    pub(crate) fn is_data(&self, t: TyId) -> bool {
        self.data_walk(t, &mut HashSet::new(), None)
    }

    /// Whether `t` is data at `place` (a place variable, or `heap`): data
    /// whose frozen parts are in the heap or in `place`, so that reading it
    /// reads no other place (`(t data p)`, F13).
    pub(crate) fn is_data_at(&self, t: TyId, place: Region) -> bool {
        self.data_walk(t, &mut HashSet::new(), Some(place))
    }

    /// Where data at region `r` is: the place it is frozen into, or the
    /// place or region it was made at, or else the heap.
    fn data_place(r: Region) -> Region {
        match r {
            Region::Frozen(Some(p), _) | Region::Var(p) => Region::Var(p),
            _ => Region::Heap,
        }
    }

    /// Where the data a `data` variable stands for is: its bound, or the heap.
    fn data_var_place(&self, v: DVar) -> Region {
        self.arena.bound(v).unwrap_or(Region::Heap)
    }

    fn data_walk(&self, t: TyId, seen: &mut HashSet<TyId>, place: Option<Region>) -> bool {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return true;
        }
        let here = |q: Region| place.is_none_or(|p| q == Region::Heap || q == p);
        match self.arena.get(t).clone() {
            Ty::Base(_) | Ty::Nat(_) | Ty::Void => true,
            Ty::Var(v) => self.arena.is_data_var(v) && here(self.data_var_place(v)),
            Ty::Product(ps) | Ty::Sum(ps) => ps.iter().all(|(_, x)| self.data_walk(*x, seen, place)),
            Ty::Pair(a, b, r) => {
                r.is_frozen() && here(Self::data_place(r)) && self.data_walk(a, seen, place) && self.data_walk(b, seen, place)
            }
            Ty::Bloblet { fields, frozen, region } => {
                frozen && here(Self::data_place(region)) && fields.iter().all(|f| self.data_walk(*f, seen, place))
            }
            Ty::NList { elem, region, .. } => here(Self::data_place(region)) && self.data_walk(elem, seen, place),
            _ => false,
        }
    }

    /// The places, other than the heap, that data `t`'s parts are in.
    pub(crate) fn data_places(&self, t: TyId, seen: &mut HashSet<TyId>, out: &mut Vec<Region>) {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return;
        }
        let mut note = |q: Region| {
            if q != Region::Heap && !out.contains(&q) {
                out.push(q);
            }
        };
        match self.arena.get(t).clone() {
            Ty::Var(v) if self.arena.is_data_var(v) => note(self.data_var_place(v)),
            Ty::Product(ps) | Ty::Sum(ps) => ps.iter().for_each(|(_, x)| self.data_places(*x, seen, out)),
            Ty::Pair(a, b, r) => {
                note(Self::data_place(r));
                self.data_places(a, seen, out);
                self.data_places(b, seen, out);
            }
            Ty::Bloblet { fields, region, .. } => {
                note(Self::data_place(region));
                fields.iter().for_each(|f| self.data_places(*f, seen, out));
            }
            Ty::NList { elem, region, .. } => {
                note(Self::data_place(region));
                self.data_places(elem, seen, out);
            }
            _ => {}
        }
    }

    /// If `test` is `(acyclic? v)`, the variable, as the binding it is.
    pub(crate) fn acyclic_test(&self, test: ExpId) -> Option<(Sym, usize)> {
        self.certifying_test(test, "acyclic?")
    }

    /// If `test` is `(nat? v)`, the variable, as the binding it is.
    pub(crate) fn nat_test(&self, test: ExpId) -> Option<(Sym, usize)> {
        self.certifying_test(test, "nat?")
    }

    /// If `test` is `(op v)`, `op` standard, the variable, as the binding
    /// it is.
    fn certifying_test(&self, test: ExpId, name: &str) -> Option<(Sym, usize)> {
        let Exp::App { fun, args } = self.arena.exp_at(test) else { return None };
        let mut f = *fun;
        while let Exp::Proj { body, .. } | Exp::The { exp: body, .. } = self.arena.exp_at(f) {
            f = *body;
        }
        match (self.arena.exp_at(f), &args[..]) {
            (Exp::Var(op), [a]) if self.interner.name(*op) == name && self.is_standard(*op) => match self.arena.exp_at(*a) {
                Exp::Var(v) => Some((*v, self.env.iter().rposition(|(n, _)| n == v)?)),
                _ => None,
            },
            _ => None,
        }
    }

    /// If `test` is `(length-is? v k)`, the variable, as the binding it is,
    /// and the length, as a size.
    pub(crate) fn length_test(&self, test: ExpId) -> Option<(Sym, usize, Size)> {
        let Exp::App { fun, args } = self.arena.exp_at(test) else { return None };
        match (self.arena.exp_at(*fun), &args[..]) {
            (Exp::Var(op), [a, n]) if self.interner.name(*op) == "length-is?" && self.is_standard(*op) => self.length_arg(*a, *n),
            _ => None,
        }
    }

    /// `v` and `k` of `(length-is? v k)` or `(certify-length v k)`: the
    /// variable, its binding, and the length, a natural literal or a
    /// variable of type `(nat s)`.
    pub(crate) fn length_arg(&self, a: ExpId, n: ExpId) -> Option<(Sym, usize, Size)> {
        let Exp::Var(v) = self.arena.exp_at(a) else { return None };
        if !matches!(self.arena.exp_at(n), Exp::Int(_) | Exp::Var(_)) {
            return None;
        }
        Some((*v, self.env.iter().rposition(|(x, _)| x == v)?, self.nat_size(n)?))
    }

    /// `t` with its frozen regions made finite: what data `acyclic?` has
    /// found acyclic is.
    pub(crate) fn finitized(&mut self, t: TyId) -> TyId {
        self.finitize_memo(t, &mut HashMap::new())
    }

    fn finitize_memo(&mut self, t: TyId, memo: &mut HashMap<TyId, TyId>) -> TyId {
        let t = self.arena.resolve(t);
        if let Some(x) = memo.get(&t) {
            return *x;
        }
        let fin = |r: Region| match r {
            Region::Frozen(p, false) => Region::Frozen(p, true),
            r => r,
        };
        let ty = self.arena.get(t).clone();
        if !matches!(ty, Ty::Pair(..) | Ty::Product(_) | Ty::Sum(_) | Ty::Bloblet { .. }) {
            return t;
        }
        let slot = self.arena.ty(Ty::Link(None));
        memo.insert(t, slot);
        let new = match ty {
            Ty::Pair(a, b, r) => Ty::Pair(self.finitize_memo(a, memo), self.finitize_memo(b, memo), fin(r)),
            Ty::Product(ps) => Ty::Product(ps.into_iter().map(|(l, x)| (l, self.finitize_memo(x, memo))).collect()),
            Ty::Sum(ps) => Ty::Sum(ps.into_iter().map(|(l, x)| (l, self.finitize_memo(x, memo))).collect()),
            Ty::Bloblet { fields, frozen, region } => Ty::Bloblet {
                fields: fields.into_iter().map(|f| self.finitize_memo(f, memo)).collect(),
                frozen,
                region: fin(region),
            },
            other => other,
        };
        let id = self.arena.ty(new);
        self.arena.set_link(slot, id);
        slot
    }

    /// Whether `r` is, or is frozen into, a generative type's parameter.
    fn is_generative_param(&self, r: Region) -> bool {
        let v = match r {
            Region::Var(v) | Region::Frozen(Some(v), _) => v,
            _ => return false,
        };
        self.generatives.iter().any(|g| g.params.iter().any(|(p, _)| *p == v))
    }

    /// The `which`th generative type's representation, for `args`.
    pub(crate) fn unfold(&mut self, which: u32, args: &[D]) -> TyId {
        let g = self.generatives[which as usize].clone();
        let map: HashMap<DVar, D> = g.params.iter().map(|(v, _)| *v).zip(args.iter().cloned()).collect();
        self.subst(g.rep, &map)
    }

    /// Whether the `which`th generative type's representation bears out the
    /// variance declared for its parameters: each occurs only where its
    /// variance allows (a covariant one only positively, and so on).
    pub(crate) fn check_variance(&self, which: u32, span: fixpt_read::Span) -> R<()> {
        let g = &self.generatives[which as usize];
        for ((v, _), want) in g.params.iter().zip(&g.variance) {
            if *want == Variance::Inv {
                continue;
            }
            let mut found = Vec::new();
            self.polarity(g.rep, *v, Variance::Co, &mut HashSet::new(), &mut found);
            let bad = found.iter().any(|p| *p != *want);
            if bad {
                return Err(FxError::at(
                    span,
                    format!(
                        "`{}` is declared {} in `{}`, but occurs where it may not",
                        self.interner.name(self.arena.dvar_name(*v)),
                        if *want == Variance::Co { "covariant (+)" } else { "contravariant (-)" },
                        self.interner.name(g.name)
                    ),
                ));
            }
        }
        Ok(())
    }

    /// `v` anywhere in description `d`, given to a description function,
    /// which may use what it is given either way: invariantly.
    fn polarity_fun(&self, d: &D, v: DVar, seen: &mut HashSet<(TyId, u8)>, found: &mut Vec<Variance>) {
        for x in self.d_types(d) {
            self.polarity(x, v, Variance::Inv, seen, found);
        }
        let mentions = |r: &Region| matches!(r, Region::Var(x) | Region::Frozen(Some(x), _) if *x == v);
        if self.d_regions(d).iter().any(mentions)
            || self.d_effects(d).iter().any(|e| e.0.contains(&Atom::Var(v)))
            || matches!(d, D::Fun(f) if matches!(self.arena.get(*f), Ty::Var(x) if *x == v))
        {
            found.push(Variance::Inv);
        }
    }

    /// Each polarity at which `v` occurs in `t`, reached at polarity `at`.
    fn polarity(&self, t: TyId, v: DVar, at: Variance, seen: &mut HashSet<(TyId, u8)>, found: &mut Vec<Variance>) {
        let t = self.arena.resolve(t);
        let key = match at {
            Variance::Co => 0,
            Variance::Contra => 1,
            Variance::Inv => 2,
        };
        if !seen.insert((t, key)) {
            return;
        }
        let flip = |p: Variance| match p {
            Variance::Co => Variance::Contra,
            Variance::Contra => Variance::Co,
            Variance::Inv => Variance::Inv,
        };
        let eff = |e: &Effect, p: Variance, found: &mut Vec<Variance>| {
            if e.0.iter().any(|a| matches!(a, Atom::Var(x) if *x == v)) {
                found.push(p);
            }
            // In an effect function applied: either way.
            if e.0.iter().any(|a| matches!(a, Atom::App(n) if self.arena.effect_apps.mentions(*n, &|x| x == v))) {
                found.push(Variance::Inv);
            }
            if e.0.iter().any(|a| matches!(a.region(), Some(Region::Var(x)) if x == v)) {
                found.push(Variance::Inv);
            }
        };
        let reg = |r: Region, found: &mut Vec<Variance>| {
            if matches!(r, Region::Var(x) | Region::Frozen(Some(x), _) if x == v) {
                found.push(Variance::Inv);
            }
        };
        match self.arena.get(t).clone() {
            Ty::Var(x) if x == v => found.push(at),
            Ty::Subr { effect, params, result, .. } => {
                eff(&effect, at, found);
                for p in params {
                    self.polarity(p, v, flip(at), seen, found);
                }
                self.polarity(result, v, at, seen, found);
            }
            Ty::Poly { body, .. } => self.polarity(body, v, at, seen, found),
            Ty::Ref(a, r) | Ty::Array(a, r) | Ty::ICell(a, r) | Ty::MarkKey(a, r) => {
                reg(r, found);
                self.polarity(a, v, Variance::Inv, seen, found);
            }
            Ty::Pair(a, b, r) => {
                reg(r, found);
                let p = if r.is_frozen() { at } else { Variance::Inv };
                self.polarity(a, v, p, seen, found);
                self.polarity(b, v, p, seen, found);
            }
            Ty::Bloblet { fields, frozen, region } => {
                reg(region, found);
                for f in fields {
                    self.polarity(f, v, if frozen { at } else { Variance::Inv }, seen, found);
                }
            }
            Ty::Product(parts) | Ty::Sum(parts) => {
                for (_, x) in parts {
                    self.polarity(x, v, at, seen, found);
                }
            }
            Ty::PromptTag { answer: a, payload: b, effect, region }
            | Ty::Composable { arg: a, answer: b, effect, region } => {
                reg(region, found);
                eff(&effect, Variance::Inv, found);
                self.polarity(a, v, Variance::Inv, seen, found);
                self.polarity(b, v, Variance::Inv, seen, found);
            }
            Ty::Place(r) => reg(r, found),
            Ty::NList { elem, region, .. } => {
                reg(region, found);
                self.polarity(elem, v, at, seen, found);
            }
            Ty::Named { which, args } => {
                let vs = self.generatives[which as usize].variance.clone();
                for (d, w) in args.iter().zip(vs) {
                    let p = match (w, at) {
                        (Variance::Inv, _) | (_, Variance::Inv) => Variance::Inv,
                        (Variance::Co, p) => p,
                        (Variance::Contra, p) => flip(p),
                    };
                    match d {
                        D::Type(x) => self.polarity(*x, v, p, seen, found),
                        D::Region(r) => reg(*r, found),
                        D::Effect(e) => eff(e, p, found),
                        D::Size(_) | D::Conv(_) => {}
                        D::Fun(_) => self.polarity_fun(d, v, seen, found),
                    }
                }
            }
            // What a description function is given, it may use either way.
            Ty::App { fun, args } => {
                if matches!(self.arena.get(fun), Ty::Var(x) if *x == v) {
                    found.push(Variance::Inv);
                }
                for d in &args {
                    self.polarity_fun(d, v, seen, found);
                }
            }
            _ => {}
        }
    }

    /// `Ok`, unless `t` keeps, in storage at some region `r`, a procedure
    /// whose latent effect reads or awaits `r` and does not say `spin`. Such
    /// a procedure could be fetched from `r` by a procedure fetched from
    /// `r`: a knot tied through the store, a loop with no recursive call,
    /// which only its type can show (`docs/research/type-and-effect-directions.md`,
    /// R6).
    pub(crate) fn no_knot(&self, t: TyId, span: fixpt_read::Span) -> R<()> {
        let mut seen = HashSet::new();
        match self.knot_in(t, &[], &mut seen) {
            None => Ok(()),
            Some((r, p)) => {
                let r = self.show_region(r);
                Err(FxError::at(
                    span,
                    format!("a procedure kept in `{r}` reads `{r}`, so it could reach itself: it must say `spin`, and it is a {}", self.show_ty(p)),
                ))
            }
        }
    }

    fn knot_in(&self, t: TyId, kept: &[Region], seen: &mut HashSet<(TyId, Vec<Region>)>) -> Option<(Region, TyId)> {
        let t = self.arena.resolve(t);
        if !seen.insert((t, kept.to_vec())) {
            return None;
        }
        let with = |r: Region| -> Vec<Region> {
            let mut k = kept.to_vec();
            if !k.contains(&r) {
                k.push(r);
            }
            k
        };
        let reads_kept = |e: &Effect| {
            if e.0.contains(&Atom::Spin) {
                return None;
            }
            // `@globals` among the regions kept stands for every region
            // (no procedure is kept in globals' bindings).
            let everywhere = kept.contains(&Region::Globals);
            e.0.iter().find_map(|a| match a {
                Atom::Read(r) | Atom::Await(r) if kept.contains(r) => Some(*r),
                Atom::Read(r) | Atom::Await(r) if everywhere && !r.is_frozen() && !r.is_globals() => Some(*r),
                _ => None,
            })
        };
        match self.arena.get(t).clone() {
            Ty::Ref(a, r) | Ty::Array(a, r) | Ty::ICell(a, r) | Ty::MarkKey(a, r) => self.knot_in(a, &with(r), seen),
            Ty::Pair(a, b, r) => {
                let k = if r.is_frozen() { kept.to_vec() } else { with(r) };
                self.knot_in(a, &k, seen).or_else(|| self.knot_in(b, &k, seen))
            }
            Ty::Bloblet { fields, frozen, region } => {
                let k = if frozen { kept.to_vec() } else { with(region) };
                fields.iter().find_map(|f| self.knot_in(*f, &k, seen))
            }
            Ty::Product(parts) | Ty::Sum(parts) => parts.iter().find_map(|(_, x)| self.knot_in(*x, kept, seen)),
            Ty::NList { elem, .. } => self.knot_in(elem, kept, seen),
            Ty::Poly { body, .. } => self.knot_in(body, kept, seen),
            // A procedure: kept where it is, it may not read there unsaid;
            // what it takes and gives is kept nowhere yet.
            Ty::Subr { effect, params, result, .. } => reads_kept(&effect)
                .map(|r| (r, t))
                .or_else(|| params.iter().chain([&result]).find_map(|x| self.knot_in(*x, &[], seen))),
            Ty::Composable { arg, answer, effect, .. } => reads_kept(&effect)
                .map(|r| (r, t))
                .or_else(|| [arg, answer].iter().find_map(|x| self.knot_in(*x, &[], seen))),
            Ty::PromptTag { answer, payload, .. } => [answer, payload].iter().find_map(|x| self.knot_in(*x, &[], seen)),
            // Transparent to safety: its representation, and what it was
            // given, kept, cautiously, wherever its representation keeps
            // anything and in every region it was given.
            Ty::Named { which, args } => {
                let rep = self.generatives[which as usize].rep;
                let mut k = kept.to_vec();
                let mut storage = Vec::new();
                self.storage_regions(rep, &mut HashSet::new(), &mut storage);
                for r in storage.into_iter().chain(args.iter().filter_map(|d| match d {
                    D::Region(r) => Some(*r),
                    _ => None,
                })) {
                    if !self.is_generative_param(r) && !r.is_frozen() && !k.contains(&r) {
                        k.push(r);
                    }
                }
                self.knot_in(rep, kept, seen).or_else(|| args.iter().flat_map(|d| self.d_types(d)).find_map(|x| self.knot_in(x, &k, seen)))
            }
            // A module's abstract type constructor applied: its
            // representation, unseen, may keep what it was given anywhere.
            // A `poly`'s variable applied is checked as it is instantiated.
            Ty::App { fun, args } => {
                let abstract_head = matches!(self.arena.get(fun), Ty::Var(v) if self.abstract_funs.contains(v));
                let k = if abstract_head { with(Region::Globals) } else { kept.to_vec() };
                args.iter().flat_map(|d| self.d_types(d)).find_map(|x| self.knot_in(x, &k, seen))
            }
            _ => None,
        }
    }

    /// Whether a latent effect anywhere in `t` writes `r`: what a
    /// `letfreeze`'s value may not do to its region.
    pub(crate) fn writes_in(&self, t: TyId, r: Region) -> bool {
        let mut seen = HashSet::new();
        let mut todo = vec![t];
        // A generative type's representation writing one of its parameters
        // writes whatever it was given: cautiously, any region given any.
        let (mut writes_param, mut given) = (false, false);
        while let Some(t) = todo.pop() {
            let t = self.arena.resolve(t);
            if !seen.insert(t) {
                continue;
            }
            let (effects, kids): (Vec<&Effect>, Vec<TyId>) = match self.arena.get(t) {
                Ty::Subr { effect, params, result, .. } => (vec![effect], params.iter().copied().chain([*result]).collect()),
                Ty::PromptTag { answer, payload, effect, .. } => (vec![effect], vec![*answer, *payload]),
                Ty::Composable { arg, answer, effect, .. } => (vec![effect], vec![*arg, *answer]),
                Ty::Poly { body, .. } => (vec![], vec![*body]),
                Ty::Ref(a, _) | Ty::Array(a, _) | Ty::ICell(a, _) | Ty::MarkKey(a, _) => (vec![], vec![*a]),
                Ty::Pair(a, b, _) => (vec![], vec![*a, *b]),
                Ty::NList { elem, .. } => (vec![], vec![*elem]),
                Ty::Bloblet { fields, .. } => (vec![], fields.clone()),
                Ty::Product(parts) | Ty::Sum(parts) => (vec![], parts.iter().map(|(_, t)| *t).collect()),
                Ty::Named { which, args } => {
                    let mut kids = vec![self.generatives[*which as usize].rep];
                    for d in args {
                        kids.extend(self.d_types(d));
                        given |= self.d_writes(d, r);
                    }
                    (vec![], kids)
                }
                // A description function applied, unseen: it may write
                // whatever it was given.
                Ty::App { args, .. } => {
                    let mut kids = Vec::new();
                    for d in args {
                        kids.extend(self.d_types(d));
                        if self.d_writes(d, r) {
                            given = true;
                            writes_param = true;
                        }
                    }
                    (vec![], kids)
                }
                _ => (vec![], vec![]),
            };
            if effects.iter().any(|e| e.0.contains(&Atom::Write(r))) {
                return true;
            }
            writes_param |= effects.iter().any(|e| {
                e.0.iter().any(|a| matches!(a, Atom::Write(x) if self.is_generative_param(*x)) || matches!(a, Atom::Var(v) if self.generatives.iter().any(|g| g.params.iter().any(|(p, _)| p == v))))
            });
            todo.extend(kids);
        }
        writes_param && given
    }

    // ------------------------------------------------------------- subtyping
    /// Whether descriptions `x` and `y` are the same under `env`: types
    /// each a subtype of the other.
    fn d_same(&mut self, x: &D, y: &D, env: &BinderEnv, st: &mut SubState) -> bool {
        match (x, y) {
            (D::Type(x), D::Type(y)) => self.sub(*x, *y, env, st) && self.sub(*y, *x, &env.flip(), st),
            (D::Region(r), D::Region(s)) => env.region(&env.a, *r) == env.region(&env.b, *s),
            (D::Effect(d), D::Effect(e)) => env.effect(&env.a, d, &self.arena.effect_apps) == env.effect(&env.b, e, &self.arena.effect_apps),
            (D::Size(m), D::Size(n)) => self.size_eq(m, n),
            (D::Conv(Conv::Var(x)), D::Conv(Conv::Var(y))) => env.var(&env.a, *x) == env.var(&env.b, *y),
            (D::Conv(c), D::Conv(d)) => c == d,
            (D::Fun(f), D::Fun(g)) => self.fun_same(*f, *g, env, st),
            _ => false,
        }
    }

    /// Whether description functions `f` and `g` are the same under `env`:
    /// the same variable, or `dlambda`s of the same kinds whose bodies are
    /// the same, their parameters named alike. They are reduced and
    /// eta-contracted as they are made, so nothing else is.
    fn fun_same(&mut self, f: TyId, g: TyId, env: &BinderEnv, st: &mut SubState) -> bool {
        let (f, g) = (self.arena.resolve(f), self.arena.resolve(g));
        if f == g && env.is_empty() {
            return true;
        }
        match (self.arena.get(f).clone(), self.arena.get(g).clone()) {
            (Ty::Var(x), Ty::Var(y)) => env.var(&env.a, x) == env.var(&env.b, y),
            // A dependent procedure's parameter's, or a `select` as written.
            (Ty::ParamSel(k, x), Ty::ParamSel(j, y)) => k == j && x == y,
            (Ty::Select(m, x), Ty::Select(n, y)) => m == n && x == y,
            (Ty::Lam { params: pa, body: ba }, Ty::Lam { params: pb, body: bb }) => {
                if pa.len() != pb.len() || pa.iter().zip(&pb).any(|((_, k), (_, l))| k != l) {
                    return false;
                }
                let mut inner = env.clone();
                for (i, ((va, _), (vb, _))) in pa.iter().zip(&pb).enumerate() {
                    let n = st.labels.len() as u32;
                    let l = *st.labels.entry((f, g, i)).or_insert(DVar(u32::MAX - n));
                    inner.a.insert(*va, l);
                    inner.b.insert(*vb, l);
                }
                self.d_same(&ba, &bb, &inner, st)
            }
            _ => false,
        }
    }

    /// `a ≤ b`. Recursive types are compared coinductively: a pair already
    /// being compared is assumed to hold, which is what makes comparing two
    /// cycles terminate — FX-87's `trail`, Amadio and Cardelli's assumption
    /// set. Every rule is a conjunction, so an assumption left behind by a
    /// comparison that failed is never relied on: the failure is the answer.
    pub fn subtype(&mut self, a: TyId, b: TyId) -> bool {
        let mut st = SubState::default();
        self.sub(a, b, &BinderEnv::default(), &mut st)
    }

    /// `a ≤ b` under `env`, which names each `poly` binder in scope on either
    /// side by the pair of `poly` nodes that bound it, so their bodies are
    /// compared as they are, not substituted: a cycle through a `poly` comes
    /// back to a pair, and an environment, already on the trail.
    fn sub(&mut self, a: TyId, b: TyId, env: &BinderEnv, st: &mut SubState) -> bool {
        if self.lemmas.is_empty() {
            return self.sub_rules(a, b, env, st);
        }
        let (ra, rb) = (self.arena.resolve(a), self.arena.resolve(b));
        if !self.lemma_may_apply(ra, rb) {
            return self.sub_rules(a, b, env, st);
        }
        // The rules first. A comparison that failed may have left
        // assumptions on the trail, so it is put back as it was.
        let saved = st.clone();
        if self.sub_rules(a, b, env, st) {
            return true;
        }
        *st = saved;
        // Then a lemma, whose hypotheses are compared assuming what is
        // being shown, coinductively, as the rules are.
        st.trail.insert((ra, rb, env.clone()));
        for hyps in self.lemma_instances(ra, rb) {
            let saved = st.clone();
            if hyps.iter().all(|(x, y)| self.sub(*x, *y, env, st)) {
                return true;
            }
            *st = saved;
        }
        false
    }

    /// `a ≤ b` by the rules alone: see [`sub`](Self::sub).
    fn sub_rules(&mut self, a: TyId, b: TyId, env: &BinderEnv, st: &mut SubState) -> bool {
        let (a, b) = (self.arena.resolve(a), self.arena.resolve(b));
        if (a == b && env.is_empty()) || !st.trail.insert((a, b, env.clone())) {
            return true;
        }
        let (ta, tb) = (self.arena.get(a).clone(), self.arena.get(b).clone());
        let ra = |r: Region| env.region(&env.a, r);
        let rb = |r: Region| env.region(&env.b, r);
        let apps = self.arena.effect_apps.clone();
        let ea = |e: &Effect| env.effect(&env.a, e, &apps);
        let eb = |e: &Effect| env.effect(&env.b, e, &apps);
        let flip = env.flip();
        // Inside a generative type's own conversions, its name is its
        // representation; everywhere else it is only itself.
        let same_named = matches!((&ta, &tb), (Ty::Named { which: g, .. }, Ty::Named { which: h, .. }) if g == h);
        if !same_named && !matches!(ta, Ty::Void) {
            if let Ty::Named { which, args } = &ta
                && self.transparent.contains(which)
            {
                let a2 = self.unfold(*which, args);
                return self.sub(a2, b, env, st);
            }
            if let Ty::Named { which, args } = &tb
                && self.transparent.contains(which)
            {
                let b2 = self.unfold(*which, args);
                return self.sub(a, b2, env, st);
            }
        }
        // A composable continuation can be called, so it can stand where a
        // subroutine is wanted.
        if let (Ty::Composable { .. }, Ty::Subr { .. }) = (&ta, &tb) {
            let (xa, pa, qa) = ta.as_subr().expect("callable");
            let (xb, pb, qb) = tb.as_subr().expect("callable");
            return pa.len() == pb.len()
                && ea(&xa).within(&eb(&xb))
                && pa.iter().zip(&pb).all(|(x, y)| self.sub(*y, *x, &flip, st))
                && self.sub(qa, qb, env, st);
        }
        match (ta, tb) {
            // `void` is the bottom type: nothing is ever returned as one.
            (Ty::Void, _) => true,
            (Ty::Base(x), Ty::Base(y)) => x == y,
            // A natural is an integer; one of a known size, a natural.
            (Ty::Nat(_), Ty::Base(_)) => b == self.int,
            (Ty::Nat(m), Ty::Nat(n)) => self.size_le(&m, &n),
            (Ty::Var(x), Ty::Var(y)) => env.var(&env.a, x) == env.var(&env.b, y),
            (
                Ty::Subr { conv: ca, effect: xa, params: pa, result: qa },
                Ty::Subr { conv: cb, effect: xb, params: pb, result: qb },
            ) => {
                // Conventions: the same, or any of FX-26's own as `fx`;
                // variables by the binders they stand for.
                let conv_ok = match (ca, cb) {
                    (Conv::Var(x), Conv::Var(y)) => env.var(&env.a, x) == env.var(&env.b, y),
                    _ => ca.fits(cb),
                };
                conv_ok
                    && pa.len() == pb.len()
                    && ea(&xa).within(&eb(&xb))
                    && pa.iter().zip(&pb).all(|(x, y)| self.sub(*y, *x, &flip, st))
                    && self.sub(qa, qb, env, st)
            }
            // References and pairs are mutable, so their contents are
            // invariant: FX-87's `ref` rule, and its pairs.
            (Ty::Place(r), Ty::Place(s)) => ra(r) == rb(s),
            (Ty::Ref(x, r), Ty::Ref(y, s)) | (Ty::Array(x, r), Ty::Array(y, s)) | (Ty::ICell(x, r), Ty::ICell(y, s)) => {
                ra(r) == rb(s) && self.sub(x, y, env, st) && self.sub(y, x, &flip, st)
            }
            // Frozen pairs cannot be written, so, as a frozen bloblet's
            // fields, their contents are covariant.
            (Ty::Pair(x1, x2, r), Ty::Pair(y1, y2, s)) if r.is_frozen() && Region::frozen_le(ra(r), rb(s)) => {
                self.sub(x1, y1, env, st) && self.sub(x2, y2, env, st)
            }
            (Ty::Pair(x1, x2, r), Ty::Pair(y1, y2, s)) => {
                ra(r) == rb(s)
                    && self.sub(x1, y1, env, st)
                    && self.sub(y1, x1, &flip, st)
                    && self.sub(x2, y2, env, st)
                    && self.sub(y2, x2, &flip, st)
            }
            // A tag both delivers and receives values of its types, so it is
            // invariant in all of them, as a reference is in its contents.
            (
                Ty::PromptTag { answer: a1, payload: h1, effect: d1, region: r1 },
                Ty::PromptTag { answer: a2, payload: h2, effect: d2, region: r2 },
            ) => {
                ra(r1) == rb(r2)
                    && ea(&d1) == eb(&d2)
                    && self.sub(a1, a2, env, st)
                    && self.sub(a2, a1, &flip, st)
                    && self.sub(h1, h2, env, st)
                    && self.sub(h2, h1, &flip, st)
            }
            // Called like a subroutine: contravariant in what it takes,
            // covariant in what it gives and does.
            (
                Ty::Composable { arg: t1, answer: a1, effect: d1, region: r1 },
                Ty::Composable { arg: t2, answer: a2, effect: d2, region: r2 },
            ) => ra(r1) == rb(r2) && ea(&d1).within(&eb(&d2)) && self.sub(t2, t1, &flip, st) && self.sub(a1, a2, env, st),
            (Ty::MarkKey(x, r), Ty::MarkKey(y, s)) => ra(r) == rb(s) && self.sub(x, y, env, st) && self.sub(y, x, &flip, st),
            // A bloblet's fields are invariant, as a reference's contents
            // are, unless they are frozen, when nothing can store into them.
            // Freezing is a change of type, never a subtype: a bloblet seen
            // as frozen through one name could still be written through
            // another.
            (
                Ty::Bloblet { fields: fa, frozen: za, region: r },
                Ty::Bloblet { fields: fb, frozen: zb, region: s },
            ) => {
                (ra(r) == rb(s) || (za && Region::frozen_le(ra(r), rb(s))))
                    && za == zb
                    && fa.len() == fb.len()
                    && fa.iter().zip(&fb).all(|(x, y)| self.sub(*x, *y, env, st) && (za || self.sub(*y, *x, &flip, st)))
            }
            // Immutable, so covariant: a product in its fields, a sum in its
            // variants, and a sum with fewer tags fits one with more.
            (Ty::Product(pa), Ty::Product(pb)) => {
                pa.len() == pb.len() && pa.iter().zip(&pb).all(|((la, x), (lb, y))| la == lb && self.sub(*x, *y, env, st))
            }
            (Ty::Sum(sa), Ty::Sum(sb)) => sa.iter().all(|(la, x)| {
                sb.iter().find(|(lb, _)| lb == la).is_some_and(|(_, y)| self.sub(*x, *y, env, st))
            }),
            // A `nlist` is frozen, so covariant in its elements; its size must
            // be the same, or forgotten as `finite`.
            (Ty::NList { elem: x, size: m, region: r }, Ty::NList { elem: y, size: n, region: s }) => {
                Region::frozen_le(ra(r), rb(s)) && self.size_le(&m, &n) && self.sub(x, y, env, st)
            }
            // Any `nlist` is a finite list; a finite list is a `nlist` of some
            // length.
            (Ty::NList { elem: x, size, region: r }, Ty::Pair(y, tail, s)) => {
                // Of no elements, it has no tail to compare.
                // A `nlist` of some length has for its tail the same type.
                let rest = match size {
                    Size::Finite => Some(a),
                    _ if size.as_lit() == Some(0) => None,
                    _ => Some(self.arena.ty(Ty::NList { elem: x, size: self.tail_size(&size), region: r })),
                };
                Region::frozen_le(ra(r), rb(s)) && self.sub(x, y, env, st) && rest.is_none_or(|rest| self.sub(rest, tail, env, st))
            }
            (Ty::Pair(x, tail, r), Ty::NList { elem: y, size: Size::Finite, region: s }) if matches!(r, Region::Frozen(_, true)) => {
                Region::frozen_le(ra(r), rb(s)) && self.sub(x, y, env, st) && self.sub(tail, b, env, st)
            }
            // A generative type is related only to itself, argument by
            // argument, as its variance says.
            (Ty::Named { which: g, args: xa }, Ty::Named { which: h, args: xb }) if g == h => {
                let variance = self.generatives[g as usize].variance.clone();
                xa.iter().zip(&xb).zip(variance).all(|((x, y), v)| match (x, y) {
                    (D::Type(x), D::Type(y)) => match v {
                        Variance::Co => self.sub(*x, *y, env, st),
                        Variance::Contra => self.sub(*y, *x, &flip, st),
                        Variance::Inv => self.sub(*x, *y, env, st) && self.sub(*y, *x, &flip, st),
                    },
                    (D::Region(r), D::Region(s)) => ra(*r) == rb(*s),
                    (D::Size(m), D::Size(n)) => self.size_eq(m, n),
                    (D::Conv(Conv::Var(x)), D::Conv(Conv::Var(y))) => env.var(&env.a, *x) == env.var(&env.b, *y),
                    (D::Conv(c), D::Conv(d)) => c == d,
                    (D::Effect(d), D::Effect(e)) => match v {
                        Variance::Co => ea(d).within(&eb(e)),
                        Variance::Contra => eb(e).within(&ea(d)),
                        Variance::Inv => ea(d) == eb(e),
                    },
                    (D::Fun(f), D::Fun(g)) => self.fun_same(*f, *g, env, st),
                    _ => false,
                })
            }
            // A description function applied: the same function, given
            // the same descriptions (FX-91's congruence).
            (Ty::App { fun: f, args: xa }, Ty::App { fun: g, args: xb }) => {
                xa.len() == xb.len() && self.fun_same(f, g, env, st) && xa.iter().zip(&xb).all(|(x, y)| self.d_same(x, y, env, st))
            }
            // Modules: their values the same, in order, since a module is
            // a product of them; their types fewer, an abstract one met by
            // a transparent one (`first-class-modules.md`, M4).
            (Ty::Module { abs: aa, descs: da, vals: va }, Ty::Module { abs: ab, descs: db, vals: vb }) => {
                self.module_sub((a, b), (&aa, &da, &va), (&ab, &db, &vb), env, st)
            }
            (Ty::ParamSel(k, x), Ty::ParamSel(j, y)) => k == j && x == y,
            // Two description functions (a module's transparent ones).
            (Ty::Lam { .. }, Ty::Lam { .. }) => self.fun_same(a, b, env, st),
            (Ty::Poly { binders: ba, body: xa }, Ty::Poly { binders: bb, body: xb }) => {
                if ba.len() != bb.len() || ba.iter().zip(&bb).any(|((_, k1), (_, k2))| k1 != k2) {
                    return false;
                }
                // Each pair of binders is named by the pair of nodes and its
                // position: entering the same pair again rebinds the same
                // name, as re-entering a scope shadows it, so the
                // environments stay finitely many.
                let mut inner = env.clone();
                for (i, ((va, _), (vb, _))) in ba.iter().zip(&bb).enumerate() {
                    let n = st.labels.len() as u32;
                    let l = *st.labels.entry((a, b, i)).or_insert(DVar(u32::MAX - n));
                    inner.a.insert(*va, l);
                    inner.b.insert(*vb, l);
                }
                // Bounded region binders must have the same bounds.
                let bounds = ba.iter().zip(&bb).all(|((va, _), (vb, _))| {
                    match (self.arena.bound(*va), self.arena.bound(*vb)) {
                        (None, None) => true,
                        (Some(x), Some(y)) => inner.region(&inner.a, x) == inner.region(&inner.b, y),
                        _ => false,
                    }
                });
                bounds && self.sub(xa, xb, &inner, st)
            }
            _ => false,
        }
    }

    /// Module type `a` ≤ `b`: each abstract type of `b`'s an abstract type
    /// of `a`'s (paired as a `poly`'s binders are) or a transparent one
    /// (`b`'s abstract type is then what `a` says it is); each description
    /// of `b`'s one of `a`'s, the same; and their values the same names, in
    /// order, each `a`'s a subtype of `b`'s, since a module is a product of
    /// its values. Fewer values, or another order, `expect` makes by
    /// reshaping (`Checker::reshape`).
    fn module_sub(&mut self, (a, b): (TyId, TyId), (aa, da, va): ModuleView, (ab, db, vb): ModuleView, env: &BinderEnv, st: &mut SubState) -> bool {
        if aa.iter().any(|(n, _)| db.iter().any(|(m, _)| m == n)) || va.len() != vb.len() || va.iter().zip(vb).any(|((n, _), (m, _))| n != m) {
            return false;
        }
        let mut inner = env.clone();
        for (i, (n, y)) in ab.iter().enumerate() {
            match aa.iter().find(|(m, _)| m == n) {
                Some((_, x)) if self.arena.dvar_kind_known(*x) != self.arena.dvar_kind_known(*y) => return false,
                Some((_, x)) => {
                    let k = st.labels.len() as u32;
                    let l = *st.labels.entry((a, b, i)).or_insert(DVar(u32::MAX - k));
                    inner.a.insert(*x, l);
                    inner.b.insert(*y, l);
                }
                None if da.iter().any(|(m, _)| m == n) => {}
                None => return false,
            }
        }
        let (bd, bv) = match st.modules.get(&(a, b)) {
            Some(parts) => parts.clone(),
            None => {
                // `b`'s abstract types that `a` defines: those definitions,
                // `a`'s own abstract types in them named as paired.
                let to_label: HashMap<DVar, D> = inner
                    .a
                    .iter()
                    .map(|(x, l)| {
                        let t = self.arena.ty(Ty::Var(*l));
                        (*x, if matches!(self.arena.dvar_kind_known(*x), Some(Kind::Arrow(_))) { D::Fun(t) } else { D::Type(t) })
                    })
                    .collect();
                let mut by: HashMap<DVar, D> = HashMap::new();
                for (n, y) in ab {
                    if !aa.iter().any(|(m, _)| m == n)
                        && let Some((_, d)) = da.iter().find(|(m, _)| m == n)
                    {
                        let d = self.subst(*d, &to_label);
                        let d = if matches!(self.arena.dvar_kind_known(*y), Some(Kind::Arrow(_))) { D::Fun(d) } else { D::Type(d) };
                        by.insert(*y, d);
                    }
                }
                let parts: ModuleParts = (
                    db.iter().map(|(n, t)| (*n, self.subst(*t, &by))).collect(),
                    vb.iter().map(|(n, t)| (*n, self.subst(*t, &by))).collect(),
                );
                st.modules.insert((a, b), parts.clone());
                parts
            }
        };
        let flip = inner.flip();
        bd.iter().all(|(n, y)| da.iter().find(|(m, _)| m == n).is_some_and(|(_, x)| self.sub(*x, *y, &inner, st) && self.sub(*y, *x, &flip, st)))
            && va.iter().zip(&bv).all(|((_, x), (_, y))| self.sub(*x, *y, &inner, st))
    }

    // ---------------------------------------------------------- substitution
    /// `t` with each binder in `map` replaced — what `proj` does. Recursive
    /// types are copied as cycles: each node is given its slot before its
    /// children are built.
    pub fn subst(&mut self, t: TyId, map: &HashMap<DVar, D>) -> TyId {
        self.subst_memo(t, map, &mut HashMap::new())
    }

    /// A description substituted into, sharing `memo` with the type it is
    /// part of.
    pub(crate) fn subst_d_memo(&mut self, d: &D, map: &HashMap<DVar, D>, memo: &mut HashMap<TyId, TyId>) -> D {
        match d {
            D::Type(t) => D::Type(self.subst_memo(*t, map, memo)),
            D::Fun(f) => D::Fun(self.subst_memo(*f, map, memo)),
            D::Region(r) => D::Region(subst_region(*r, map)),
            D::Effect(e) => D::Effect(subst_effect(e, map, &self.arena)),
            D::Size(z) => D::Size(crate::sizes::subst_size(z, map)),
            D::Conv(c) => D::Conv(match c {
                Conv::Var(v) => match map.get(v) {
                    Some(D::Conv(by)) => *by,
                    _ => *c,
                },
                c => *c,
            }),
        }
    }

    fn subst_memo(&mut self, t: TyId, map: &HashMap<DVar, D>, memo: &mut HashMap<TyId, TyId>) -> TyId {
        let t = self.arena.resolve(t);
        if let Some(&n) = memo.get(&t) {
            return n;
        }
        let ty = self.arena.get(t).clone();
        match ty {
            Ty::Base(_) | Ty::Void | Ty::Link(None) => return t,
            Ty::Select(m, n) => return self.select_map.get(&(m, n)).copied().unwrap_or(t),
            Ty::ParamSel(k, n) => return self.param_map.get(&(k, n)).copied().unwrap_or(t),
            Ty::Var(v) => {
                return match map.get(&v) {
                    Some(D::Type(x) | D::Fun(x)) => *x,
                    _ => t,
                };
            }
            _ => {}
        }
        let slot = self.arena.ty(Ty::Link(None));
        // A function applied, given what it is substituted by: reduced, if
        // it is a `dlambda` now.
        if let Ty::App { fun, args } = &ty {
            memo.insert(t, slot);
            let f = self.subst_memo(*fun, map, memo);
            let args: Vec<D> = args.iter().map(|d| self.subst_d_memo(d, map, memo)).collect();
            let to = match self.apply_fun(f, args) {
                D::Type(x) => x,
                // A function to another kind, in a type: left as it was.
                _ => t,
            };
            self.arena.set_link(slot, to);
            return slot;
        }
        memo.insert(t, slot);
        let region = |r: Region| subst_region(r, map);
        let new = match ty {
            Ty::Subr { conv, effect, params, result } => {
                let conv = match conv {
                    Conv::Var(v) => match map.get(&v) {
                        Some(D::Conv(c)) => *c,
                        _ => conv,
                    },
                    c => c,
                };
                let effect = subst_effect(&effect, map, &self.arena);
                let params = params.iter().map(|p| self.subst_memo(*p, map, memo)).collect();
                let result = self.subst_memo(result, map, memo);
                Ty::Subr { conv, effect, params, result }
            }
            Ty::Poly { binders, body } => Ty::Poly { binders, body: self.subst_memo(body, map, memo) },
            Ty::Ref(a, r) => Ty::Ref(self.subst_memo(a, map, memo), region(r)),
            Ty::Array(a, r) => Ty::Array(self.subst_memo(a, map, memo), region(r)),
            Ty::ICell(a, r) => Ty::ICell(self.subst_memo(a, map, memo), region(r)),
            Ty::Place(r) => Ty::Place(region(r)),
            Ty::Pair(a, b, r) => Ty::Pair(self.subst_memo(a, map, memo), self.subst_memo(b, map, memo), region(r)),
            Ty::PromptTag { answer, payload, effect, region: r } => Ty::PromptTag {
                answer: self.subst_memo(answer, map, memo),
                payload: self.subst_memo(payload, map, memo),
                effect: subst_effect(&effect, map, &self.arena),
                region: region(r),
            },
            Ty::Composable { arg, answer, effect, region: r } => Ty::Composable {
                arg: self.subst_memo(arg, map, memo),
                answer: self.subst_memo(answer, map, memo),
                effect: subst_effect(&effect, map, &self.arena),
                region: region(r),
            },
            Ty::MarkKey(t, r) => Ty::MarkKey(self.subst_memo(t, map, memo), region(r)),
            Ty::Product(parts) => Ty::Product(parts.iter().map(|(l, t)| (*l, self.subst_memo(*t, map, memo))).collect()),
            Ty::Sum(parts) => Ty::Sum(parts.iter().map(|(l, t)| (*l, self.subst_memo(*t, map, memo))).collect()),
            Ty::Module { abs, descs, vals } => Ty::Module {
                abs,
                descs: descs.iter().map(|(l, t)| (*l, self.subst_memo(*t, map, memo))).collect(),
                vals: vals.iter().map(|(l, t)| (*l, self.subst_memo(*t, map, memo))).collect(),
            },
            Ty::Bloblet { fields, frozen, region: r } => Ty::Bloblet {
                fields: fields.iter().map(|f| self.subst_memo(*f, map, memo)).collect(),
                frozen,
                region: region(r),
            },
            Ty::NList { elem, size, region: r } => {
                Ty::NList { elem: self.subst_memo(elem, map, memo), size: crate::sizes::subst_size(&size, map), region: region(r) }
            }
            Ty::Nat(size) => Ty::Nat(crate::sizes::subst_size(&size, map)),
            Ty::Named { which, args } => Ty::Named { which, args: args.iter().map(|d| self.subst_d_memo(d, map, memo)).collect() },
            Ty::Lam { params, body } => Ty::Lam { params, body: self.subst_d_memo(&body, map, memo) },
            other => other,
        };
        let id = self.arena.ty(new);
        self.arena.set_link(slot, id);
        slot
    }
}

/// `r` with `map`'s regions for its variables: frozen data's place too.
pub(crate) fn subst_region(r: Region, map: &HashMap<DVar, D>) -> Region {
    match r {
        Region::Var(v) => match map.get(&v) {
            Some(D::Region(x)) => *x,
            _ => r,
        },
        Region::Frozen(Some(p), f) => match map.get(&p) {
            Some(D::Region(Region::Var(q))) => Region::Frozen(Some(*q), f),
            Some(D::Region(Region::Heap)) => Region::Frozen(None, f),
            _ => r,
        },
        c => c,
    }
}

/// What an effect function is given, substituted into.
fn subst_earg(a: &EArg, map: &HashMap<DVar, D>, arena: &crate::ast::Arena) -> EArg {
    match a {
        EArg::Region(r) => EArg::Region(subst_region(*r, map)),
        EArg::Effect(e) => EArg::Effect(subst_effect(e, map, arena)),
        EArg::Size(z) => EArg::Size(crate::sizes::subst_size(z, map)),
        EArg::Conv(c) => EArg::Conv(match c {
            Conv::Var(v) => match map.get(v) {
                Some(D::Conv(by)) => *by,
                _ => *c,
            },
            c => *c,
        }),
    }
}

/// What an effect function is given, as a description.
pub(crate) fn earg_d(a: EArg) -> D {
    match a {
        EArg::Region(r) => D::Region(r),
        EArg::Effect(e) => D::Effect(e),
        EArg::Size(z) => D::Size(z),
        EArg::Conv(c) => D::Conv(c),
    }
}

/// An effect substituted into. A read, allocation or await at data frozen
/// into the heap is pure (`Checker::frozen`), and so is dropped: a region
/// variable instantiated at `acyclic` or `const` leaves none behind.
pub(crate) fn subst_effect(e: &Effect, map: &HashMap<DVar, D>, arena: &crate::ast::Arena) -> Effect {
    let mut out = Effect::pure();
    for a in &e.0 {
        let sub_r = |r: Region| subst_region(r, map);
        if let Atom::Read(r) | Atom::Alloc(r) | Atom::Await(r) = *a
            && matches!(sub_r(r), Region::Frozen(None, _))
        {
            continue;
        }
        let piece = match *a {
            Atom::Var(v) => match map.get(&v) {
                Some(D::Effect(x)) => x.clone(),
                _ => Effect::atom(*a),
            },
            Atom::Read(r) => Effect::atom(Atom::Read(sub_r(r))),
            Atom::Write(r) => Effect::atom(Atom::Write(sub_r(r))),
            Atom::Alloc(r) => Effect::atom(Atom::Alloc(sub_r(r))),
            Atom::Goto(r) => Effect::atom(Atom::Goto(sub_r(r))),
            Atom::Comefrom(r) => Effect::atom(Atom::Comefrom(sub_r(r))),
            Atom::Await(r) => Effect::atom(Atom::Await(sub_r(r))),
            Atom::Spin => Effect::atom(Atom::Spin),
            // An effect function applied: given what it is substituted by,
            // reduced if that is a `dlambda`.
            Atom::App(n) => {
                let (head, args) = arena.effect_apps.parts(n);
                let args: Vec<EArg> = args.iter().map(|x| subst_earg(x, map, arena)).collect();
                match map.get(&head) {
                    Some(D::Fun(f)) => match arena.get(*f) {
                        Ty::Var(w) => Effect::atom(arena.effect_apps.atom(*w, args)),
                        Ty::Lam { params, body: D::Effect(body) } if params.len() == args.len() => {
                            let given: HashMap<DVar, D> = params.iter().map(|(v, _)| *v).zip(args.into_iter().map(earg_d)).collect();
                            subst_effect(body, &given, arena)
                        }
                        _ => Effect::atom(*a),
                    },
                    _ => Effect::atom(arena.effect_apps.atom(head, args)),
                }
            }
        };
        out = out.union(&piece);
    }
    out
}

// ---------------------------------------------------------------- prompts
impl Checker {
    /// `(prompt tag body handler)`.
    ///
    /// The tag's type fixes what crosses the prompt: the body must produce
    /// the answer type `A`, the handler must take the payload `H` to an `A`,
    /// and the body's effect must be within the tag's bound `D` apart from
    /// control on the tag's region `R` — the bound is what a continuation
    /// captured up to this prompt is said to do when it is called.
    ///
    /// Then the prompt delimits: `(goto R)` and `(comefrom R)` are removed
    /// from the body's effect, but only if the body can reach no tag in `R`
    /// other than this one. A region can hold many tags, and an abort to
    /// another of them passes straight through this prompt. So the condition
    /// is on the body's free variables: none may have a type mentioning `R`,
    /// except the tag itself when `tag` is a variable. A tag the body makes
    /// for itself is fine: an abort to it with no prompt of its own inside
    /// the body is an error, not a jump past this one.
    // ------------------------------------------------------------- tagcase
    /// `tagcase`. `expected`, when checking, is what every arm is checked
    /// against; otherwise the result is the arms' types' least upper bound
    /// among themselves.
    pub(crate) fn synth_tagcase(
        &mut self,
        e: ExpId,
        scrutinee: ExpId,
        arms: &[Arm],
        els: &Option<(Sym, ExpId)>,
        expected: Option<TyId>,
    ) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let (st, mut eff) = self.synth(scrutinee)?;
        let Ty::Sum(variants) = self.arena.get(st).clone() else {
            return Err(FxError::at(self.arena.span_of(scrutinee), format!("a sum is expected here, and this is a {}", self.show_ty(st))));
        };
        let mut types = Vec::new();
        for arm in arms {
            let Some((_, t)) = variants.iter().find(|(l, _)| *l == arm.tag) else {
                return Err(FxError::at(self.arena.span_of(arm.body), format!("a {} has no tag `{}`", self.show_ty(st), self.interner.name(arm.tag))));
            };
            let bound: Vec<(Sym, TyId)> = match &arm.bind {
                ArmBind::Value(x) => vec![(*x, *t)],
                ArmBind::Fields(xs) => match self.arena.get(*t).clone() {
                    Ty::Product(fs) if fs.len() == xs.len() => xs.iter().zip(&fs).map(|(x, (_, t))| (*x, *t)).collect(),
                    _ => {
                        return Err(FxError::at(self.arena.span_of(arm.body), format!("`{}` carries a {}, which cannot be taken apart into {} name(s)", self.interner.name(arm.tag), self.show_ty(*t), xs.len())));
                    }
                },
            };
            let (t, be) = self.in_scope(&bound, |c| match expected {
                Some(x) => Ok((x, c.check(arm.body, x)?)),
                None => c.synth(arm.body),
            })?;
            eff = eff.union(&be);
            types.push(t);
        }
        let rest: Vec<(Sym, TyId)> = variants.iter().filter(|(l, _)| !arms.iter().any(|a| a.tag == *l)).cloned().collect();
        match els {
            Some((y, body)) => {
                let rest_ty = self.arena.ty(Ty::Sum(rest));
                let (t, be) = self.in_scope(&[(*y, rest_ty)], |c| match expected {
                    Some(x) => Ok((x, c.check(*body, x)?)),
                    None => c.synth(*body),
                })?;
                eff = eff.union(&be);
                types.push(t);
            }
            None if !rest.is_empty() => {
                let names: Vec<&str> = rest.iter().map(|(l, _)| self.interner.name(*l)).collect();
                return Err(FxError::at(span, format!("this `tagcase` has no arm for {}", names.join(", "))));
            }
            None => {}
        }
        let t = match expected {
            Some(x) => x,
            None => {
                let Some(t) = types.iter().copied().find(|t| types.clone().iter().all(|u| self.subtype(*u, *t))) else {
                    let shown: Vec<String> = types.iter().map(|t| self.show_ty(*t)).collect();
                    return Err(FxError::at(span, format!("the arms are {}", shown.join(", "))));
                };
                t
            }
        };
        let eff = self.mask(e, &eff, t);
        Ok((t, eff))
    }

    /// `env` cut back to `n` bindings, and the known procedures among those
    /// cut forgotten.
    pub(crate) fn truncate_env(&mut self, n: usize) {
        self.env.truncate(n);
        self.known.retain(|(_, i)| *i < n);
        self.global_slots.retain(|i| *i < n);
    }

    /// Run `f` with `bound` in scope.
    pub(crate) fn in_scope<T>(&mut self, bound: &[(Sym, TyId)], f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let depth = self.env.len();
        self.env.extend_from_slice(bound);
        let r = f(self);
        self.truncate_env(depth);
        r
    }

    // --------------------------------------------------------------- bloblets
    /// The bloblet forms. `expected`, when checking, supplies a new
    /// bloblet's region and field types.
    pub(crate) fn synth_bloblet(
        &mut self,
        e: ExpId,
        op: BlobletOp,
        args: &[ExpId],
        expected: Option<TyId>,
    ) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let int = self.int;
        if matches!(op, BlobletOp::Make | BlobletOp::RMake) {
            // `rmake-bloblet`'s region is its first operand's; `make-bloblet`'s
            // the type it is checked against, or a fresh one.
            let (given, mut eff, args) = if op == BlobletOp::RMake {
                let (r, rest) = args.split_first().expect("parsed");
                let (rt, re) = self.synth(*r)?;
                let Ty::Place(g) = self.arena.get(rt).clone() else {
                    return Err(FxError::at(span, format!("a region is expected here, and this is a {}", self.show_ty(rt))));
                };
                (Some(g), re, rest)
            } else {
                (None, Effect::pure(), args)
            };
            let (bytes, fields) = args.split_first().expect("parsed");
            eff = eff.union(&self.check(*bytes, int)?);
            let want = expected.and_then(|t| match self.arena.get(t).clone() {
                Ty::Bloblet { fields: fs, frozen: false, region }
                    if fs.len() == fields.len() && given.is_none_or(|g| g == region) =>
                {
                    Some((fs, region))
                }
                _ => None,
            });
            let (tys, region) = match want {
                Some((fs, region)) => {
                    for (f, t) in fields.iter().zip(&fs) {
                        eff = eff.union(&self.check(*f, *t)?);
                    }
                    (fs, region)
                }
                None => {
                    let mut tys = Vec::new();
                    for f in fields {
                        let (t, fe) = self.synth(*f)?;
                        eff = eff.union(&fe);
                        tys.push(t);
                    }
                    (tys, given.unwrap_or_else(|| self.fresh_region_named("bloblet")))
                }
            };
            eff.0.insert(Atom::Alloc(region));
            let t = self.arena.ty(Ty::Bloblet { fields: tys, frozen: false, region });
            self.no_knot(t, span)?;
            let eff = self.mask(e, &eff, t);
            return Ok((t, eff));
        }
        let (b, rest) = args.split_first().expect("parsed");
        let (bt, mut eff) = self.synth(*b)?;
        let Ty::Bloblet { fields, frozen, region } = self.arena.get(bt).clone() else {
            return Err(FxError::at(self.arena.span_of(*b), format!("a bloblet is expected here, and this is a {}", self.show_ty(bt))));
        };
        let field = |c: &Self, i: usize| -> R<TyId> {
            fields.get(i).copied().ok_or_else(|| {
                FxError::at(span, format!("a {} has no field {i}: its fields are 0 to {}", c.show_ty(bt), fields.len() as i64 - 1))
            })
        };
        let t = match op {
            BlobletOp::Make | BlobletOp::RMake => unreachable!(),
            BlobletOp::Ref(i) => {
                let t = field(self, i)?;
                if !frozen {
                    eff.0.insert(Atom::Read(region));
                }
                t
            }
            BlobletOp::Set(i) => {
                let t = field(self, i)?;
                if frozen {
                    return Err(FxError::at(span, format!("a {} cannot be changed: its fields are frozen", self.show_ty(bt))));
                }
                eff = eff.union(&self.check(rest[0], t)?);
                eff.0.insert(Atom::Write(region));
                self.unit
            }
            BlobletOp::Freeze => {
                eff.0.insert(Atom::Write(region));
                self.arena.ty(Ty::Bloblet { fields: fields.clone(), frozen: true, region })
            }
            BlobletOp::Byte => {
                eff = eff.union(&self.check(rest[0], int)?);
                eff.0.insert(Atom::Read(region));
                int
            }
            BlobletOp::SetByte => {
                eff = eff.union(&self.check(rest[0], int)?);
                eff = eff.union(&self.check(rest[1], int)?);
                eff.0.insert(Atom::Write(region));
                self.unit
            }
            // The suffix's length never changes.
            BlobletOp::Bytes => int,
        };
        let eff = self.mask(e, &eff, t);
        Ok((t, eff))
    }

    fn synth_prompt(&mut self, e: ExpId, tag: ExpId, body: ExpId, handler: ExpId) -> R<(TyId, Effect)> {
        let (tt, te) = self.synth(tag)?;
        let Ty::PromptTag { answer, payload, effect: bound, region } = self.arena.get(tt).clone() else {
            return Err(FxError::at(
                self.arena.span_of(tag),
                format!("a prompt needs a prompt tag, not a {}", self.show_ty(tt)),
            ));
        };
        // Checked against the answer type, so that what the body needs to
        // know — an operator's binders, a `nil` — it is told.
        let be = self.check(body, answer).map_err(|err| match expected_and_found(&err.message) {
            Some((want, got, delta)) if err.span == self.arena.span_of(body) => {
                FxError::at(err.span, format!("the tag's prompts deliver a {want}, and this body is a {got}{delta}"))
            }
            _ => err,
        })?;
        let own = Effect([Atom::Goto(region), Atom::Comefrom(region)].into_iter().collect());
        let beyond = Effect(be.0.iter().copied().filter(|a| !Effect::atom(*a).within(&bound) && !own.contains(*a)).collect());
        if !beyond.is_pure() {
            return Err(FxError::at(
                self.arena.span_of(body),
                format!(
                    "the tag allows its delimited computations {}, and this body also has {}",
                    self.show_effect(&bound),
                    self.show_effect(&beyond)
                ),
            ));
        }
        // A handler written as a `lambda` is told what it takes and gives.
        let (ht, he) = if matches!(self.arena.exp_at(handler), Exp::Lambda { params, .. } if params.len() == 1) {
            let Exp::Lambda { body: hbody, .. } = self.arena.exp_at(handler).clone() else { unreachable!() };
            self.synth_lambda_as(handler, Some(&[payload]), Some(answer)).map_err(|err| match expected_and_found(&err.message) {
                Some((_, got, delta)) if err.span == self.arena.span_of(hbody) => FxError::at(
                    err.span,
                    format!("the handler must take a {} to a {}, and this gives a {got}{delta}", self.show_ty(payload), self.show_ty(answer)),
                ),
                _ => err,
            })?
        } else {
            self.synth(handler)?
        };
        let Some((latent, params, result)) = self.arena.get(ht).as_subr() else {
            return Err(FxError::at(self.arena.span_of(handler), format!("a handler is a subroutine, not a {}", self.show_ty(ht))));
        };
        if params.len() != 1 || !self.subtype(payload, params[0]) || !self.subtype(result, answer) {
            return Err(FxError::at(
                self.arena.span_of(handler),
                format!("the handler must take a {} to a {}; it is a {}", self.show_ty(payload), self.show_ty(answer), self.show_ty(ht)),
            ));
        }
        let delimited = if self.reaches_only(body, tag, region) {
            Effect(be.0.iter().copied().filter(|a| !own.contains(*a)).collect())
        } else {
            be
        };
        let eff = te.union(&he).union(&latent).union(&delimited);
        Ok((answer, self.mask(e, &eff, answer)))
    }

    /// Whether the only way `body` can name anything in region `r` is the
    /// variable `tag` (if `tag` is one).
    fn reaches_only(&self, body: ExpId, tag: ExpId, r: Region) -> bool {
        let tag_var = match self.arena.exp_at(tag) {
            Exp::Var(s) => Some(*s),
            _ => None,
        };
        self.free_vars(body).into_iter().filter(|v| Some(*v) != tag_var).all(|v| {
            let Some(t) = self.lookup(v) else { return true };
            let mut rs = HashSet::new();
            self.regions_in(t, &mut rs);
            !rs.contains(&r)
        })
    }
}

/// What a recursive binding that is not a lambda is told.
pub fn letrec_not_lambda(name: &str) -> String {
    format!("`{name}` is bound recursively, so it must be a lambda: nothing may run before every binding exists")
}

/// A message "a W is expected here, and this is a G", its second line (an
/// effect's delta, [`Checker::effect_delta`]) apart: W, G, and that line
/// with its newline, or "".
pub(crate) fn expected_and_found(message: &str) -> Option<(&str, &str, &str)> {
    let (first, delta) = match message.find('\n') {
        Some(i) => (&message[..i], &message[i..]),
        None => (message, ""),
    };
    let (want, got) = first.strip_prefix("a ")?.split_once(" is expected here, and this is a ")?;
    Some((want, got, delta))
}

/// What a `letrena` or `letreap` whose value would outlive its region is
/// told.
pub fn region_escapes(form: &str, r: &str, t: &str) -> String {
    format!("the value of `{form} {r}` would outlive its region: its type is {t}")
}

/// What one whose body may capture a continuation is told.
pub fn region_captured(form: &str, r: &str, eff: &str) -> String {
    format!("a continuation captured in `{form} {r}` could outlive its region: its effect is {eff}")
}

/// What one subtype question remembers: the pairs assumed (FX-87's trail),
/// each with the binder environment it was asked under, and the names given
/// to pairs of `poly` binders.
#[derive(Clone, Default)]
struct SubState {
    trail: HashSet<(TyId, TyId, BinderEnv)>,
    labels: HashMap<(TyId, TyId, usize), DVar>,
    /// For a pair of module types met before, the wanted one's
    /// descriptions and values with its abstract types the given one's
    /// transparent ones: made once, so that a recursive type meets the same
    /// pair again, which the trail catches.
    modules: HashMap<(TyId, TyId), ModuleParts>,
}

type ModuleParts = (Vec<(Sym, TyId)>, Vec<(Sym, TyId)>);
type ModuleView<'a> = (&'a [(Sym, DVar)], &'a [(Sym, TyId)], &'a [(Sym, TyId)]);

/// For each side of a subtype question, the `poly` binders in scope, each
/// mapped to the name its pair of binders was given.
#[derive(Clone, Default, PartialEq, Eq, Hash)]
struct BinderEnv {
    a: std::collections::BTreeMap<DVar, DVar>,
    b: std::collections::BTreeMap<DVar, DVar>,
}

impl BinderEnv {
    fn is_empty(&self) -> bool {
        self.a.is_empty() && self.b.is_empty()
    }
    /// The same environment, for the question asked the other way round.
    fn flip(&self) -> BinderEnv {
        BinderEnv { a: self.b.clone(), b: self.a.clone() }
    }
    fn var(&self, side: &std::collections::BTreeMap<DVar, DVar>, v: DVar) -> DVar {
        side.get(&v).copied().unwrap_or(v)
    }
    fn region(&self, side: &std::collections::BTreeMap<DVar, DVar>, r: Region) -> Region {
        match r {
            Region::Var(v) => Region::Var(self.var(side, v)),
            Region::Frozen(Some(p), f) => Region::Frozen(Some(self.var(side, p)), f),
            c => c,
        }
    }
    fn effect(&self, side: &std::collections::BTreeMap<DVar, DVar>, e: &Effect, apps: &crate::ast::EffectApps) -> Effect {
        if side.is_empty() {
            return e.clone();
        }
        let r = |x: Region| self.region(side, x);
        Effect(
            e.0.iter()
                .map(|a| match *a {
                    Atom::Var(v) => Atom::Var(self.var(side, v)),
                    Atom::Read(x) => Atom::Read(r(x)),
                    Atom::Write(x) => Atom::Write(r(x)),
                    Atom::Alloc(x) => Atom::Alloc(r(x)),
                    Atom::Goto(x) => Atom::Goto(r(x)),
                    Atom::Comefrom(x) => Atom::Comefrom(r(x)),
                    Atom::Await(x) => Atom::Await(r(x)),
                    Atom::Spin => Atom::Spin,
                    // Its variable, and what it was given, as named here.
                    Atom::App(n) => {
                        let (head, args) = apps.parts(n);
                        let args = args
                            .into_iter()
                            .map(|x| match x {
                                EArg::Region(x) => EArg::Region(r(x)),
                                EArg::Effect(e) => EArg::Effect(self.effect(side, &e, apps)),
                                EArg::Conv(Conv::Var(v)) => EArg::Conv(Conv::Var(self.var(side, v))),
                                x => x,
                            })
                            .collect();
                        apps.atom(self.var(side, head), args)
                    }
                })
                .collect(),
        )
    }
}
