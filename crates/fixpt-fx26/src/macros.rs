//! Typed hygienic macros, the prototype (`docs/research/typed-macros.md`,
//! "The prototype"): Herman's binding signatures, written with his tree
//! addresses, checked where a macro is defined and used to parse its uses;
//! expansion by transcription, the template's binders made fresh and its
//! free names the standard bindings, through `#%fx`. In the front end
//! written in Rust alone, before either checker: both check what it
//! expands to, printed (`Checker::expand_forms`).
//!
//! A signature is a syntax type, `σ`, of a use's operands (all but the
//! macro's name):
//!
//! ```text
//! σ ::= expr | bvar | id | data | type | label | lambda | dvar | kind | ()
//!     | (σ . σ) | (σ …)                    a pair; a list, of pairs
//!     | (σ … σ ...)                        a list ending in any number of σ
//!     | (import σ β) | (export σ β)        Herman's σ↓β and σ↑β
//!     | (mu v σ) | v | (oneof σ …)         recursion, alternatives
//!     | (literal name)                     a name written as it is (`else`)
//!     | (many σ)                           placed any number of times
//!     | (expr #:type T #:effect E)         a typed hole: of type at most `T`
//!     | (bvar #:type T)                      and effect at most `E`; a binder
//!     | (lambda #:type T)                    of a `T` (either part left out);
//!                                          a lambda of a `T`, written
//! β ::= (rho (ℓ δ) …)                      a rib, {ℓ : δ, …}
//!     | (cage ρ-or-(at ℓ) …)               ribs in order, innermost first; ℓ@γ
//! δ ::= none | var | dvar | place | rib | env
//!                                         var binds a value; dvar, a description;
//!                                         place, both (`letrena`'s, `letreap`'s)
//! ```
//!
//! An address `ℓ` is a word of `A` (car) and `D` (cdr), read right to left
//! as `cadr` is, from the innermost `mu`, `union` member or signature
//! around it; `()`, Herman's `ε`, is that part itself. `id`, `type` and `label` are FX-26's: a variable referred to
//! (as `set!`'s target would be), a description, a tag or field's name;
//! `dvar` a description's binder (a type, an effect, a region: they share
//! one namespace), and `kind` a binder's kind, which names nothing.
//! So is `many`: a pattern variable with an expression in it is placed at
//! most once in a template, affine, unless its part of the signature is
//! `(many σ)`; placed where another macro's signature says `many`, it is
//! taken as placed more than once, so the opt-out is said all the way up
//! a chain of macros (`docs/research/typed-macros.md`).
//!
//! A macro whose signature is `(macro σ desc)` makes a description: its uses
//! are where a description is, in a template's descriptions too, its
//! template a description (`docs/research/datatype-macro.md`, "Keyword
//! constructors: decided", 7).
//!
//! A macro whose signature is `(macro σ defn)` makes definitions
//! (`typed-macros.md`, item 9): its template is one of the kernel's, or a
//! `begin` of them, spliced where it is used, at the top level alone
//! (`Macros::expand_top`). A name a use gives is defined under that name,
//! as the program sees it; one the template writes is made fresh, as its
//! other binders are, so that nothing outside it can name it.
//!
//! A description a template writes is aligned name by name (`Aligner::desc`):
//! a name it binds made fresh, a pattern variable's what the use gave, the
//! words of descriptions as written, and any other name the top level's,
//! `#%toplevel:name` (`typed-macros.md`, "Decided: a template's free
//! description names, one qualified name each").

use crate::error::{FxError, R};
use fixpt_read::{Interner, Span, Sym};
use crate::heap_syn::{At, Kept, Shape, Syn, V};
use fixpt_hash::{HashMap, HashSet};
use std::rc::Rc;
use paths::Path;

mod contract;
mod infer;
pub(crate) mod paths;
mod shown;
pub(crate) mod shapes;
pub(crate) mod hygiene;
pub(crate) mod procedural;

/// A syntax type (Herman's `σ`).
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum STy {
    Expr,
    /// An expression that is a lambda, where a form wants one (`letrec`'s
    /// bindings): as the checkers take one (`Checker::is_lambda`), a
    /// `lambda` or `rlambda`, in `plambda`s and `the`s.
    Lambda,
    Bvar,
    Id,
    Data,
    Type,
    Label,
    /// A description's binder.
    Dvar,
    /// A binder's kind, as written: it names nothing.
    Kind,
    /// A definition, where a template makes one (the kernel's `begin` of
    /// them); no part of a signature, for now.
    Defn,
    /// A macro's transformer a template writes, the `syntax-rules` of a
    /// `define-syntax` it makes: each name in it a reference, renamed where
    /// the template binds it, else the expansion's alias, so that it means
    /// what it does where the template's macro is defined; a pattern
    /// variable placed in it placed any number of times; its `...` the
    /// template's, the defined macro's written `(... ...)` (R7RS).
    Rules,
    /// A module's item, as a program's walk takes one (`scope-forms`): a
    /// definition, a string (a comment), or an expression run as the module
    /// is made.
    Item,
    Nil,
    /// A kernel form's word, `(literal else)`, matched by name: the
    /// kernel's own signatures', and a reserved name's.
    Literal(Sym),
    /// A trailmark, `(trailmark else)`: the name bound to the one whose
    /// number is the second, matched by that binding (`Mark`).
    Mark(Sym, usize),
    Pair(Rc<STy>, Rc<STy>),
    Import(Rc<STy>, Bind),
    Export(Rc<STy>, Bind),
    /// `(mu v σ)`: `σ`, each `Var` in it that refers to this `mu` the
    /// whole again. A value, compared by its structure: no table, nothing
    /// of what was read before it. Its tag, of a signature being inferred
    /// alone: the round and the part it is made for (`infer.rs`'s `build`),
    /// which a signature read never has.
    Mu(Rc<STy>, Option<(usize, usize)>),
    /// A `mu`'s variable, by how many `mu`s are between it and its own
    /// (de Bruijn's numbering): 0 the innermost around it.
    Var(usize),
    /// What may be placed any number of times.
    Many(Rc<STy>),
    /// An `expr` or `bvar` with its type, effect or both written: a typed
    /// hole (`typed-macros.md`, "Proposed: typed holes").
    Typed(Rc<STy>, Hole),
    /// `(oneof σ …)`, written `union` too: one of members told apart by
    /// their shapes in the source.
    Union(Vec<Rc<STy>>),
}

/// What a typed hole says: its type and its effect, each as written, if it
/// is (left out, the macro is polymorphic in it).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Hole {
    ty: Option<Kept>,
    effect: Option<Kept>,
}

impl Hole {
    /// Whether its effect is written `pure`, so that running it twice does
    /// nothing twice.
    fn pure(&self, interner: &Interner) -> bool {
        self.effect.and_then(|e| e.get().sym()).is_some_and(|e| interner.name(e) == "pure")
    }
}

/// What an annotation binds (Herman's `β`): a rib, or a ribcage.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Bind {
    Rib(Vec<(Addr, Delta)>),
    Cage(Vec<Ring>),
    /// A rib of what it binds, as found: the binders a template's
    /// description writes (`Aligner::desc`), no signature's.
    Direct(Vec<Atom>),
    /// What the repetitions before a repeated part bound, as found
    /// (`Level::Earlier`): a repeated parameter's name in its own type.
    Earlier(Vec<Atom>),
    /// The names of the module at an address, `(shape A)`: what `with` and
    /// `include` bind (`binding-shapes.md`), not known to a program's walk
    /// yet (`Level::Shape`).
    Shape(Addr),
}

/// One of a ribcage's: a rib, or the ribcage exported at an address.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Ring {
    Rib(Vec<(Addr, Delta)>),
    At(Addr),
    /// What the module at an address gives (`Bind::Shape`), in a cage: a
    /// file's module parameters, each included in its items.
    Shape(Addr),
}

/// An address's steps from its root, first first: `true` the car.
type Addr = Vec<bool>;

/// What a part at an address binds (Herman's `δ`).
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Delta {
    None,
    Var,
    Dvar,
    /// A description, and a value of it: a place, which is also a value of
    /// type `(place r)`.
    Place,
    Rib,
    Env,
    /// A macro's binder, `(macro σ made)`, the defined macro's signature as
    /// written: a value's name, in scope as `var`'s is; what a use defines
    /// (`(defn (ℓ (macro σ made)))`), its expansion held to it
    /// (`Macros::syntax_held`).
    Syntax(Kept),
}

/// A template's namespaces: values, and descriptions (types, effects,
/// regions and the rest, which share one scope, `parse.rs`'s `dscope`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Ns {
    Value,
    Desc,
}

/// What a name a template refers to is, if the template does not bind it:
/// the top level's value, `(with #%toplevel name)`; the top level's,
/// qualified, `#%toplevel:name` (a description's name, or the module a
/// `select` names); as written (a global's, in `(globals g …)`, which no
/// local can shadow); or nothing, refused (the module a template's `(with
/// m name)` takes from, which a template binds or a use gives, for now).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Free {
    Toplevel,
    /// A name in a macro's transformer a template writes (`STy::Rules`):
    /// the expansion's alias, whatever it names.
    Inner,
    Qualified,
    Plain,
    Bound,
}

/// A macro defined: its signature and clauses.
#[derive(Debug)]
pub(crate) struct Macro {
    sig: Rc<STy>,
    /// Whether it makes definitions, `(macro σ defn)`.
    defn: bool,
    /// Whether it makes a description, `(macro σ desc)`.
    desc: bool,
    /// The binders of its signature's `(poly (binder …) σ)`, if it has one.
    poly: Vec<Kept>,
    clauses: Vec<Clause>,
    /// The text it was read from, its templates' places in it.
    text: Option<std::sync::Arc<str>>,
    /// A procedural macro's transformer (`procedural`), which has no
    /// signature nor clauses: `sig` says nothing of it.
    procedural: Option<Rc<procedural::Procedural>>,
}

/// A trailmark, `(define-syntax else (trailmark ["where it belongs"]))`: a
/// name bound as syntax that is used only as a form's sign, which a
/// `syntax-rules`' `#:trailmarks` matches by its binding, never an
/// expression nor a binder (`typed-macros.md`, "Trailmarks").
/// Kept apart from the macros (`Macros::marks`): a list it heads is no use.
#[derive(Debug)]
pub(crate) struct Mark {
    /// What tells it from any other: the binding, not the name.
    id: usize,
    /// Where it belongs, said where it is used alone.
    said: Option<String>,
}

/// The standard environment's trailmarks, `else` and `=>`, and where each
/// belongs; numbered from the top, apart from those a program defines.
/// The limits of one form's expansion, read as it begins (`Withs::limits`):
/// the uses it may expand, the fuel behind the check of a use that comes
/// back to itself; and how deep they may be, each in the expansion of the
/// one before, past which one that changes each time is taken not to end
/// (`Macros::enter`). 10000 and 1000, or as `FIXPT_MACRO_USES` and
/// `FIXPT_MACRO_DEPTH` set them (`fixpt_runtime::syscall::macro_limit`).
fn limits(at: &Syn) -> R<(usize, usize, bool, bool)> {
    let read = |name| fixpt_runtime::syscall::macro_limit(name).map_err(|why| FxError::at(at.at(), why));
    Ok((read("USES")?, read("DEPTH")?, read("RECHECK")? == 1, read("CONTRACTS")? == 1))
}

/// Use operands `s`, each of its parts in `leaves` (by its value) a
/// pattern variable of its own, `%part:k`, the part `parts[k]`.
fn pseudo_pattern(s: &Syn, leaves: &HashSet<u64>, parts: &mut Vec<Syn>, interner: &mut Interner) -> Syn {
    if leaves.contains(&s.0.raw()) {
        let k = parts.len();
        parts.push(*s);
        return Syn::symbol(s.at(), interner.intern(&format!("%part:{k}")), interner);
    }
    match s.view() {
        V::List { items, tail } => {
            let items: Vec<Syn> = items.iter().map(|x| pseudo_pattern(x, leaves, parts, interner)).collect();
            let tail = tail.map(|t| pseudo_pattern(&t, leaves, parts, interner));
            Syn::of_list(s.at(), &items, tail)
        }
        _ => *s,
    }
}

/// Use operands `s`, each of its parts `done` has (by its value) what it
/// says instead.
fn substituted(s: &Syn, done: &HashMap<u64, Syn>) -> Syn {
    if let Some(r) = done.get(&s.0.raw()) {
        return *r;
    }
    match s.view() {
        V::List { items, tail } => {
            let items: Vec<Syn> = items.iter().map(|x| substituted(x, done)).collect();
            let tail = tail.map(|t| substituted(&t, done));
            Syn::of_list(s.at(), &items, tail)
        }
        _ => *s,
    }
}

/// `s`, each symbol among `at` (by its value) made the name it maps to.
fn renamed_at(s: &Syn, at: &HashMap<u64, Sym>, interner: &mut Interner) -> Syn {
    if let Some(to) = at.get(&s.0.raw()) {
        return Syn::symbol(s.at(), *to, interner);
    }
    match s.view() {
        V::List { items, tail } => {
            let items: Vec<Syn> = items.iter().map(|x| renamed_at(x, at, interner)).collect();
            let tail = tail.map(|t| renamed_at(&t, at, interner));
            Syn::of_list(s.at(), &items, tail)
        }
        V::Vector(items) => {
            let items: Vec<Syn> = items.iter().map(|x| renamed_at(x, at, interner)).collect();
            Syn::new(s.at(), V::Vector(items), interner)
        }
        _ => *s,
    }
}

/// A node of an expansion, as α-equivalence takes it (`Macros::alpha_nodes`):
/// its kind and the nodes under it, by number; a binder whatever its name
/// (of a description's, or a value's); a reference by the binder that binds
/// it, or by its name if free; any other part as it is.
enum AlphaNode {
    Pair(usize, usize),
    Nil,
    Binder(bool),
    Bound(usize),
    Free(Sym, bool),
    Desc(Vec<usize>),
    Seq(usize, bool),
    Form(usize),
    Other(Syn),
}

/// Whether two expansions' nodes are the same up to their binders' names.
fn alpha_same(a: &[AlphaNode], b: &[AlphaNode]) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).all(|(x, y)| match (x, y) {
            (AlphaNode::Pair(p, q), AlphaNode::Pair(r, s)) => p == r && q == s,
            (AlphaNode::Nil, AlphaNode::Nil) => true,
            (AlphaNode::Binder(d), AlphaNode::Binder(e)) => d == e,
            (AlphaNode::Bound(i), AlphaNode::Bound(j)) => i == j,
            (AlphaNode::Free(n, d), AlphaNode::Free(m, e)) => n == m && d == e,
            (AlphaNode::Desc(xs), AlphaNode::Desc(ys)) => xs == ys,
            (AlphaNode::Seq(i, m), AlphaNode::Seq(j, n)) => i == j && m == n,
            (AlphaNode::Form(i), AlphaNode::Form(j)) => i == j,
            (AlphaNode::Other(s), AlphaNode::Other(r)) => same_syntax(s, r),
            _ => false,
        })
}

/// `s` with each symbol `renames` names made what it names, everywhere in
/// it, its places kept.
fn renamed_syn(s: &Syn, renames: &HashMap<Sym, Sym>, interner: &mut Interner) -> Syn {
    match s.view() {
        V::Symbol(n) => match renames.get(&n) {
            Some(to) => Syn::symbol(s.at(), *to, interner),
            None => *s,
        },
        V::List { items, tail } => {
            let items: Vec<Syn> = items.iter().map(|x| renamed_syn(x, renames, interner)).collect();
            let tail = tail.map(|t| renamed_syn(&t, renames, interner));
            Syn::of_list(s.at(), &items, tail)
        }
        V::Vector(items) => {
            let items: Vec<Syn> = items.iter().map(|x| renamed_syn(x, renames, interner)).collect();
            Syn::new(s.at(), V::Vector(items), interner)
        }
        _ => *s,
    }
}

/// How many parts syntax `s` has, each list, pair's tail and atom one.
fn syn_size(s: &Syn) -> usize {
    match s.parts() {
        Some((items, tail)) => 1 + items.map(|x| syn_size(&x)).sum::<usize>() + tail.map_or(0, |t| syn_size(&t)),
        None => 1,
    }
}

/// Whether syntax `a` and `b` are the same, part by part, wherever each is.
/// Whether bindings `p` and `q` say the same: two macros' binders, by what
/// their signatures write.
fn bind_same(p: &Bind, q: &Bind) -> bool {
    let rib = |a: &[(Addr, Delta)], b: &[(Addr, Delta)]| {
        a.len() == b.len()
            && a.iter().zip(b).all(|((x, d), (y, e))| {
                x == y
                    && match (d, e) {
                        (Delta::Syntax(k), Delta::Syntax(l)) => k == l || same_syntax(&k.get(), &l.get()),
                        _ => d == e,
                    }
            })
    };
    match (p, q) {
        (Bind::Rib(a), Bind::Rib(b)) => rib(a, b),
        (Bind::Cage(a), Bind::Cage(b)) => {
            a.len() == b.len()
                && a.iter().zip(b).all(|(x, y)| match (x, y) {
                    (Ring::Rib(x), Ring::Rib(y)) => rib(x, y),
                    _ => x == y,
                })
        }
        _ => p == q,
    }
}

fn same_syntax(a: &Syn, b: &Syn) -> bool {
    match (a.parts(), b.parts()) {
        (Some((mut xs, xt)), Some((mut ys, yt))) => {
            loop {
                match (xs.next(), ys.next()) {
                    (Some(x), Some(y)) if same_syntax(&x, &y) => {}
                    (None, None) => break,
                    _ => return false,
                }
            }
            match (xt, yt) {
                (Some(x), Some(y)) => same_syntax(&x, &y),
                (None, None) => true,
                _ => false,
            }
        }
        // An atom, as a pattern's is matched (`macros-match.fx`'s
        // `same-atom?`): a vector, a real, a ratio, a bignum or a
        // bytevector never the same, as the FX-26 expander has it.
        (None, None) => {
            let v = a.view();
            !matches!(v, V::Vector(_) | V::Bytevector(_) | V::Number(fixpt_read::Num::Real(_) | fixpt_read::Num::Ratio(..) | fixpt_read::Num::Big { .. })) && v == b.view()
        }
        _ => false,
    }
}

const STANDARD_MARKS: [(&str, &str); 2] = [("else", "a `cond`'s, `case`'s or `tagcase`'s last clause's"), ("=>", "a `cond` clause's, before the procedure given the test")];

/// A clause: its pattern (of the operands), its template, and what is done
/// to the template's names where it is transcribed, by their paths in it.
#[derive(Debug)]
struct Clause {
    pattern: Kept,
    /// Its pattern variables that are names (`bvar`, `dvar`, `id`), which
    /// match a name alone (a `label` may be a keyword).
    names: HashSet<Sym>,
    /// Its `syntax-rules`' trailmarks, each the binding it is, which a
    /// use's name matches if it is bound to that one.
    marks: HashMap<Sym, usize>,
    template: Kept,
    actions: HashMap<Path, Action>,
    /// Its pattern's variables, in the order the pattern has them.
    pvars: Vec<(Sym, PInfo)>,
    /// Each typed hole's type, as a use reads it (`(select #%toplevel T)`),
    /// which the use's expression is held to, `(the T e)`; none where the
    /// type names the macro's `poly` binders, which no use can write.
    contracts: HashMap<Sym, Kept>,
    /// Where its macro is defined, what its aliases are read in.
    def_env: hygiene::DefEnv,
    /// Its template's checked uses: each list whose head is a macro, its
    /// operands aligned with that macro's signature as the definition
    /// aligned the template, by where it starts; what transcription makes
    /// there needs no alignment as it is expanded (`Withs::trusted`;
    /// `typed-macros.md`, "Decided: a use a template made is not aligned
    /// again").
    checked_uses: HashSet<i64>,
}

/// What becomes of one of a template's parts: a name made fresh, one name
/// for the binder found at a path and for each reference to it; a name
/// free in the template, its alias, `%~K.N:name`, which the resolution after
/// expansion makes the name where the macro is defined, nothing at the use
/// capturing it (`hygiene`): a top-level macro's the top level's, `(with
/// #%toplevel name)` or, a description's, `#%toplevel:name`
/// (`typed-macros.md`, item 5).
///
/// A file's macro (`import-with-syntax`) means what it meant in its file: a
/// free name the file's own, `(with %shared:key name)`, the one value every
/// load of the file is, which nothing shadows; else the standard one, `(with
/// #%fx name)` (a file sees the standard environment alone), both by its
/// alias; a type, read
/// through the file's module, `(select %shared:key type)`, or the standard
/// environment, `(select #%fx type)`; a use of another of the file's
/// macros, that macro, by the name the importer has it by
/// (`typed-macros.md`, "Decided: macros come with a file").
#[derive(Clone, Debug)]
enum Action {
    /// The binder's path, and how many ellipses it is under.
    Rename(Path, usize),
    /// A name free in the template: its alias, `%~K.N:name`, which the
    /// resolution after expansion makes the name where the macro is
    /// defined (`hygiene`).
    Alias,
    ModuleType(Sym),
    /// A type of a file's, its macros imported of an instance of it, `lib`
    /// (`binding-shapes.md`, step 4 (c)): `(select lib T)`, `lib` an alias,
    /// so that a binder at the use is kept from capturing it (`hygiene`).
    InstanceType(Sym),
    /// A description a file's frame holds (`TODO.md` §300): `(select (with
    /// lib frame) %ft:T)`, `lib` the file's module, an alias if it is an
    /// instance's, as `InstanceType`'s.
    FrameType(Sym, Sym, bool),
    StandardType,
    MacroHead(Sym),
    /// A trailmark of a file's, written by a template: the name the
    /// importer has it by.
    Mark(Sym),
}

/// What a file's macros are defined in (`Macros::define_file`): the
/// hidden global every load of the file is, `%shared:key`, or the instance
/// of it, if `instance` (`binding-shapes.md`, step 4 (c)); the values and
/// types its module shows; each of its macros' names, and the name the
/// importer has it by, which no program writes; and which names are
/// standard.
pub struct FileScope<'a> {
    pub shared: Sym,
    pub instance: bool,
    pub values: fixpt_hash::HashSet<Sym>,
    pub types: fixpt_hash::HashSet<Sym>,
    pub internal: HashMap<Sym, Sym>,
    pub frame: Frame,
    pub is_standard: &'a dyn Fn(Sym) -> bool,
}

/// A module file's frame (`TODO.md` §300; `Checker::frame_text`), if it
/// has one: its member's name, and the values and the descriptions it
/// holds, which the file does not show and its macros' expansions may
/// reach, through it (a description by its alias there, `%ft:name`).
pub type Frame = Option<Rc<FrameOf>>;

#[derive(Debug)]
pub struct FrameOf {
    pub name: Sym,
    pub values: HashSet<Sym>,
    pub descs: HashSet<Sym>,
}

/// Whether frame `frame` holds value `n`.
pub(crate) fn frame_holds(frame: &Frame, n: Sym) -> bool {
    frame.as_ref().is_some_and(|f| f.values.contains(&n))
}

/// Whether frame `frame` holds description `n`.
pub(crate) fn frame_holds_desc(frame: &Frame, n: Sym) -> bool {
    frame.as_ref().is_some_and(|f| f.descs.contains(&n))
}

/// What `import-with-syntax` of a file reads of it, in order
/// (`Macros::define_file`; `binding-shapes.md`, step 4): its macros
/// written, the files whose macros it imports, and the uses at its top
/// level that may make macros, each with whether a `hide` holds it.
pub enum FileEntry {
    /// A `define-syntax`, `define-syntax-rec` or `begin-for-syntax`.
    Syntax(Syn, bool),
    /// An `import-with-syntax` of the file it reads, with its `(only …)`
    /// or `(except …)`, if any.
    Import(Rc<FileMacros>, Option<(bool, Vec<Sym>)>, bool),
    /// A form at the file's top level, which a use of a macro of the
    /// file's that makes definitions may make macros of (`TODO.md` §287).
    Use(Syn, bool),
}

/// A file's macros, as `import-with-syntax` reads them (`FileEntry`): the
/// hidden global every load of the file is, `%shared:key`, the values
/// and types its module shows, the key the importer names its macros by
/// (`%syntax:key:name`), the keys of the forms its uses expand as at an
/// import (`m{F}mm`, apart from its own expansion's, `m{F}m`), and its
/// text, which their places are in.
pub struct FileMacros {
    pub shared: Sym,
    pub values: HashSet<Sym>,
    pub types: HashSet<Sym>,
    pub frame: Frame,
    pub key: String,
    pub prefix: String,
    pub text: std::sync::Arc<str>,
    pub entries: Vec<FileEntry>,
}

/// The prefix of a module file's forms' keys (`Macros::form_begin`), of
/// its key, `key`, `input:` or not: `m{F}m` for its own expansion, `m{F}mm`
/// for the uses an importer expands (`define_file`), `F` a hash of the
/// key as a string's (`syn_hash`), so that no two files' forms, nor a
/// file's and an importer's, have one key, nor so their expansions' tags,
/// which their definition environments are kept by.
pub fn file_prefix(key: &str, imported: bool) -> String {
    const P: i64 = 2_147_483_647;
    let path = key.strip_prefix("input:").unwrap_or(key);
    let f = (2 * 65599 + fixpt_heap::heap::string_hash_of(path) % P) % P;
    format!("m{f}m{}", if imported { "m" } else { "" })
}

/// The prefix of the keys of the uses an importer of an instance, `lib`,
/// of a file expands, of the file's, `prefix` (`m{F}mm`): `m{F}mm{G}m`, `G`
/// a hash of `lib` as a symbol's (`syn_hash`), so that two instances' are
/// apart (FX-26's `instance-prefix`, alike).
pub fn instance_prefix(prefix: &str, lib: &str) -> String {
    const P: i64 = 2_147_483_647;
    let g = (65599 + fixpt_heap::heap::string_hash_of(lib) % P) % P;
    format!("{prefix}{g}m")
}

/// The macros defined, and the syntax types of the kernel's forms, for
/// checking templates. Cloned to be put back (`Checker::macros_kept`).
#[derive(Clone, Default)]
pub struct Macros {
    /// The kernel's tables, read once and shared (`ensure_kernel`).
    k: Rc<Kernel>,
    defined: HashMap<Sym, Rc<Macro>>,
    fresh: usize,
    /// The text being read, if it is known (`Checker::read_in`): a macro
    /// defined in it has its templates' places in it.
    pub(crate) reading: Option<std::sync::Arc<str>>,
    /// What the expander saw of `with`s and of the modules forms open,
    /// out of line (`Withs`): a `Macros` is moved whole.
    pub(crate) withs: Box<Withs>,
    /// Where each macro the program has by its name was defined: its
    /// `define-syntax`, or the `import-with-syntax` that brought it. A
    /// program is expanded before it is checked, so what is defined when a
    /// form is checked may be defined after it (`defined_before`).
    defined_at: HashMap<Sym, At>,
    /// Whether a template is being transcribed for its check, its holes'
    /// calls in place of a use's expressions (`template_checks`).
    checking: bool,
}

/// A `(macro σ made)` entry's signature read: its syntax type, and whether it
/// makes definitions, or a description.
pub(crate) type SyntaxSig = (Rc<STy>, bool, bool);

/// A macro an expansion defined: its name, where, and the macro the name
/// was before, if any.
pub(crate) type MadeSyntax = (Sym, At, Option<Rc<Macro>>);

/// What the expander saw of `with`s, for the checkers, and the shapes it
/// knows of the modules forms open.
#[derive(Clone, Default)]
pub(crate) struct Withs {
    /// The phase-1 forms in force (`begin-for-syntax`'s, in order, each its
    /// text and its file's directory), each transformer defined now running
    /// where they are (`phase1.rs`).
    pub(crate) phase1: Rc<Vec<crate::phase1::Form>>,
    /// The uses of macros the expansion is inside, the innermost last: each
    /// its macro, its form, and how many parts the form has, once it is
    /// looked at (`Macros::enter`).
    pub(crate) chain: Vec<(Sym, Syn, Option<usize>)>,
    /// The limits of the expansion of the form the chain is in, its uses
    /// and their depth (`limits`); and whether a use a template made is
    /// aligned again (`FIXPT_MACRO_RECHECK`).
    pub(crate) limits: (usize, usize),
    pub(crate) recheck: bool,
    /// Whether a procedural macro's expansions are held to its contract
    /// (`FIXPT_MACRO_CONTRACTS`, on unless 0).
    pub(crate) contracts: bool,
    /// The places of the uses this form's expansion has made at a
    /// template's checked uses (`Clause::checked_uses`): each fits its
    /// macro's signature, by the definition's alignment, and is not
    /// aligned again.
    pub(crate) trusted: HashSet<At>,
    /// The trailmarks defined, by name (`Mark`): the standard ones are the
    /// kernel's. Here, out of line: a `Macros` is moved whole, and is in the
    /// checker's frames.
    pub(crate) marks: HashMap<Sym, Rc<Mark>>,
    /// By each `with` form's place, the macros used in its body by names
    /// written in the source, each with the use's place: refused there if
    /// the module gives a value of the name (`Checker::with_as`), which the
    /// program would seem to call, and the expander cannot see.
    pub(crate) with_uses: HashMap<Span, Vec<(Sym, Span)>>,
    /// By each `(with m name)` form's place that a template wrote, the name
    /// and its place: refused there if the module gives no value of it
    /// (`Checker::with_as`), which would otherwise be what it is where the
    /// macro is used, a binding there capturing it. And each a path wrote,
    /// `a::b::c` (`TODO.md` §296), the same: the path to that name its name,
    /// and `true`.
    pub(crate) projections: HashMap<Span, (Sym, Span, bool)>,
    /// The macros an expansion defined (`Macros::expand_defn`), each with
    /// where, and what its name was before: the driver holds each to the
    /// globals, as it does a written one, and undoes them if the form is
    /// refused (`Macros::made_undone`).
    pub(crate) made_syntax: Vec<MadeSyntax>,
    /// Each `(macro σ made)` entry's signature, read where the signature it is
    /// in is (`Macros::signature`): what a template reads a use of the
    /// macro it binds by (`Aligner::heads_read`). Out of line, as all of
    /// this is: a `Macros` is held in frames.
    pub(crate) syntax_sigs: HashMap<Kept, SyntaxSig>,
    /// The shapes known (`shapes`): the top level's names', files'.
    shapes: shapes::Known,
    /// Where the macro each expansion's aliases are of was defined, by the
    /// expansion's tag (`hygiene::DefEnv`); a template's check's is `0`.
    pub(crate) def_envs: HashMap<String, hygiene::DefEnv>,
    /// Each expansion's tag, by its number (`Macros::expansion_begun`):
    /// `K.N`, the form's key and how many expansions of it so far, `N`, so
    /// that its aliases, `%~K.N:x`, are of the form and the macros it uses
    /// alone, not of how many expansions the forms before it made.
    pub(crate) tags: HashMap<u32, String>,
    pub(crate) expanded: u32,
    /// How many binders at uses the resolution renamed in this form, which
    /// would have captured a name a module file's own macro introduces
    /// (`%x~K.N`).
    pub(crate) captors: usize,
    /// The top-level form's key, which every name it makes fresh carries
    /// (`Macros::form_begin`); each key's hash, with how many forms had it;
    /// the prefix of a module file's forms' keys, none for a program's
    /// (`file_prefix`).
    pub(crate) form_key: String,
    pub(crate) keys_seen: HashMap<i64, u32>,
    pub(crate) module_prefix: String,
    /// Where the macros defined now are, unless a file's scope is given:
    /// the top level, or a module file's items, as its own macros are
    /// (`Checker::file_own_expanded`).
    pub(crate) def_env: hygiene::DefEnv,
    /// The heap the macros' syntax is in, its symbols, and whether they
    /// are lent now (`Checker::syn`; `docs/research/heap-syntax.md`):
    /// shared by a copy of the macros put back, whose handles (`Kept`) are
    /// into it; here, behind `Withs`'s box, so that a checker is no larger.
    pub(crate) world: Rc<std::cell::RefCell<SynWorld>>,
}

/// What syntax is in: a heap (made when first wanted), its symbols, and
/// whether they are lent now; or, a session's checker's, its session's
/// heap, lent by the session around each call (`Checker::with_heap`).
#[derive(Default)]
pub(crate) struct SynWorld {
    pub(crate) heap: Option<Box<fixpt_heap::Heap>>,
    /// The names its heap is made with, when it is: its checker's
    /// interner's, made first (`Checker::with_convention`).
    pub(crate) names: Option<fixpt_memmgmt::names::Owner>,
    pub(crate) syms: crate::heap_syn::SymTable,
    pub(crate) lending: bool,
    pub(crate) session: bool,
}

/// The kernel's tables (`macros-kernel.fx`), read once, never changed.
#[derive(Default)]
struct Kernel {
    /// Its forms' signatures, by name.
    forms: HashMap<String, Rc<STy>>,
    /// Its definitions' forms, by name (its `begin` of them is not its
    /// `begin` of expressions).
    definitions: HashMap<String, Rc<STy>>,
    /// The words of descriptions: those a list's head may be, and those
    /// read anywhere, as written (`Aligner::desc`).
    heads: HashSet<String>,
    words: HashSet<String>,
    /// The type forms' heads, whose template makes a description.
    type_forms: HashSet<String>,
    /// The binding structure of the forms its list has not (yet):
    /// `scope-forms`, for a program's walk alone; and its definitions.
    scope_forms: HashMap<String, Rc<STy>>,
    scope_definitions: HashMap<String, Rc<STy>>,
    /// The standard environment's trailmarks (`STANDARD_MARKS`), which a
    /// file sees too.
    marks: HashMap<Sym, Rc<Mark>>,
    /// The words its signatures write, `(literal else)`: which its forms
    /// read by name, where a label may be too (`tagcase`'s arms), so that
    /// no use gives a label one (`literal_word`).
    literals: HashSet<Sym>,
}

/// The kernel's forms a template may use, with their binding structure
/// (each signature of a form's operands), and the keywords: data, which the
/// expander written in FX-26 reads too. A form not here is refused in a
/// template; what has no binders is an application, of expressions.
const KERNEL: &str = include_str!("macros-kernel.fx");

/// How deep two members of a `union` are compared for overlap (`sty`):
/// members must differ within so many lists.
const OVERLAP_DEPTH: usize = 6;
/// How deep `fits` looks, more than `OVERLAP_DEPTH`.
const FITS_DEPTH: usize = OVERLAP_DEPTH + 2;

/// The list quoted in the kernel's `(define name datum (quote list))`.
/// Each word `s` writes as `(literal word)`, onto `out`, a dotted list's too.
fn literals_in(s: &Syn, interner: &Interner, out: &mut HashSet<Sym>) {
    let V::List { items, tail } = s.view() else { return };
    match (items.as_slice(), &tail) {
        ([h, w], None) if h.sym().is_some_and(|h| interner.name(h) == "literal") && w.sym().is_some() => _ = out.insert(w.sym().expect("a word")),
        _ => items.iter().chain(tail.as_ref()).for_each(|i| literals_in(i, interner, out)),
    }
}

fn kernel_list(forms: &[Syn], interner: &Interner, name: &str) -> Vec<Syn> {
    let def = forms.iter().find_map(|f| match f.list().as_deref() {
        Some([_, n, _, q]) if n.sym().is_some_and(|n| interner.name(n) == name) => Some(q.clone()),
        _ => None,
    });
    let quoted = def.and_then(|q| q.list().and_then(|l| l.get(1).copied())).expect("the kernel's list");
    quoted.list().expect("a list")
}

/// What a transcription has made so far: each binder's fresh name, by its
/// path and the repetitions it is in; and how many times each repeated
/// binder was repeated, by its path and the repetitions around that.
#[derive(Default)]
struct Made {
    fresh: HashMap<(Path, Vec<usize>), Sym>,
    counts: HashMap<(Path, Vec<usize>), usize>,
}

/// Where a syntax type is aligned with syntax: a macro's pattern, a
/// template, or a use.
#[derive(Clone, Copy, PartialEq)]
enum Mode {
    Pattern,
    Template,
    Use,
    /// A program's form, after expansion: a template with no pattern
    /// variables, its binders and references found, as the checkers will
    /// read them (`binding-shapes.md`, step 1; `Macros::alpha_renamed`).
    Program,
}

/// One node of syntax aligned with a syntax type.
struct Node {
    syn: Syn,
    /// Its path from the template's (or pattern's) root.
    path: Path,
    /// The type at it, its annotations taken off.
    core: Rc<STy>,
    /// Its imports, outermost first, and its export, each with the root its
    /// addresses are from.
    imports: Vec<(Bind, usize)>,
    export: Option<(Bind, usize)>,
    /// Whether its part of the signature is `(many …)`.
    many: bool,
    /// Its part's typed hole, if the signature types it.
    hole: Option<Hole>,
    /// Whether it is a whole description a template writes (`Aligner::desc`).
    desc: bool,
    /// Whether an ellipsis follows it, so that it is repeated.
    repeated: bool,
    /// Whether it is a list whose head a `(macro σ made)` entry may bind, read
    /// by its scope (`Aligner::pending`): its environment found.
    head: bool,
    kids: Kids,
}

enum Kids {
    Pair(usize, usize),
    Nil,
    /// A pattern variable (in a pattern, or placed in a template).
    PVar(Sym),
    /// A template's binder, a name it writes in a binding position, of a
    /// namespace.
    Binder(Sym, Ns),
    /// A name in a template referred to, in a namespace, and what it is if
    /// the template does not bind it.
    Ref(Sym, Ns, Free),
    /// A description's parts, a list a template writes, in order.
    Desc(Vec<usize>),
    /// A list given by ellipsis, `(p ...)`: its element, repeated; whether
    /// each element is in the scope of those before it (a ribcage's list,
    /// a `let*`'s clauses or a `begin`'s definitions), not a `let`'s.
    Seq(usize, bool),
    /// A form in a template, its operands (or, an application's, itself).
    Form(usize),
    Other,
}

/// What an environment is made of: a pattern variable bound (`bvar`,
/// `dvar`), the rib or ribcage a pattern variable exports, a template's own
/// binder; each bound in a namespace (Herman's δ, one per namespace). A
/// pattern variable's, with how many lists by ellipsis gathered it: 0 its
/// own repetition's, as an element's part names it; 1 every repetition's,
/// as the list's export gathers its elements' (`let`'s body sees every
/// binder), and so on out (`TODO.md` §223).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Atom {
    Var(Sym, Ns, usize),
    RibOf(Sym),
    Lit(usize, Ns),
}

/// Each pattern variable, template binder and name referred to, by node,
/// with its environment, whether it is in a `many` part, and how many
/// ellipses it is under (`walk`).
type Found = Vec<(usize, Env, bool, usize)>;

/// An environment, innermost first, as the walk makes it: what each
/// import added, shared, so that a part's is its parent's with its own
/// added, not all of it made again (a module's items each bind a level).
#[derive(Clone, Debug, Default)]
pub(crate) struct Env(Vec<Rc<Vec<Level>>>);

impl Env {
    /// This, with `levels` inside it.
    fn within(&self, levels: Vec<Level>) -> Env {
        let mut out = self.clone();
        if !levels.is_empty() {
            out.0.push(Rc::new(levels));
        }
        out
    }

    /// Its levels, innermost first.
    fn levels(&self) -> impl Iterator<Item = &Level> {
        self.0.iter().rev().flat_map(|c| c.iter())
    }

    fn to_vec(&self) -> Vec<Level> {
        self.levels().cloned().collect()
    }
}

/// One level of an environment: a rib, or a pattern variable's ribcage; or,
/// in a repeated element of a ribcage's list, what the repetitions before
/// it bound, which its own binders' names cannot tell from its own.
#[derive(Clone, Debug, PartialEq)]
enum Level {
    Rib(Rc<Vec<Atom>>),
    Cage(Sym),
    Earlier(Rc<Vec<Atom>>),
    /// What the module at a node gives (`Bind::Shape`), whose names a
    /// program's walk does not know yet: a name looked for past it may be
    /// one of them.
    Shape(usize),
}

/// A pattern variable: its type, its kind (the type's annotations off), and
/// its environment as the signature declares it.
#[derive(Clone, Debug)]
struct PInfo {
    core: Rc<STy>,
    declared: Vec<Level>,
    /// Whether it may be placed any number of times (`(many …)`).
    many: bool,
    /// Its typed hole, if the signature types it.
    hole: Option<Hole>,
    /// How many ellipses its pattern has it under: what the use gives of it
    /// is a list of so many levels.
    depth: usize,
}

/// Syn aligned with syntax types, as a tree of `Node`s.
struct Aligner<'m> {
    m: &'m Macros,
    interner: &'m Interner,
    mode: Mode,
    pvars: &'m HashMap<Sym, PInfo>,
    nodes: Vec<Node>,
    /// The names a program's walk cannot place: written where an address
    /// reaches no part (inside a quasiquoted vector), so neither they nor
    /// a binder of their name are renamed (`alpha_renamed`).
    unplaced: Vec<Sym>,
    /// The parts left to fill (`run`).
    work: Vec<Step>,
    /// How each list whose head a `(macro σ made)` entry may bind is read so
    /// far, by its syntax, if the template uses a macro with one
    /// (`Macros::template_aligned`); and the lists found so, each with
    /// whether a definition is there.
    heads: Option<&'m HashMap<u64, Head>>,
    pending: Vec<(usize, bool)>,
    /// A program's form read by its scopes (`Aligner::program`): the lists
    /// a macro's name heads read as applications so far, by their paths,
    /// their heads bound around them; any other such list a use. Each
    /// such list pending, for the walk to find what binds its head.
    apps: Option<HashSet<Path>>,
    /// Where a form is expanded (`Macros::uses_found`): a use whole, its
    /// parts aligned no further (its expansion is, in its turn); else by
    /// its signature.
    whole: bool,
}

/// How a template reads a list whose head a `(macro σ made)` entry may bind:
/// a use of the macro of that entry's signature, or an application.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Head {
    Macro(Kept),
    Application,
}

/// A part to fill: its node, its type, its syntax, and the node its
/// addresses are from.
type Step = (usize, Rc<STy>, Syn, usize);

impl Macros {
    /// Whether `n` is a word the kernel's signatures write, `(literal
    /// else)`, which its forms read by name where a label may be too: a
    /// template's label never fits one (`fits_shaped`), so a use's label is
    /// never one, and `(tagcase e (t x body) …)` of a label `t` stays a
    /// tag's arm (Heist's should-work note, entry 5). Any other reserved
    /// word is a label as any name is, `(isearch-but s (prompt p))`.
    fn literal_word(&self, n: Sym) -> bool {
        self.k.literals.contains(&n)
    }

    fn ensure_kernel(&mut self, interner: &mut Interner) -> R<()> {
        if !self.k.forms.is_empty() {
            return Ok(());
        }
        let forms = crate::heap_syn::read_syn_unplaced(KERNEL, interner).map_err(|e| FxError::at(e.span, format!("the kernel's syntax types: {}", e.message)))?;
        let mut k = Kernel::default();
        // `defn`, which the kernel's signatures name, and no macro's.
        let mut named: HashMap<Sym, Rc<STy>> = HashMap::from_iter([(interner.intern("defn"), Rc::new(STy::Defn))]);
        for f in &kernel_list(&forms, interner, "kernel-forms") {
            let items = f.list().expect("a kernel entry");
            let what = interner.name(items[0].sym().expect("a head")).to_string();
            let name = items[1].sym().expect("a name");
            let t = self.sty(&items[2], interner, &named)?;
            match what.as_str() {
                "define" => _ = named.insert(name, t),
                "definition" => _ = k.definitions.insert(interner.name(name).to_string(), t),
                _ => _ = k.forms.insert(interner.name(name).to_string(), t),
            }
        }
        for f in &kernel_list(&forms, interner, "scope-forms") {
            let items = f.list().expect("a scope entry");
            let what = interner.name(items[0].sym().expect("a head")).to_string();
            let name = items[1].sym().expect("a name");
            let t = self.sty(&items[2], interner, &named)?;
            match what.as_str() {
                "define" => _ = named.insert(name, t),
                "definition" => _ = k.scope_definitions.insert(interner.name(name).to_string(), t),
                _ => _ = k.scope_forms.insert(interner.name(name).to_string(), t),
            }
        }
        let names = |list: &str, i: &Interner| kernel_list(&forms, i, list).iter().map(|w| i.name(w.sym().expect("a word")).to_string()).collect::<HashSet<_>>();
        k.heads = names("description-heads", interner);
        k.words = names("description-words", interner);
        k.type_forms = names("type-forms", interner);
        for list in ["kernel-forms", "scope-forms"] {
            kernel_list(&forms, interner, list).iter().for_each(|f| literals_in(f, interner, &mut k.literals));
        }
        for (i, (n, said)) in STANDARD_MARKS.iter().enumerate() {
            k.marks.insert(interner.intern(n), Rc::new(Mark { id: usize::MAX - i, said: Some(said.to_string()) }));
        }
        self.k = Rc::new(k);
        Ok(())
    }

    /// The trailmark `name` is bound to, if it is one: defined, or the
    /// standard environment's, unless a macro of that name hides it.
    pub(crate) fn mark_of(&self, name: Sym) -> Option<&Rc<Mark>> {
        if self.defined.contains_key(&name) {
            return None;
        }
        self.withs.marks.get(&name).or_else(|| self.k.marks.get(&name))
    }

    /// Where trailmark `name` belongs, if it is one: what is said where it
    /// is used alone.
    pub fn trailmark(&self, name: Sym) -> Option<Option<&str>> {
        self.mark_of(name).map(|m| m.said.as_deref())
    }

    /// Whether `name` is a macro defined.
    pub fn is_macro(&self, name: Sym) -> bool {
        self.defined.contains_key(&name)
    }

    /// If `name` is a macro defined, whether before what is at `at` (one
    /// defined in another file, or where unknown, is taken to be), and if
    /// not, where.
    pub fn defined_before(&self, name: Sym, at: Span) -> Option<Result<(), Span>> {
        if !self.is_macro(name) {
            return None;
        }
        Some(match self.defined_at.get(&name).map(|d| d.span()) {
            Some(d) if d.file == at.file && d.start > at.start => Err(d),
            _ => Ok(()),
        })
    }

    /// A syntax type read, `named`'s names the kernel's abbreviations.
    fn sty(&mut self, s: &Syn, interner: &Interner, named: &HashMap<Sym, Rc<STy>>) -> R<Rc<STy>> {
        self.sty_in(s, interner, named, &mut Vec::new())
    }

    /// `mu` `t`, read whole, at `at`: each `oneof` in it whose members
    /// refer to a `mu` around them, which its reading left (`sty_in`), its
    /// members closed, told apart by their shapes.
    fn mu_read(&self, t: Rc<STy>, at: At) -> R<Rc<STy>> {
        if self.oneofs_apart(&t, &mut Vec::new()) { Ok(t) } else { Err(FxError::at(at, format!("a syntax type: {ONEOF_APART}"))) }
    }

    /// Whether, of `t` under the `mu`s `env` (closed, the innermost last),
    /// each `oneof` whose members refer to one of them has them apart.
    fn oneofs_apart(&self, t: &Rc<STy>, env: &mut Vec<Rc<STy>>) -> bool {
        match &**t {
            STy::Mu(b, _) => {
                env.push(closed_by(t, env));
                let r = self.oneofs_apart(b, env);
                env.pop();
                r
            }
            STy::Union(ms) => {
                if ms.iter().any(|m| has_free(m, 0)) {
                    let closed: Vec<Rc<STy>> = ms.iter().map(|m| closed_by(m, env)).collect();
                    if any_overlap(self, &closed) {
                        return false;
                    }
                }
                ms.iter().all(|m| self.oneofs_apart(m, env))
            }
            STy::Pair(a, d) => self.oneofs_apart(a, env) && self.oneofs_apart(d, env),
            STy::Import(b, _) | STy::Export(b, _) | STy::Many(b) | STy::Typed(b, _) => self.oneofs_apart(b, env),
            _ => true,
        }
    }

    /// `sty`'s reading, the `mu` variables in scope `mus`, the innermost
    /// last (none, a list's by ellipsis).
    fn sty_in(&mut self, s: &Syn, interner: &Interner, named: &HashMap<Sym, Rc<STy>>, mus: &mut Vec<Option<Sym>>) -> R<Rc<STy>> {
        let bad = |why: &str| FxError::at(s.at(), format!("a syntax type: {why}"));
        let t = match &s.view() {
            V::Nil => STy::Nil,
            V::Symbol(n) => {
                if let Some(i) = mus.iter().rev().position(|v| *v == Some(*n)) {
                    STy::Var(i)
                } else if let Some(t) = named.get(n) {
                    return Ok(t.clone());
                } else {
                    match interner.name(*n) {
                        "expr" => STy::Expr,
                        "lambda" => STy::Lambda,
                        "bvar" => STy::Bvar,
                        "id" => STy::Id,
                        "data" => STy::Data,
                        // A description, kinded after expansion as an
                        // expression is typed (the user's, 2026-11-15).
                        "desc" => STy::Type,
                        "type" => return Err(bad("a part that is a description is written `desc`, not `type`")),
                        "label" => STy::Label,
                        "dvar" => STy::Dvar,
                        "kind" => STy::Kind,
                        "item" => STy::Item,
                        other => return Err(bad(&format!("`{other}` is none (`expr`, `bvar`, `id`, `data`, `desc`, `label`, `lambda`, `dvar`, `kind`, `item`, or a `mu`'s variable)"))),
                    }
                }
            }
            // `(σ … σ ...)`: a list ending in any number of the last `σ`.
            V::List { items, tail: None } if items.len() >= 2 && is_ellipsis(&items[items.len() - 1], interner) => {
                // Read under the list's own `mu`, which no name refers to.
                mus.push(None);
                let elem = self.sty_in(&items[items.len() - 2], interner, named, mus);
                mus.pop();
                let mut t = seq(elem?);
                if mus.is_empty() {
                    t = self.mu_read(t, s.at())?;
                }
                for x in items[..items.len() - 2].iter().rev() {
                    t = Rc::new(STy::Pair(self.sty_in(x, interner, named, mus)?, t));
                }
                return Ok(t);
            }
            V::List { items, tail } => {
                let head = items[0].sym().map(|h| interner.name(h));
                match (head, &items[..], tail) {
                    (Some("import" | "export"), [_, body, b], None) => {
                        let body = self.sty_in(body, interner, named, mus)?;
                        let b = bind(b, interner)?;
                        if head == Some("import") && matches!(&b, Bind::Rib(es) if es.iter().any(|e| matches!(e.1, Delta::Syntax(_)))) {
                            return Err(bad("a macro's binder, `(macro …)`, says what a use defines, in what its signature makes, `(defn D …)`"));
                        }
                        if head == Some("import") { STy::Import(body, b) } else { STy::Export(body, b) }
                    }
                    (Some("mu"), [_, v, body], None) => {
                        let v = v.sym().ok_or_else(|| bad("`(mu variable type)`"))?;
                        mus.push(Some(v));
                        let body = self.sty_in(body, interner, named, mus);
                        mus.pop();
                        let body = body?;
                        if !guarded(&body, 0) {
                            return Err(bad("a `mu`'s variable is used where no pair is around it (Herman's types are contractive)"));
                        }
                        let t = Rc::new(STy::Mu(body, None));
                        return if mus.is_empty() { self.mu_read(t, s.at()) } else { Ok(t) };
                    }
                    (Some("union" | "oneof"), [_, ms @ ..], None) => {
                        let ms = ms.iter().map(|m| self.sty_in(m, interner, named, mus)).collect::<R<Vec<_>>>()?;
                        // Members that refer to a `mu` around them, checked
                        // when it is read whole (`mu_read`).
                        if !ms.iter().any(|m| has_free(m, 0)) && any_overlap(self, &ms) {
                            return Err(bad(ONEOF_APART));
                        }
                        STy::Union(ms)
                    }
                    (Some("many"), [_, body], None) => STy::Many(self.sty_in(body, interner, named, mus)?),
                    // `(expr #:type T #:effect E)`, `(bvar #:type T)`: a list
                    // whose second is a keyword, which no syntax type is.
                    (Some(kind @ ("expr" | "bvar" | "lambda")), [_, k, ..], None) if matches!(k.view(), V::Keyword(_)) => {
                        let hole = hole(&items[1..], kind, s, interner)?;
                        let core = match kind {
                            "expr" => STy::Expr,
                            "bvar" => STy::Bvar,
                            _ => STy::Lambda,
                        };
                        STy::Typed(Rc::new(core), hole)
                    }
                    // The kernel's words, as its signatures write them, and a
                    // reserved name; a name a macro matches, a trailmark.
                    (Some("literal"), [_, n], None) => {
                        let n = n.sym().ok_or_else(|| bad("`(literal name)`"))?;
                        if !self.k.forms.is_empty() && !reserved(interner.name(n)) {
                            return Err(bad(&format!("`(literal {0})` is a kernel form's word; a name a macro's pattern matches is a trailmark's, `(trailmark {0})`", interner.name(n))));
                        }
                        STy::Literal(n)
                    }
                    (Some("trailmark"), [_, n], None) => {
                        let n = n.sym().ok_or_else(|| bad("`(trailmark name)`"))?;
                        match self.mark_of(n) {
                            Some(m) => STy::Mark(n, m.id),
                            None => return Err(bad(&no_trailmark(interner.name(n)))),
                        }
                    }
                    _ => {
                        let rest = match (items.len(), tail) {
                            (1, None) => Rc::new(STy::Nil),
                            (1, Some(t)) => self.sty_in(t, interner, named, mus)?,
                            _ => self.sty_in(&Syn::of_list(s.at(), &items[1..].to_vec(), tail.clone()), interner, named, mus)?,
                        };
                        STy::Pair(self.sty_in(&items[0], interner, named, mus)?, rest)
                    }
                }
            }
            _ => return Err(bad("not one")),
        };
        Ok(Rc::new(t))
    }


    /// The type of an element of list type `t`, if a template or pattern may
    /// give its elements by ellipsis, and whether each is in the scope of
    /// those before it: a `mu` of `()` and of pairs of an element and
    /// itself, which binds no more than what each element exports, all of
    /// them together (a `let`'s), the rest perhaps in the scope of what the
    /// element binds (a `lambda`'s parameters, each in the later ones'
    /// types); or each element's in the scope of those after it, the list a
    /// ribcage (a `let*`'s, a `begin`'s definitions). Each pair's element,
    /// with the part of the pair's export that is its.
    fn seq_of(&self, t: &Rc<STy>) -> Option<(Rc<STy>, bool)> {
        let body = unfolded(t)?;
        let STy::Union(ms) = &*body else { return None };
        if let Some(elem) = self.cage_seq_of(t, ms) {
            return Some((elem, true));
        }
        let (mut elems, mut nil, mut scoped) = (Vec::new(), false, false);
        for m in ms {
            let (core, entries) = match &**m {
                STy::Export(b, Bind::Rib(es)) => (b, Some(es)),
                STy::Export(..) | STy::Import(..) => return None,
                _ => (m, None),
            };
            // The rest, and what of the element's it is in the scope of.
            let (rest, inner) = match &**core {
                STy::Pair(_, d) => match &**d {
                    STy::Import(r, Bind::Rib(fs)) => (r, Some(fs)),
                    _ => (d, None),
                },
                _ => (core, None),
            };
            match &**core {
                STy::Nil => nil = true,
                STy::Pair(a, _) if same(rest, t) => {
                    if let Some(fs) = inner {
                        let mine: Vec<(Addr, Delta)> = entries.into_iter().flatten().filter(|(addr, _)| addr.first() == Some(&true)).cloned().collect();
                        if *fs != mine {
                            return None;
                        }
                        scoped = true;
                    }
                    let mut own = Vec::new();
                    for (addr, delta) in entries.into_iter().flatten() {
                        match addr.split_first() {
                            Some((true, rest)) => own.push((rest.to_vec(), *delta)),
                            Some((false, [])) if *delta == Delta::Rib => {}
                            _ => return None,
                        }
                    }
                    // An element that exports what the pair says it does.
                    let elem = match (&**a, &own[..]) {
                        (_, []) => a.clone(),
                        (STy::Export(..), [(here, Delta::Rib)]) if here.is_empty() => a.clone(),
                        _ => Rc::new(STy::Export(a.clone(), Bind::Rib(own))),
                    };
                    elems.push(elem);
                }
                _ => return None,
            }
        }
        match elems.len() {
            0 => None,
            _ if !nil => None,
            1 => elems.pop().map(|e| (e, scoped)),
            _ => Some((Rc::new(STy::Union(elems)), scoped)),
        }
    }

    /// A ribcage's list, `mu` `id` of members `ms`: `(export () (cage))`,
    /// and pairs `(export (e . (import id β)) (cage (at D) β'))`, the rest
    /// in the scope of what the element binds, `β`, which is also the
    /// list's innermost rib or ribcage, `β'`, after the rest's. The element
    /// type, with what it exports.
    fn cage_seq_of(&self, t: &Rc<STy>, ms: &[Rc<STy>]) -> Option<Rc<STy>> {
        let (mut elems, mut nil) = (Vec::new(), false);
        for m in ms {
            let STy::Export(core, Bind::Cage(rings)) = &**m else { return None };
            match (&**core, &rings[..]) {
                (STy::Nil, []) => nil = true,
                (STy::Pair(a, d), [Ring::At(rest), own]) if rest == &vec![false] => {
                    let STy::Import(r, inner) = &**d else { return None };
                    if !same(r, t) {
                        return None;
                    }
                    // What the rest is in the scope of is the element's own.
                    let (same, elem) = match (own, inner) {
                        (Ring::Rib(es), Bind::Rib(fs)) => (es == fs, {
                            let es: Option<Vec<(Addr, Delta)>> = es.iter().map(|(addr, d)| addr.split_first().filter(|(h, _)| **h).map(|(_, r)| (r.to_vec(), *d))).collect();
                            Rc::new(STy::Export(a.clone(), Bind::Rib(es?)))
                        }),
                        (Ring::At(x), Bind::Cage(fs)) if x == &vec![true] => (fs[..] == [Ring::At(vec![true])], a.clone()),
                        _ => return None,
                    };
                    if !same {
                        return None;
                    }
                    elems.push(elem);
                }
                _ => return None,
            }
        }
        match (elems.len(), nil) {
            (1, true) => elems.pop(),
            _ => None,
        }
    }

    /// The type at `t`, its annotations seen through, not its `mu`s.
    fn peel<'a>(&'a self, t: &'a Rc<STy>) -> &'a Rc<STy> {
        match &**t {
            STy::Import(b, _) | STy::Export(b, _) | STy::Many(b) | STy::Typed(b, _) => self.peel(b),
            _ => t,
        }
    }

    /// Whether signature `t` binds nothing, as a template may use one of
    /// `scope-forms` (`bloblet-ref`'s, `TODO.md` §247): no `import` or
    /// `export` in it, so neither a module's item nor its names (`item`,
    /// `(shape A)`), which a program's walk alone knows; a `mu`'s body
    /// once, its variable what is around it.
    fn binds_nothing(&self, t: &STy) -> bool {
        match t {
            STy::Item | STy::Import(..) | STy::Export(..) => false,
            STy::Pair(a, d) => self.binds_nothing(a) && self.binds_nothing(d),
            STy::Many(b) | STy::Typed(b, _) | STy::Mu(b, _) => self.binds_nothing(b),
            STy::Union(ms) => ms.iter().all(|m| self.binds_nothing(m)),
            _ => true,
        }
    }

    /// The type at `t`, its annotations, `mu`s and unions seen through
    /// to what is under them (for overlap and fit).
    fn unfold(&self, t: &Rc<STy>) -> Rc<STy> {
        match &**t {
            STy::Import(b, _) | STy::Export(b, _) | STy::Many(b) | STy::Typed(b, _) => self.unfold(b),
            STy::Mu(..) => self.unfold(&unfold_mu(t)),
            _ => t.clone(),
        }
    }

    /// Whether some source syntax could be of both `a` and `b` (Herman's
    /// shapes, §5.2.3): `expr` may be anything but a form's name; looked
    /// at to `depth` pairs, past which they are taken to overlap.
    fn overlap(&self, a: &Rc<STy>, b: &Rc<STy>, depth: usize) -> bool {
        use STy::*;
        let (a, b) = (&self.unfold(a), &self.unfold(b));
        match (&**a, &**b) {
            (Union(ms), _) => ms.iter().any(|m| self.overlap(m, b, depth)),
            (_, Union(ms)) => ms.iter().any(|m| self.overlap(a, m, depth)),
            // A trailmark is itself: no expression, datum, binder or
            // other trailmark; an `id` may be any name.
            (Mark(_, x), Mark(_, y)) => x == y,
            (Mark(..), Id) | (Id, Mark(..)) => true,
            (Mark(..), _) | (_, Mark(..)) => false,
            (Literal(_), Expr | Bvar | Dvar) | (Expr | Bvar | Dvar, Literal(_)) => false,
            // A lambda is a list: no name, `()` or label, and any list.
            (Lambda, Literal(_) | Bvar | Dvar | Id | Nil | Label) | (Literal(_) | Bvar | Dvar | Id | Nil | Label, Lambda) => false,
            (Lambda, _) | (_, Lambda) => true,
            (Literal(x), Literal(y)) => x == y,
            (Literal(_), Id) | (Id, Literal(_)) => true,
            (Expr | Data | Type | Kind | Defn | Item, _) | (_, Expr | Data | Type | Kind | Defn | Item) => true,
            (Pair(a1, d1), Pair(a2, d2)) => depth == 0 || (self.overlap(a1, a2, depth - 1) && self.overlap(d1, d2, depth - 1)),
            (Nil, Nil) => true,
            (Label, Label) => true,
            (Label, _) | (_, Label) => false,
            (Bvar | Dvar | Id, Bvar | Dvar | Id) => true,
            _ => false,
        }
    }

    /// Whether `s` has the shape of `t`, in `mode`: a pattern variable in a
    /// template, or any name in a pattern, fits anything.
    fn fits(&self, t: &Rc<STy>, s: &Syn, mode: Mode, interner: &Interner, pvars: &HashMap<Sym, PInfo>) -> bool {
        self.fits_within(t, s, mode, interner, pvars, FITS_DEPTH)
    }

    /// `fits`, looking no deeper than `depth` lists: a `union`'s members
    /// differ within `OVERLAP_DEPTH` (`sty`), so that is enough to choose
    /// one, and what is chosen is aligned whole; and a long list is not
    /// looked through at each of its parts.
    fn fits_within(&self, t: &Rc<STy>, s: &Syn, mode: Mode, interner: &Interner, pvars: &HashMap<Sym, PInfo>, depth: usize) -> bool {
        // `(p ...)`, where a list of elements `p` fits may be.
        if matches!(mode, Mode::Pattern | Mode::Template) && let Some(x) = ellipsis(s, interner) {
            return self.seq_of(self.peel(t)).is_some_and(|(e, _)| self.fits_within(&e, &x, mode, interner, pvars, depth));
        }
        self.fits_shaped(t, Some(s), s.shape(), mode, interner, pvars, depth)
    }

    /// [`fits_within`](Self::fits_within) of `s`, of shape `shape`, past
    /// its ellipsis: a `union`'s members each held to the one look at it.
    /// No `s` for a `()` that is a list's end, which nothing reads past
    /// its shape.
    #[allow(clippy::too_many_arguments)]
    fn fits_shaped(&self, t: &Rc<STy>, s: Option<&Syn>, shape: Shape, mode: Mode, interner: &Interner, pvars: &HashMap<Sym, PInfo>, depth: usize) -> bool {
        use STy::*;
        if let Shape::Symbol(n) = shape {
            let lit = matches!(&*self.unfold(t), Literal(_) | Mark(..));
            // A pattern variable placed fits anything but, if it is a name,
            // a list's shape, which a name never has.
            let name = pvars.get(&n).is_some_and(|p| matches!(&*p.core, Bvar | Dvar | Id | Label));
            let list = matches!(&*self.unfold(t), Pair(..) | Nil | Lambda);
            // And a label's, never a reserved word a signature writes,
            // which no use gives it (Heist's should-work note, entry 5,
            // TODO §304): `tagcase`'s `(t x body)` of a label `t` is no
            // `(else y body)`.
            let unreserved = pvars.get(&n).is_some_and(|p| matches!(&*p.core, Label));
            let word = matches!(&*self.unfold(t), Literal(w) if reserved(interner.name(*w)));
            let mark = self.mark_of(n).is_some();
            if (mode == Mode::Pattern && !lit && !mark && interner.name(n) != "_") || (mode == Mode::Template && pvars.contains_key(&n) && !(name && list) && !(unreserved && word)) {
                return true;
            }
            // A trailmark, where a use, a pattern or a template writes one:
            // itself, a kernel's word of its name, or an `id`; never an
            // expression, a datum or a binder.
            if matches!(mode, Mode::Use | Mode::Pattern | Mode::Template)
                && let Some(m) = self.mark_of(n)
            {
                return match &*self.unfold(t) {
                    Union(ms) => ms.iter().any(|x| self.fits_shaped(x, s, shape, mode, interner, pvars, depth)),
                    Mark(_, id) => *id == m.id,
                    Literal(x) => *x == n,
                    Id => true,
                    _ => false,
                };
            }
        }
        let syn = || *s.expect("syntax where its shape is not `()`'s");
        match &*self.unfold(t) {
            Union(ms) => ms.iter().any(|m| self.fits_shaped(m, s, shape, mode, interner, pvars, depth)),
            Pair(a, d) => match shape {
                Shape::List | Shape::Dotted => {
                    let s = syn();
                    let (mut items, tail) = s.parts().expect("a list");
                    match items.next() {
                        // No parts: what its tail is.
                        None => tail.is_some_and(|x| self.fits_within(t, &x, mode, interner, pvars, depth)),
                        Some(first) => depth == 0 || (self.fits_within(a, &first, mode, interner, pvars, depth - 1) && self.fits_rest(d, items, tail, s.at(), mode, interner, pvars, depth - 1)),
                    }
                }
                _ => false,
            },
            Nil => shape == Shape::Nil,
            Literal(n) => shape.sym() == Some(*n),
            Mark(_, id) => shape.sym().and_then(|n| self.mark_of(n)).is_some_and(|m| m.id == *id),
            Bvar | Dvar => shape.sym().is_some_and(|n| mode == Mode::Program || !reserved(interner.name(n))),
            Id => shape.sym().is_some(),
            // A use's label any name but a word the kernel's forms read
            // (`literal_word`).
            Label => matches!(shape, Shape::Keyword(_)) || (matches!(mode, Mode::Use | Mode::Program) && shape.sym().is_some_and(|n| mode == Mode::Program || !self.literal_word(n))) || (mode == Mode::Program && shape == Shape::Atom && matches!(syn().view(), V::Number(_))),
            Expr => (mode == Mode::Program || !shape.sym().is_some_and(|n| reserved(interner.name(n)))) && shape != Shape::Nil,
            Lambda => shape == Shape::List && lambda_shaped(&syn(), interner),
            Defn => matches!(shape, Shape::List | Shape::Dotted),
            Data | Type | Kind | Item | Rules => true,
            Import(..) | Export(..) | Mu(..) | Many(_) | Typed(..) | Var(_) => unreachable!("unfolded, closed"),
        }
    }

    /// `fits_within` of the rest of a list, its parts `rest` and then
    /// `tail`, looked at where it is: a long list's rest is not made again
    /// at each of its parts.
    #[allow(clippy::too_many_arguments)]
    fn fits_rest(&self, t: &Rc<STy>, rest: crate::heap_syn::Items, tail: Option<Syn>, span: At, mode: Mode, interner: &Interner, pvars: &HashMap<Sym, PInfo>, depth: usize) -> bool {
        use STy::*;
        let mut after = rest;
        let Some(x) = after.next() else {
            return match tail {
                Some(t1) => self.fits_within(t, &t1, mode, interner, pvars, depth),
                None => self.fits_shaped(t, None, Shape::Nil, mode, interner, pvars, depth),
            };
        };
        // What a pattern or template writes by ellipsis, or a lambda's
        // shape, is read from the rest made whole (a template is small).
        let whole = || Syn::of_list(span, &rest.collect::<Vec<_>>(), tail);
        if matches!(mode, Mode::Pattern | Mode::Template) {
            return self.fits_within(t, &whole(), mode, interner, pvars, depth);
        }
        match &*self.unfold(t) {
            Union(ms) => ms.iter().any(|m| self.fits_rest(m, rest, tail, span, mode, interner, pvars, depth)),
            Pair(a, d) => depth == 0 || (self.fits_within(a, &x, mode, interner, pvars, depth - 1) && self.fits_rest(d, after, tail, span, mode, interner, pvars, depth - 1)),
            Nil | Literal(_) | Mark(..) | Bvar | Dvar | Id | Label => false,
            Lambda => lambda_shaped(&whole(), interner),
            Expr | Defn | Data | Type | Kind | Item | Rules => true,
            Import(..) | Export(..) | Mu(..) | Many(_) | Typed(..) | Var(_) => unreachable!("unfolded, closed"),
        }
    }

    /// Top-level form `form` begun: the names it makes fresh are `%x:K.N`,
    /// `K` its key, `N` counted from 1 within it. Its key is a hash of what
    /// was written (`syn_hash`) and, past the first form of that hash, how
    /// many came before it, `H-1`, …: no two forms' keys are one, so neither
    /// are their names, and a form's names are of it and the macros it uses
    /// alone (FX-26's `macros-fresh.fx`, alike).
    pub(crate) fn form_begin(&mut self, form: &Syn, interner: &Interner) {
        let h = syn_hash(form, interner);
        let seen = self.withs.keys_seen.entry(h).or_insert(0);
        let n = *seen;
        *seen += 1;
        let m = &self.withs.module_prefix;
        self.withs.form_key = if n == 0 { format!("{m}{h}") } else { format!("{m}{h}-{n}") };
        self.fresh = 0;
        self.withs.captors = 0;
        self.withs.expanded = 0;
        // What is kept within one form as at any form's start, whatever a
        // failure before left (FX-26's `form-begun!`, alike): the macros an
        // expansion defined, none yet; no template's check under way.
        self.withs.made_syntax.clear();
        self.checking = false;
    }

    /// The next fresh name's tag, `K.N`.
    fn fresh_tag(&mut self) -> String {
        self.fresh += 1;
        format!("{}.{}", self.withs.form_key, self.fresh)
    }

    /// Expansion `made` begun, of a macro defined where `def_env` says: its
    /// tag, `K.N`, counted apart from the fresh names' (`Withs::tags`).
    fn expansion_begun(&mut self, made: u32, def_env: hygiene::DefEnv) {
        self.withs.expanded += 1;
        let tag = format!("{}.{}", self.withs.form_key, self.withs.expanded);
        self.withs.def_envs.insert(tag.clone(), def_env);
        self.withs.tags.insert(made, tag);
    }

    /// Expansion `made`'s tag; a template's check's (`made` 0), `0`.
    pub(crate) fn tag_of(&self, made: u32) -> String {
        self.withs.tags.get(&made).cloned().unwrap_or_else(|| "0".to_string())
    }

    /// `(define-syntax name [σ] (syntax-rules [#:trailmarks (name …)] ((_ . pattern)
    /// template) …))`, its signature written or inferred; or a
    /// `define-syntax-rec` of them: checked, and defined; their names. A template's free name is the top level's
    /// where the macro is used (`Action::Toplevel`).
    pub fn define(&mut self, form: &Syn, interner: &mut Interner) -> R<Vec<Sym>> {
        let names = self.define_in(form, interner, None)?;
        for n in &names {
            self.defined_at.insert(*n, form.at());
        }
        Ok(names)
    }

    /// The checks of macro `name`'s templates, once, where it is defined
    /// (`typed-macros.md`, "Proposed: typed holes"): for each clause, if
    /// its `expr` parts are typed holes, a hidden definition of the template
    /// as a procedure over its holes, each hole a parameter called where the
    /// template places it, `(subr E (U …) T)`, given the binders of the
    /// template's in its scope; its binders' types the `bvar`s', each part
    /// left out a binder of the procedure's `plambda`. Checked as any
    /// definition is, by both checkers; none if no part is typed.
    pub fn template_checks(&mut self, name: Sym, interner: &mut Interner) -> R<Vec<Syn>> {
        // A trailmark has no templates.
        let Some(m) = self.defined.get(&name).cloned() else { return Ok(Vec::new()) };
        let mut out = Vec::new();
        for c in &m.clauses {
            if c.pvars.iter().all(|(_, p)| p.hole.is_none()) {
                continue;
            }
            out.push(self.template_check(name, &m, c, interner)?);
        }
        Ok(out)
    }

    fn template_check(&mut self, name: Sym, m: &Macro, c: &Clause, interner: &mut Interner) -> R<Syn> {
        let (template, pattern) = (c.template.get(), c.pattern.get());
        let at = template.at();
        let shown = |n: Sym, i: &Interner| i.name(n).to_string();
        let place = |n: Sym| find_symbol(&pattern, n).map_or(pattern.at(), |s| s.at());
        let sym = |s: &str, i: &mut Interner| Syn::named(at, s, i);
        let mut binders: Vec<Syn> = m.poly.iter().map(|k| k.get()).collect();
        let mut binds: HashMap<Sym, Syn> = HashMap::default();
        // Each binder, a fresh name for the holes in its scope to be given.
        for (n, p) in &c.pvars {
            match &*p.core {
                STy::Expr | STy::Lambda => {}
                STy::Bvar => {
                    let f = format!("%{}:{}", shown(*n, interner), self.fresh_tag());
                    binds.insert(*n, sym(&f, interner));
                }
                _ => {
                    return Err(FxError::at(place(*n), format!("`{}` is not an `expr`, a `lambda` or a `bvar`: a macro whose parts are typed is checked once, of those alone, not yet", shown(*n, interner))));
                }
            }
        }
        let mut params = Vec::new();
        for (n, p) in &c.pvars {
            let lambda = matches!(&*p.core, STy::Lambda);
            if !matches!(&*p.core, STy::Expr) && !lambda {
                continue;
            }
            let Some(h) = &p.hole else {
                return Err(FxError::at(place(*n), format!("`{}` has no type or effect, and another part of this macro does: a macro whose parts are typed is checked once, each `expr` and `lambda` part typed", shown(*n, interner))));
            };
            // The binders in its scope, outermost first, each a typed `bvar`.
            let mut scope = Vec::new();
            for level in p.declared.iter().rev() {
                let Level::Rib(atoms) = level else {
                    return Err(FxError::at(place(*n), format!("`{}` is in the scope of a part's ribcage: not yet where a macro's parts are typed", shown(*n, interner))));
                };
                for a in atoms.iter() {
                    let Atom::Var(b, _, _) = a else {
                        return Err(FxError::at(place(*n), format!("`{}` is in the scope of the binders a part exports: not yet where a macro's parts are typed", shown(*n, interner))));
                    };
                    let ty = c.pvars.iter().find(|(x, _)| x == b).and_then(|(_, q)| q.hole.as_ref()?.ty.map(Kept::get));
                    let Some(ty) = ty else {
                        return Err(FxError::at(place(*b), format!("`{}` binds a variable `{}` is in the scope of: its type is written, `(bvar #:type T)`, where a macro's parts are typed", shown(*b, interner), shown(*n, interner))));
                    };
                    scope.push((*b, ty));
                }
            }
            // A part left out, a binder of the procedure's, named for the
            // hole (`%type-of-e`), what a message about it says.
            let mut part = |given: &Option<Syn>, kind: &str, i: &mut Interner| match given {
                Some(s) => s.clone(),
                None => {
                    let v = Syn::named(at, &format!("%{kind}-of-{}", shown(*n, i)), i);
                    binders.push(Syn::lst(at, vec![v.clone(), Syn::named(at, kind, i)]));
                    v
                }
            };
            // A lambda's stand-in is a lambda: its procedure, given, called
            // with the lambda's arguments, of the types its type says; so
            // its type is written, `(subr E (A …) R)`, and making it does
            // nothing.
            let lambda_ty = if lambda {
                let written = h.ty.map(Kept::get).and_then(|t| match t.list().as_deref() {
                    Some([s, _, args, _]) if s.sym().is_some_and(|s| interner.name(s) == "subr") && (args.list().is_some() || matches!(args.view(), V::Nil)) => Some(t),
                    _ => None,
                });
                let Some(written) = written else {
                    return Err(FxError::at(place(*n), format!("`{}` is a `lambda` part: its type is written, `(lambda #:type (subr E (A …) R))`, which its stand-in in the check is made of", shown(*n, interner))));
                };
                Some(written)
            } else {
                None
            };
            let ty = part(&h.ty.map(Kept::get), "type", interner);
            let effect = if lambda { sym("pure", interner) } else { part(&h.effect.map(Kept::get), "effect", interner) };
            let hole = sym(&format!("%h:{}:{}", shown(*n, interner), self.fresh_tag()), interner);
            let args: Vec<Syn> = scope.iter().map(|(_, t)| t.clone()).collect();
            let subr = Syn::lst(at, vec![sym("subr", interner), effect, list_of(at, args, None), ty]);
            params.push(Syn::lst(at, vec![hole.clone(), subr]));
            let call = Syn::lst(at, std::iter::once(hole).chain(scope.iter().map(|(b, _)| binds[b].clone())).collect());
            let stand_in = match lambda_ty {
                None => call,
                Some(written) => {
                    let items = written.list().expect("a `subr`");
                    let arg_types = items[2].list().map(|l| l.to_vec()).unwrap_or_default();
                    let mut params = Vec::new();
                    let mut names = vec![call];
                    for a in arg_types {
                        let v = sym(&format!("%a:{}", self.fresh_tag()), interner);
                        params.push(Syn::lst(at, vec![v.clone(), a]));
                        names.push(v);
                    }
                    Syn::lst(at, vec![sym("lambda", interner), list_of(at, params, None), Syn::lst(at, names)])
                }
            };
            binds.insert(*n, stand_in);
        }
        self.checking = true;
        self.withs.def_envs.insert("0".to_string(), c.def_env.clone());
        let body = self.transcribe(c, &template, Path::ROOT, &binds, &mut Made::default(), &mut Vec::new(), 0, interner)?;
        self.checking = false;
        let lambda = Syn::lst(at, vec![sym("lambda", interner), list_of(at, params, None), body]);
        let made = if binders.is_empty() { lambda } else { Syn::lst(at, vec![sym("plambda", interner), Syn::lst(at, binders), lambda]) };
        let hidden = sym(&format!("%template:{}:{}", shown(name, interner), self.fresh_tag()), interner);
        Ok(Syn::lst(at, vec![sym("define", interner), hidden, made]))
    }

    /// `f` run with a module file's own macros in place of these: none but
    /// the file's, which it defines as it goes, where its items are
    /// (`hygiene::DefEnv::Within`), read from `text`; these put back after.
    /// A file sees the standard environment alone, no macro of the
    /// program's.
    pub(crate) fn in_file_scope<T>(&mut self, text: &str, prefix: String, f: impl FnOnce(&mut Macros) -> T) -> T {
        let defined = std::mem::take(&mut self.defined);
        let marks = std::mem::take(&mut self.withs.marks);
        let defined_at = std::mem::take(&mut self.defined_at);
        let def_env = std::mem::replace(&mut self.withs.def_env, hygiene::DefEnv::Within);
        let reading = self.reading.replace(std::sync::Arc::from(text));
        let phase1 = std::mem::take(&mut self.withs.phase1);
        // The file's forms' keys its own (`form_begin`); the form's put back.
        let named = (std::mem::take(&mut self.withs.form_key), self.fresh, self.withs.captors, self.withs.expanded, std::mem::take(&mut self.withs.keys_seen), std::mem::replace(&mut self.withs.module_prefix, prefix));
        let r = f(self);
        (self.withs.form_key, self.fresh, self.withs.captors, self.withs.expanded, self.withs.keys_seen, self.withs.module_prefix) = named;
        self.withs.phase1 = phase1;
        self.defined = defined;
        self.withs.marks = marks;
        self.defined_at = defined_at;
        self.withs.def_env = def_env;
        self.reading = reading;
        r
    }

    /// Where a macro defined now is defined: in a file's scope, if `file`
    /// gives one, as its importer has it; else where macros are now.
    fn def_env_of(&self, file: Option<&FileScope>) -> hygiene::DefEnv {
        match file {
            None => self.withs.def_env.clone(),
            Some(f) => hygiene::DefEnv::File { shared: f.shared, values: Rc::new(f.values.clone()), instance: f.instance, internal: Rc::new(f.internal.clone()), frame: f.frame.clone() },
        }
    }

    /// A file's macros, `file`'s entries (`FileEntry`), defined as the file
    /// means them (`FileScope`): among themselves first, by their names in
    /// it, as its templates name them, with the macros of the files it
    /// imports and those its top-level uses make (`TODO.md` §287); then
    /// each by the name the importer has it by (`%syntax:key:name`, an
    /// imported one's its own file's; of an instance, `instance`,
    /// `%syntax:key@lib:name`, its uses' keys `m{F}mm{G}m`, `G` a hash of
    /// `lib`, so that two instances' are apart: step 4 (c)), and each the
    /// file gives (not hidden,
    /// nor brought by a hidden import) that `taken` takes by its own name
    /// too: what `(import-with-syntax lib)` brings (`(only name …)`,
    /// `(except name …)`; `binding-shapes.md`, step 4). The names it gives,
    /// each with the name the importer has it by. `at`: the
    /// `import-with-syntax`.
    #[allow(clippy::too_many_arguments)]
    pub fn define_file(&mut self, file: &FileMacros, instance: Option<Sym>, is_standard: &dyn Fn(Sym) -> bool, taken: &dyn Fn(Sym) -> bool, at: At, interner: &mut Interner) -> R<Vec<(Sym, Sym)>> {
        self.ensure_kernel(interner)?;
        // The file's macros defined among themselves, by their names in it,
        // as its templates name them; a use expanded where the file's items
        // are as its importer has them.
        // Its recursive syntax types go on from the program's, which take
        // them back: the signatures refer to them by place.
        let shared = instance.unwrap_or(file.shared);
        let def_env = hygiene::DefEnv::File { shared, values: Rc::new(file.values.clone()), instance: instance.is_some(), internal: Rc::default(), frame: file.frame.clone() };
        let (key, prefix) = match instance {
            Some(lib) => (format!("{}@{}", file.key, interner.name(lib)), instance_prefix(&file.prefix, interner.name(lib))),
            None => (file.key.clone(), file.prefix.clone()),
        };
        let withs = Withs { syntax_sigs: std::mem::take(&mut self.withs.syntax_sigs), form_key: self.withs.form_key.clone(), module_prefix: prefix, def_env, world: self.withs.world.clone(), ..Withs::default() };
        let mut own = Macros { k: self.k.clone(), defined: HashMap::default(), fresh: self.fresh, reading: Some(file.text.clone()), defined_at: HashMap::default(), checking: false, withs: Box::new(withs) };
        let internal_of = |n: Sym, interner: &mut Interner| {
            let name = format!("%syntax:{key}:{}", interner.name(n));
            interner.intern(&name)
        };
        // Each name the importer has a macro of the file's by: its written
        // ones' first, which a template may name before it is defined.
        let mut internal: HashMap<Sym, Sym> = HashMap::default();
        for e in &file.entries {
            if let FileEntry::Syntax(f, _) = e {
                for (n, _) in crate::top::syntax_names(f, interner).unwrap_or_default() {
                    let i = internal_of(n, interner);
                    internal.insert(n, i);
                }
            }
        }
        // A macro of the file's, its own or brought, by the name the
        // importer has it by too, for its uses that the file's expand.
        let by_internal = |own: &mut Macros, n: Sym, i: Sym| {
            if let Some(m) = own.withs.marks.get(&n).cloned() {
                own.withs.marks.insert(i, m);
            } else if let Some(m) = own.defined.get(&n).cloned() {
                own.defined.insert(i, m);
            }
        };
        // Where a name given twice is said: the file's first macro, if any.
        let first = file.entries.iter().find_map(|e| match e {
            FileEntry::Syntax(f, _) => Some(f.at()),
            _ => None,
        });
        // Each name the file gives, with whether it is hidden.
        let mut given: Vec<(Sym, bool)> = Vec::new();
        let mut defined = || -> R<()> {
            for e in &file.entries {
                match e {
                    // The file's phase-1 forms, in force for its macros after them.
                    FileEntry::Syntax(form, _) if form.head_sym().is_some_and(|h| interner.name(h) == "begin-for-syntax") => own.for_syntax(form, interner, &crate::phase1::dir_of_key(&file.key))?,
                    FileEntry::Syntax(form, hidden) => {
                        let scope = FileScope { shared, instance: instance.is_some(), values: file.values.clone(), types: file.types.clone(), internal: internal.clone(), frame: file.frame.clone(), is_standard };
                        for n in own.define_in(form, interner, Some(&scope))? {
                            by_internal(&mut own, n, internal[&n]);
                            given.push((n, *hidden));
                        }
                    }
                    FileEntry::Import(lib, filter, hidden) => {
                        let takes = |n: Sym| filter.as_ref().is_none_or(|(only, names)| names.contains(&n) == *only);
                        for (n, i) in own.define_file(lib, None, is_standard, &takes, at, interner)? {
                            if takes(n) {
                                internal.insert(n, i);
                                given.push((n, *hidden));
                            }
                        }
                    }
                    // A use of a macro that makes definitions, which may make
                    // macros: expanded as a form of its own, of a key apart
                    // (`file_prefix`), the names it defines but macros the
                    // file's module's already.
                    FileEntry::Use(form, hidden) => {
                        let head = form.list().and_then(|l| l.first().copied()).and_then(|h| h.sym());
                        if !head.is_some_and(|h| own.defined.get(&h).is_some_and(|m| m.defn || m.procedural.is_some())) {
                            continue;
                        }
                        let saved = (own.withs.form_key.clone(), own.fresh, own.withs.captors, own.withs.expanded);
                        own.form_begin(form, interner);
                        let r = own.expand_top(form, interner);
                        let made: Vec<Sym> = own.withs.made_syntax.iter().map(|m| m.0).collect();
                        (own.withs.form_key, own.fresh, own.withs.captors, own.withs.expanded) = saved;
                        r?;
                        for n in made {
                            let i = internal_of(n, interner);
                            internal.insert(n, i);
                            by_internal(&mut own, n, i);
                            given.push((n, *hidden));
                        }
                    }
                }
            }
            Ok(())
        };
        let r = defined();
        self.withs.syntax_sigs = std::mem::take(&mut own.withs.syntax_sigs);
        self.fresh = own.fresh;
        r?;
        // What its uses' expansions' aliases are resolved by, and every
        // macro of the file's by the name the importer has it by, hidden or
        // not, which those it gives may expand to.
        self.withs.def_envs.extend(std::mem::take(&mut own.withs.def_envs));
        for (n, m) in &own.defined {
            if interner.name(*n).starts_with("%syntax:") {
                self.defined.insert(*n, m.clone());
            }
        }
        for (n, m) in &own.withs.marks {
            if interner.name(*n).starts_with("%syntax:") {
                self.withs.marks.insert(*n, m.clone());
            }
        }
        let first = first.unwrap_or(at);
        let mut out = Vec::new();
        let mut seen = HashSet::default();
        for (name, hidden) in given {
            let shown = interner.name(name).to_string();
            if !seen.insert(name) {
                return Err(FxError::at(first, format!("`{shown}` is a macro this file gives twice")));
            }
            if hidden {
                continue;
            }
            out.push((name, internal[&name]));
            if !taken(name) {
                continue;
            }
            // A trailmark of the file's: bound as its macros are.
            if let Some(m) = own.withs.marks.get(&name).cloned() {
                if self.defined.contains_key(&name) || self.withs.marks.contains_key(&name) {
                    return Err(FxError::at(first, format!("`{shown}` is defined already: a file's trailmark may not be defined again")));
                }
                self.withs.marks.insert(name, m);
                self.defined_at.insert(name, at);
                continue;
            }
            let m = own.defined[&name].clone();
            if self.defined.contains_key(&name) {
                return Err(FxError::at(first, format!("`{shown}` is a macro defined already: a file's may not be defined again")));
            }
            self.defined.insert(name, m);
            self.defined_at.insert(name, at);
        }
        Ok(out)
    }

    /// `define`, in a file's scope if `file` is given: the macros' names.
    fn define_in(&mut self, form: &Syn, interner: &mut Interner, file: Option<&FileScope>) -> R<Vec<Sym>> {
        self.ensure_kernel(interner)?;
        let ws = written(form, interner)?;
        // Each macro defined first, with its signature, so that a template
        // may use it, or another of its `define-syntax-rec`; put back as it
        // was if one is refused.
        let before: Vec<(Sym, Option<Rc<Macro>>)> = ws.iter().map(|w| (w.name, self.defined.get(&w.name).cloned())).collect();
        let r = self.define_written(&ws, interner, file);
        if r.is_err() {
            for (n, b) in before {
                match b {
                    Some(m) => self.defined.insert(n, m),
                    None => self.defined.remove(&n),
                };
            }
        }
        r
    }

    /// Each of `w`'s clauses checked against signature `sig`.
    #[allow(clippy::too_many_arguments)]
    fn clauses_fit(&self, w: &Written, sig: &Rc<STy>, defn: bool, desc: bool, poly: &[Syn], interner: &mut Interner, file: Option<&FileScope>) -> R<Vec<Clause>> {
        w.clauses.iter().map(|c| self.clause(w.name, c, sig, defn, desc, poly, &w.lits, interner, file)).collect()
    }

    /// A signature of unsigned macro `w`'s clauses' shapes whole, `(oneof
    /// σ₁ …)`, each clause's inferred alone: for when the one inferred of
    /// them together, position by position, does not fit them, the parts of
    /// one clause no longer told from another's (a literal of one where
    /// another has a datum, a part one has and another not). None for one
    /// clause, or clauses that make different things.
    fn by_clauses(&mut self, w: &Written, interner: &mut Interner) -> Option<Syn> {
        if w.clauses.len() < 2 {
            return None;
        }
        let (mut members, mut made): (Vec<Syn>, Option<Option<Sym>>) = (Vec::new(), None);
        for c in &w.clauses {
            let one = infer::Unsigned { name: w.name, lits: w.lits.clone(), clauses: vec![c.clone()], span: w.span };
            let s = self.infer(&[one], interner).ok()?.pop()?;
            let arrow = s.list().filter(|l| l.len() == 3 && l[0].sym().is_some_and(|h| interner.name(h) == ADDRESSED));
            // What it makes a word: `expr`, `defn` or `desc`.
            let (sigma, k) = match arrow.as_deref() {
                Some([_, sigma, k]) if k.sym().is_some() => (sigma.clone(), k.sym()),
                _ => return None,
            };
            if made.is_some_and(|m| m != k) {
                return None;
            }
            made = Some(k);
            members.push(sigma);
        }
        let at = w.span;
        let union = Syn::lst(at, std::iter::once(Syn::named(at, "oneof", interner)).chain(members).collect());
        let k = Syn::symbol(at, made.flatten()?, interner);
        Some(Syn::lst(at, vec![Syn::named(at, ADDRESSED, interner), union, k]))
    }

    fn define_written(&mut self, ws: &[Written], interner: &mut Interner, file: Option<&FileScope>) -> R<Vec<Sym>> {
        if let [w @ Written { procedural: Some((style, code)), .. }] = ws {
            let def_env = self.def_env_of(file);
            return self.define_procedural(w.name, *style, code, w.sig.as_ref(), def_env, interner);
        }
        if let Some(w) = ws.iter().find(|w| w.procedural.is_some()) {
            return Err(FxError::at(w.span, "a procedural macro is defined alone, by `define-syntax`"));
        }
        // A trailmark: a binding of its own, apart from the macros.
        if let [Written { name, mark: Some(said), .. }] = ws {
            // Numbered apart from fresh names, which both expanders count
            // alike.
            static MARKS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(1);
            let id = MARKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            self.defined.remove(name);
            self.withs.marks.insert(*name, Rc::new(Mark { id, said: said.clone() }));
            return Ok(vec![*name]);
        }
        // A macro's `#:trailmarks`, each bound to one where it is defined.
        for w in ws {
            if let Some(n) = w.lits.iter().find(|n| self.mark_of(**n).is_none()) {
                return Err(FxError::at(w.span, no_trailmark(interner.name(*n))));
            }
        }
        let mut sigs = Vec::new();
        for w in ws {
            let s = match &w.sig {
                Some(sig) => {
                    let s = self.signature(sig, interner)?;
                    self.defined.insert(w.name, Rc::new(Macro { sig: s.1.clone(), defn: s.2, desc: s.3, poly: s.0.iter().map(|p| Kept::new(*p)).collect(), clauses: Vec::new(), text: None, procedural: None }));
                    Some(s)
                }
                None => None,
            };
            sigs.push(s);
        }
        // The signatures not written, inferred together.
        let unsigned: Vec<infer::Unsigned> = ws.iter().filter(|w| w.sig.is_none()).map(|w| infer::Unsigned { name: w.name, lits: w.lits.clone(), clauses: w.clauses.clone(), span: w.span }).collect();
        let mut inferred = Vec::new();
        if !unsigned.is_empty() {
            let made = self.infer(&unsigned, interner)?;
            let mut made = made.into_iter();
            for (w, s) in ws.iter().zip(sigs.iter_mut()) {
                if s.is_some() {
                    continue;
                }
                let sig = made.next().expect("one each");
                let shown = shown_inferred(&sig, w, interner);
                let name = interner.name(w.name).to_string();
                let said = |e: FxError| FxError::at(e.span, refused_inferred(&name, &shown, &e.message));
                // Not a signature (a union's members not told apart): the
                // union of its clauses' shapes whole, if that is one.
                let (parsed, shown) = match self.signature(&sig, interner) {
                    Ok(p) => (p, shown),
                    Err(e) => match self.by_clauses(w, interner) {
                        Some(alt) => match self.signature(&alt, interner) {
                            Ok(p) => (p, shown_inferred(&alt, w, interner)),
                            Err(_) => return Err(said(e)),
                        },
                        None => return Err(said(e)),
                    },
                };
                self.defined.insert(w.name, Rc::new(Macro { sig: parsed.1.clone(), defn: parsed.2, desc: parsed.3, poly: Vec::new(), clauses: Vec::new(), text: None, procedural: None }));
                inferred.push((w.name, shown));
                *s = Some(parsed);
            }
        }
        let mut out = Vec::new();
        for (w, s) in ws.iter().zip(sigs) {
            let (poly, sig, defn, desc) = s.expect("each signature, written or inferred");
            if w.clauses.is_empty() {
                return Err(FxError::at(w.span, "a macro has at least one clause"));
            }
            let checked = match self.clauses_fit(w, &sig, defn, desc, &poly, interner, file) {
                Ok(checked) => (sig, defn, desc, checked),
                Err(e) => match inferred.iter().find(|(n, _)| *n == w.name) {
                    None => return Err(e),
                    // Inferred: the union of its clauses' shapes whole, if
                    // its clauses fit that, as they did not the one
                    // inferred of them together, position by position.
                    Some((_, shown)) => {
                        let said = FxError::at(e.span, refused_inferred(interner.name(w.name), shown, &e.message));
                        let Some(alt) = self.by_clauses(w, interner) else { return Err(said) };
                        let Ok((_, alt, adefn, adesc)) = self.signature(&alt, interner) else { return Err(said) };
                        let was = self.defined.insert(w.name, Rc::new(Macro { sig: alt.clone(), defn: adefn, desc: adesc, poly: Vec::new(), clauses: Vec::new(), text: None, procedural: None }));
                        match self.clauses_fit(w, &alt, adefn, adesc, &poly, interner, file) {
                            Ok(checked) => (alt, adefn, adesc, checked),
                            Err(_) => {
                                if let Some(m) = was {
                                    self.defined.insert(w.name, m);
                                }
                                return Err(said);
                            }
                        }
                    }
                },
            };
            let (sig, defn, desc, checked) = checked;
            out.push((w.name, Macro { sig, defn, desc, poly: poly.iter().map(|p| Kept::new(*p)).collect(), clauses: checked, text: self.reading.clone(), procedural: None }));
        }
        Ok(out
            .into_iter()
            .map(|(n, m)| {
                self.withs.marks.remove(&n);
                self.defined.insert(n, Rc::new(m));
                n
            })
            .collect())
    }

    /// Procedural macro `name`, its transformer `code` checked at its
    /// style's type in the transformers' session (`procedural::run`).
    fn define_procedural(&mut self, name: Sym, style: procedural::Style, code: &Syn, sig: Option<&Syn>, def_env: hygiene::DefEnv, interner: &mut Interner) -> R<Vec<Sym>> {
        // Its contract, a signature as a `syntax-rules` macro's is written:
        // an expression's or definitions', of untyped parts, yet.
        let (contract, defn) = match sig {
            None => (None, false),
            Some(written) => {
                let (poly, sig, defn, desc) = self.signature(written, interner)?;
                if desc || !poly.is_empty() {
                    return Err(FxError::at(written.at(), format!("`{}`'s contract: a procedural macro's is an expression's or definitions', of untyped parts, not yet another", interner.name(name))));
                }
                (Some(sig), defn)
            }
        };
        let text = code.written(interner);
        let phase1 = self.withs.phase1.clone();
        // A session's checker's in the expansion's namespace (`phase1.rs`),
        // where its uses call it; another's in the transformers' session.
        let defined = match self.phase1_define(style, &text, &phase1) {
            Some(d) => d,
            None => procedural::define(style, &text, &phase1).map(|_| ()),
        };
        defined.map_err(|e| FxError::at(code.at(), format!("`{}`'s transformer: {e}", interner.name(name))))?;
        let p = procedural::Procedural { style, code: text, def_env, contract: contract.is_some(), phase1 };
        let sig = contract.unwrap_or_else(|| Rc::new(STy::Expr));
        let m = Macro { sig, defn, desc: false, poly: Vec::new(), clauses: Vec::new(), text: None, procedural: Some(Rc::new(p)) };
        self.defined.insert(name, Rc::new(m));
        Ok(vec![name])
    }

    /// A signature as written: the binders of its `(poly (binder …) σ)`, the
    /// syntax type, and whether it makes definitions or a description.
    fn signature(&mut self, sig: &Syn, interner: &mut Interner) -> R<(Vec<Syn>, Rc<STy>, bool, bool)> {
        // `(poly (binder …) σ)`: the binders its typed holes may name.
        let (poly, sig) = match sig.list().as_deref() {
            Some([h, bs, body]) if h.sym().is_some_and(|h| interner.name(h) == "poly") => {
                let bs = bs.list().ok_or_else(|| FxError::at(bs.at(), "a signature's `(poly ((name kind) …) σ)`"))?;
                (bs, *body)
            }
            _ => (Vec::new(), *sig),
        };
        // `(macro σ expr)`: of what its uses make, an expression; `(macro σ
        // defn)`, definitions; `(macro σ desc)`, a description (a type, an
        // effect, a region, …). Always written (the user's, 2026-11-15:
        // what a use makes is said, as a procedure's result is).
        // `(macro σ (defn (ℓ δ) …))`:
        // definitions, a use's defining what the rib says of its parts,
        // `(macro (export σ (rho (ℓ δ) …)) defn)`, which is read the same.
        // In shapes and facts: elaborated to Herman's form, which is read.
        let sig = if contract::is_contract(&sig, interner) { contract::elaborated(&sig, interner)? } else { sig };
        say_signature_notes();
        // Herman's form, as `macro/addressed` writes it: its addresses paths.
        let addressed = sig.list().and_then(|l| l.first().and_then(|h| h.sym())).is_some_and(|h| interner.name(h) == "macro/addressed");
        let (sig, defn, desc) = match sig.list().as_deref() {
            Some([h, body, made]) if h.sym().is_some_and(|h| interner.name(h) == "macro/addressed") && made.list().is_some_and(|l| l.first().and_then(|d| d.sym()).is_some_and(|d| interner.name(d) == "defn")) => {
                let entries = made.list().expect("a list")[1..].to_vec();
                if entries.is_empty() {
                    (*body, true, false)
                } else {
                    if body.list().and_then(|l| l.first().and_then(|e| e.sym())).is_some_and(|e| interner.name(e) == "export") {
                        return Err(FxError::at(body.at(), "what a use defines is said once, in what it makes, `(defn (ℓ δ) …)`, not by an `export` around its parts too"));
                    }
                    let at = made.at();
                    let rho = Syn::lst(at, std::iter::once(Syn::named(at, "rho", interner)).chain(entries).collect());
                    (Syn::lst(at, vec![Syn::named(at, "export", interner), *body, rho]), true, false)
                }
            }
            Some([h, body, made]) if h.sym().is_some_and(|h| interner.name(h) == "macro/addressed") => match made.sym().map(|m| interner.name(m)) {
                // The old `(export σ (rho (ℓ δ) …))` with `defn`, taken out
                // (`TODO.md` §288): what it said is said in what it makes.
                Some("defn") if old_defn_export(body, interner) => return Err(FxError::at(body.at(), OLD_DEFN_EXPORT)),
                Some("defn") => (*body, true, false),
                Some("desc") => (*body, false, true),
                Some("expr") => (*body, false, false),
                _ => return Err(FxError::at(made.at(), "what a signature's uses make is `expr`, `defn`, `(defn D …)` or `desc`")),
            },
            Some([h, ..]) if h.sym().is_some_and(|h| interner.name(h) == "->") => return Err(FxError::at(sig.at(), "a macro's signature is `(macro (_ part …) made fact …)`: `->` is a procedure's type")),
            Some([h, ..]) if h.sym().is_some_and(|h| interner.name(h) == "macro") => return Err(FxError::at(sig.at(), "a signature in shapes and facts is `(macro (_ part …) made fact …)`; Herman's, `(macro/addressed σ made)`")),
            _ => return Err(FxError::at(sig.at(), "a signature is `(macro (_ part …) made fact …)`, what its uses make written: `expr`, `defn`, `(defn D …)` or `desc`")),
        };
        if addressed && let Some(a) = lettered(&sig, interner) {
            return Err(FxError::at(a.at(), format!("`{}` is an address in Herman's letters: {PATH_USAGE}", a.written(interner))));
        }
        let sig = self.sty(&sig, interner, &HashMap::default())?;
        // Each macro it says a use defines, its signature read now.
        if let STy::Export(_, Bind::Rib(es)) = &*sig {
            for (_, d) in es {
                if let Delta::Syntax(k) = d
                    && !self.withs.syntax_sigs.contains_key(k)
                {
                    let (p, t, d, e) = self.signature(&k.get(), interner)?;
                    if !p.is_empty() {
                        return Err(FxError::at(k.get().at(), "a macro's binder's signature has no `poly`, not yet"));
                    }
                    self.withs.syntax_sigs.insert(*k, (t, d, e));
                }
            }
        }
        Ok((poly, sig, defn, desc))
    }

    /// A clause checked against signature `sig` (Herman's rules): its
    /// pattern fits the signature, each of the pattern's variables is
    /// placed in the template where the signature says what is in scope
    /// there, and a reference to a pattern's binder is where no other
    /// pattern binder may shadow it.
    #[allow(clippy::too_many_arguments)]
    fn clause(&self, name: Sym, c: &Syn, sig: &Rc<STy>, defn: bool, desc: bool, poly: &[Syn], lits: &[Sym], interner: &mut Interner, file: Option<&FileScope>) -> R<Clause> {
        let usage = "a clause is `((_ . pattern) template)`";
        let parts = c.list().ok_or_else(|| FxError::at(c.at(), usage))?;
        let [pattern, template] = &parts[..] else {
            return Err(FxError::at(c.at(), usage));
        };
        let Some((_, pattern)) = split(pattern) else {
            return Err(FxError::at(pattern.at(), usage));
        };
        // The pattern, aligned with the signature: each variable's type and
        // declared environment.
        let none = HashMap::default();
        let mut p = Aligner { m: self, interner, mode: Mode::Pattern, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new(), heads: None, pending: Vec::new(), apps: None, whole: false };
        let root = p.align(sig, &pattern, None, Path::ROOT)?;
        // A `syntax-rules`' literals, each a name the signature has written
        // as it is, `(literal name)`, where the pattern has it; and no other.
        {
            for node in &p.nodes {
                let Some(n) = node.syn.sym() else { continue };
                let lit = matches!(&*node.core, STy::Literal(_) | STy::Mark(..));
                if matches!(&*node.core, STy::Mark(..)) && !lits.contains(&n) {
                    return Err(FxError::at(node.syn.at(), format!("`{}` is the trailmark the signature writes here, `(trailmark {0})`, and is not among the `syntax-rules`' `#:trailmarks`", interner.name(n))));
                }
                if !lit && matches!(node.kids, Kids::PVar(_)) && lits.contains(&n) {
                    return Err(FxError::at(node.syn.at(), format!("`{}` is among the `syntax-rules`' `#:trailmarks`, and the signature has a part here, not `(trailmark {0})`", interner.name(n))));
                }
            }
        }
        let mut found = Vec::new();
        p.walk(root, &Env::default(), false, 0, &mut found, &mut Vec::new())?;
        // What a use of a macro that makes definitions says it defines, if
        // its signature says (`(macro σ (defn (ℓ δ) …))`): what a template
        // using it sees, and what its own template is held to.
        let declared = match (defn, &p.nodes[root].export) {
            (true, Some((b, r))) => Some(exports(&p.eval(b, *r, pattern.at())?)),
            _ => None,
        };
        let mut pvars: HashMap<Sym, PInfo> = HashMap::default();
        let mut order = Vec::new();
        for (at, env, many, depth) in found {
            let Kids::PVar(n) = p.nodes[at].kids else { continue };
            order.push(n);
            if depth > 0 && p.nodes[at].hole.is_some() {
                return Err(FxError::at(p.nodes[at].syn.at(), "a typed part under an ellipsis: not yet"));
            }
            if pvars.insert(n, PInfo { core: p.nodes[at].core.clone(), declared: env.to_vec(), many, hole: p.nodes[at].hole.clone(), depth }).is_some() {
                return Err(FxError::at(p.nodes[at].syn.at(), format!("`{}` is a pattern variable twice", interner.name(n))));
            }
            // Its uses' definitions are checked where each is (the first
            // tier): a template of definitions is not checked once, yet.
            if defn && p.nodes[at].hole.is_some() {
                return Err(FxError::at(p.nodes[at].syn.at(), "a macro that makes definitions has no typed parts, not yet: what each use defines is checked where it is"));
            }
            if desc && p.nodes[at].hole.is_some() {
                return Err(FxError::at(p.nodes[at].syn.at(), "a macro that makes a description has no typed parts"));
            }
        }
        // The template, an expression or definitions, aligned with the
        // kernel's forms' signatures and the macros'.
        // Where it uses a macro whose uses define a macro, `(macro σ made)`, each
        // list whose head such an entry may bind read by its scope, to a
        // fixed point (`typed-macros.md`, "Decided: a template's heads read
        // by their scope, to a fixed point"): aligned, walked, each pending
        // head read by its binder, until no reading is new; one read twice
        // otherwise refused.
        let made = Rc::new(if defn { STy::Defn } else if desc { STy::Type } else { STy::Expr });
        let scoped = self.uses_syntax_macro(template);
        let mut heads: HashMap<u64, Head> = HashMap::default();
        let (t, root, found, seqs, read) = loop {
            let mut t = Aligner { m: self, interner, mode: Mode::Template, pvars: &pvars, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new(), heads: scoped.then_some(&heads), pending: Vec::new(), apps: None, whole: false };
            let root = t.align(&made, template, None, Path::ROOT)?;
            let (mut found, mut seqs) = (Vec::new(), Vec::new());
            t.walk(root, &Env::default(), false, 0, &mut found, &mut seqs)?;
            let read = if t.pending.is_empty() { Vec::new() } else { t.heads_read(&found)? };
            // Each macro reading kept; one an application may become a
            // macro as the macros found give scope, never the other way.
            let mut new = Vec::new();
            for (at, h, _) in &read {
                let syn = t.nodes[*at].syn;
                match heads.get(&syn.0.raw()) {
                    None if matches!(h, Head::Macro(_)) => new.push((syn.0.raw(), *h)),
                    None => {}
                    Some(was) if was != h => {
                        let n = syn.list().and_then(|l| l.first().and_then(|x| x.sym())).map(|x| t.name(x).to_string()).unwrap_or_default();
                        let said = |h: &Head| if matches!(h, Head::Macro(_)) { "a use of the macro a use before it defines" } else { "an application" };
                        return Err(FxError::at(syn.at(), format!("this template's scopes have no one reading: `{}`, headed by `{n}`, is read as {} and then as {}", t.show(&syn), said(was), said(h))));
                    }
                    Some(_) => {}
                }
            }
            if new.is_empty() {
                break (t, root, found, seqs, read);
            }
            drop(t);
            heads.extend(new);
        };
        // A pending list where a definition is, read as no macro's use: no
        // definition.
        for (at, h, _) in &read {
            if matches!(h, Head::Application) && t.pending.iter().any(|(p, d)| p == at && *d) {
                let syn = t.nodes[*at].syn;
                return Err(FxError::at(syn.at(), format!("`{}` is not a definition: a macro that makes definitions makes `define`, `define*`, `define-rec`, a `begin` of them, or a use of another such", t.show(&syn))));
            }
        }
        // How many ellipses each of the template's binders is under: a
        // binder repeated is made fresh in each repetition.
        let binder_depth: HashMap<usize, usize> = found.iter().filter(|f| matches!(t.nodes[f.0].kids, Kids::Binder(..))).map(|f| (f.0, f.3)).collect();
        // The names the template binds in its uses of macros that make
        // definitions: what their signatures do not say they define, it
        // does not see.
        let mut nested = Vec::new();
        for node in &t.nodes {
            if let Kids::Form(x) = node.kids
                && let Some(h) = node.syn.list().and_then(|l| l.first().copied()).and_then(|h| h.sym())
                && !pvars.contains_key(&h)
                && self.defined.get(&h).is_some_and(|m| m.defn)
            {
                t.binders_under(x, h, &mut nested);
            }
        }
        let mut actions = HashMap::default();
        let mut uses: HashMap<Sym, usize> = HashMap::default();
        for (at, env, many, depth) in found {
            let node = &t.nodes[at];
            let span = node.syn.at();
            match &node.kids {
                Kids::PVar(n) => {
                    let info = &pvars[n];
                    let name = interner.name(*n);
                    t.placed(*n, info, &node.core, &env.to_vec(), span)?;
                    if depth < info.depth {
                        return Err(FxError::at(span, format!("`{name}` is placed under {depth} ellipses, and the pattern has it under {}", info.depth)));
                    }
                    // Anything with an expression in it, placed twice, runs
                    // twice: placed once, unless its signature says `many`.
                    // Where another macro's says `many`, it may be placed
                    // more than once there.
                    // A typed hole of no effect, `pure`, may be placed any
                    // number of times: running it twice does nothing twice.
                    let pure = info.hole.as_ref().is_some_and(|h| h.pure(interner));
                    let affine = !info.many && !pure && !matches!(&*info.core, STy::Bvar | STy::Dvar | STy::Id | STy::Label | STy::Data | STy::Type | STy::Kind);
                    if affine && depth > info.depth {
                        return Err(FxError::at(span, format!("`{name}` is placed under more ellipses than the pattern has it, so in each repetition, and an expression in it may do something each time it runs: its signature says `(many …)` if it may")));
                    }
                    if affine && many {
                        return Err(FxError::at(span, format!("`{name}` is placed where it may be placed more than once (a `many` part), and an expression in it may do something each time it runs: its signature says `(many …)` if it may")));
                    }
                    if affine {
                        let k = uses.entry(*n).or_default();
                        *k += 1;
                        if *k > 1 {
                            return Err(FxError::at(span, format!("`{name}` is placed twice, and an expression in it may do something each time it runs: its signature says `(many …)` if it may")));
                        }
                    }
                }
                Kids::Binder(..) => {
                    actions.insert(node.path.clone(), Action::Rename(node.path.clone(), depth));
                }
                Kids::Ref(n, ns, free) => {
                    // What the template binds of this name, in its namespace.
                    let binds = |atoms: &[Atom]| {
                        atoms.iter().find_map(|a| match a {
                            Atom::Lit(b, k) if *k == *ns && matches!(t.nodes[*b].kids, Kids::Binder(m, _) if m == *n) => Some(*b),
                            _ => None,
                        })
                    };
                    let bound = env.levels().find_map(|l| match l {
                        Level::Rib(atoms) => binds(atoms).map(Some),
                        Level::Earlier(atoms) => binds(atoms).map(|_| None),
                        Level::Cage(_) | Level::Shape(_) => None,
                    });
                    // A binder of a repeated element of a ribcage's list,
                    // referred to in that element: this repetition's is not
                    // yet bound, and which before it is not said.
                    let bound = match bound {
                        Some(None) => return Err(FxError::at(span, format!("`{}` is bound by the repetitions before this one, which its name does not tell apart: a repeated part refers to no binder it repeats in its own scope", interner.name(*n)))),
                        Some(b) => b,
                        None => None,
                    };
                    // A name a nested use binds, which it is not said to
                    // define: refused, not read at the top level, which the
                    // template would seem to mean by it.
                    if bound.is_none()
                        && *ns == Ns::Value
                        && let Some((_, m)) = nested.iter().find(|(b, _)| b == n)
                    {
                        let (n, m) = (interner.name(*n), interner.name(*m));
                        return Err(FxError::at(span, format!("`{n}` is bound in a use of `{m}`, whose signature does not say its uses define it: say so (`(macro σ (defn (ℓ δ) …))`), or write `(with #%toplevel {n})` for the top level's")));
                    }
                    // A binder repeated, referred to under fewer ellipses
                    // than it is: which repetition's is not said.
                    if let Some(b) = bound
                        && binder_depth.get(&b).copied().unwrap_or(0) > depth
                    {
                        return Err(FxError::at(span, format!("`{}` is bound in each repetition of a part, and referred to under fewer ellipses than it is bound: which repetition's it is is not said", interner.name(*n))));
                    }
                    let action = match (bound, free, file) {
                        (Some(b), _, _) => Action::Rename(t.nodes[b].path.clone(), binder_depth.get(&b).copied().unwrap_or(0)),
                        (None, Free::Plain, _) => continue,
                        // A name a macro's template defined this one with,
                        // an alias already: what it names where that
                        // macro is defined, kept.
                        (None, Free::Toplevel | Free::Qualified | Free::Inner, _) if procedural::alias_base(interner.name(*n)).is_some() => continue,
                        (None, Free::Inner, _) => Action::Alias,
                        (None, Free::Bound, _) => {
                            return Err(FxError::at(span, format!("`{}`, the module a template's `(with module name)` takes from, is bound by the template or given by a use: a top level's, not yet", interner.name(*n))));
                        }
                        (None, Free::Qualified, None) => Action::Alias,
                        // A file's macro's description names each type it
                        // writes free as the file has it: through the file's
                        // module, of a type it shows, or the standard
                        // environment, `(select #%fx t)`, which is all a
                        // file sees; one name at a time, as a top level's
                        // are qualified, so that the template's own binders
                        // and a use's parts in it are left as they are.
                        (None, Free::Qualified, Some(f)) if f.types.contains(n) && f.instance => Action::InstanceType(f.shared),
                        (None, Free::Qualified, Some(f)) if f.types.contains(n) => Action::ModuleType(f.shared),
                        (None, Free::Qualified, Some(f)) if frame_holds_desc(&f.frame, *n) => Action::FrameType(f.shared, f.frame.as_ref().map(|r| r.name).expect("a frame"), f.instance),
                        (None, Free::Qualified, Some(_)) => Action::StandardType,
                        (None, Free::Toplevel, None) => Action::Alias,
                        (None, Free::Toplevel, Some(f)) if f.values.contains(n) || frame_holds(&f.frame, *n) || (f.is_standard)(*n) => Action::Alias,
                        (None, Free::Toplevel, Some(_)) => {
                            return Err(FxError::at(
                                span,
                                format!("`{}` is neither a value the file defines nor a standard binding: a file's macro names only those, as they are where it is imported", interner.name(*n)),
                            ));
                        }
                    };
                    actions.insert(node.path.clone(), action);
                }
                _ => {}
            }
        }
        // Each part a template repeats says how many times: a pattern
        // variable in it that the pattern has under as many ellipses, or a
        // reference to a binder of the template's repeated as deep, as many
        // times as that binder was.
        for (r, depth) in seqs {
            let says = |k: &usize| match t.nodes[*k].kids {
                Kids::PVar(n) => pvars[&n].depth >= depth,
                Kids::Ref(..) => matches!(actions.get(&t.nodes[*k].path), Some(Action::Rename(_, d)) if *d >= depth),
                _ => false,
            };
            if !t.under(r).iter().any(says) {
                return Err(FxError::at(t.nodes[r].syn.at(), "`...` follows a part with no pattern variable in it under as many ellipses in the pattern, nor a binder repeated as deep, to say how many times"));
            }
        }
        // What the template defines of what its uses give, what its
        // signature says.
        if let Some(declared) = declared {
            let made = exports(&t.levels_of(root, template.at())?);
            if made != declared {
                return Err(FxError::at(template.at(), format!("this template defines {}, and its signature says its uses define {}", shown_exports(&made, interner), shown_exports(&declared, interner))));
            }
        }
        let mut checked_uses = HashSet::default();
        // A list read as a use of the macro a nested use defines: checked,
        // by its signature, which the defined macro is held to; its head, a
        // template's binder, renamed with it.
        for (at, h, b) in &read {
            if let Head::Macro(_) = h {
                checked_uses.insert(t.nodes[*at].syn.at().start);
                if let Some(b) = b {
                    let head = t.nodes[*at].path.push(true);
                    actions.insert(head, Action::Rename(t.nodes[*b].path.clone(), binder_depth.get(b).copied().unwrap_or(0)));
                }
            }
        }
        for node in t.nodes.iter() {
            // A use of a macro, its operands aligned with its signature: a
            // checked use (`Clause::checked_uses`).
            if let Kids::Form(_) = &node.kids
                && let Some(h) = split(&node.syn).and_then(|(h, _)| h.sym())
                && !pvars.contains_key(&h)
                && self.defined.get(&h).is_some_and(|m| m.procedural.is_none() && !m.desc)
            {
                checked_uses.insert(node.syn.at().start);
            }
            // A trailmark of the file's the template writes: by the name the
            // importer has it by.
            if let (Some(f), STy::Mark(..) | STy::Rules) = (file, &*node.core)
                && let Some(n) = node.syn.sym()
                && let Some(i) = f.internal.get(&n)
            {
                actions.insert(node.path.clone(), Action::Mark(*i));
            }
            // A use of another of the file's macros: that macro, by the
            // name the importer has it by.
            if let (Some(f), Kids::Form(_)) = (file, &node.kids)
                && let Some(h) = node.syn.list().and_then(|l| l.first().copied()).and_then(|h| h.sym())
                && let Some(i) = f.internal.get(&h)
            {
                actions.insert(node.path.clone(), Action::MacroHead(*i));
            }
        }
        // The macro's own uses in its template, which it is not yet defined
        // to meet as one: each tried with its own signature, apart, the
        // template's variables as theirs; checked if it fits, else left to
        // be aligned as it is expanded, so that no definition is refused
        // for it (`typed-macros.md`, "Decided: a use a template made is not
        // aligned again").
        for node in t.nodes.iter() {
            if let Kids::Form(_) = &node.kids
                && let Some((h, operands)) = split(&node.syn)
                && h.sym() == Some(name)
                && !pvars.contains_key(&name)
            {
                let mut a = Aligner { m: self, interner, mode: Mode::Template, pvars: &pvars, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new(), heads: None, pending: Vec::new(), apps: None, whole: false };
                if a.align(sig, &operands, None, Path::ROOT).is_ok() {
                    checked_uses.insert(node.syn.at().start);
                }
            }
        }
        // Each typed hole's contract, its type read as a use reads the
        // template's types; none where it names the macro's own binders.
        let binders: Vec<Sym> = poly.iter().filter_map(|b| b.list()?.first()?.sym()).collect();
        let mut contracts = HashMap::default();
        for (n, info) in &pvars {
            let Some(ty) = info.hole.as_ref().and_then(|h| h.ty.map(Kept::get)) else { continue };
            if !matches!(&*info.core, STy::Expr) || names_one_of(&ty, &binders) {
                continue;
            }
            let module = match file {
                None => interner.intern("#%toplevel"),
                Some(f) => match ty.sym() {
                    Some(n) if !f.types.contains(&n) => interner.intern("#%fx"),
                    _ => f.shared,
                },
            };
            let select = interner.intern("select");
            contracts.insert(*n, Kept::new(Syn::lst(ty.at(), vec![Syn::symbol(ty.at(), select, interner), Syn::symbol(ty.at(), module, interner), ty])));
        }
        let pvars: Vec<(Sym, PInfo)> = order.into_iter().map(|n| (n, pvars[&n].clone())).collect();
        let names = pvars.iter().filter(|(_, p)| matches!(&*p.core, STy::Bvar | STy::Dvar | STy::Id)).map(|(n, _)| *n).collect();
        let def_env = self.def_env_of(file);
        // A typed hole's contract is its type as the top level or the
        // file's module reads it, by a qualifier: none names a file's own
        // items, which a binder at the use could capture.
        if matches!(def_env, hygiene::DefEnv::Within) && let Some(n) = contracts.keys().next() {
            return Err(FxError::at(c.at(), format!("`{}`: a typed hole in a macro a file uses itself, not yet", interner.name(*n))));
        }
        let marks = lits.iter().filter_map(|n| Some((*n, self.mark_of(*n)?.id))).collect();
        Ok(Clause { pattern: Kept::new(pattern), names, marks, template: Kept::new(*template), actions, pvars, contracts, def_env, checked_uses })
    }

    /// `form` with each use of a macro in it expanded, as each expands,
    /// until none is left; quoted data left as it is.
    pub fn expand(&mut self, form: &Syn, interner: &mut Interner) -> R<Syn> {
        if self.defined.is_empty() && !names_path(form, interner) {
            return Ok(form.clone());
        }
        let (uses, depth, recheck, contracts) = limits(form)?;
        (self.withs.limits, self.withs.recheck, self.withs.contracts) = ((uses, depth), recheck, contracts);
        self.withs.trusted.clear();
        let mut budget = self.withs.limits.0;
        self.withs.chain.clear();
        let out = self.expand_in(form, interner, &mut budget, &mut Vec::new())?;
        // A form of the program's is the text written for it, what a use
        // made of it or not: the REPL takes the entry's text by it.
        Ok(out.placed(form.at()))
    }

    /// Top-level form `form` expanded: a use of a macro that makes
    /// definitions, the definitions it makes, in order, a `begin` of them
    /// spliced (as R7RS's at the top level); each at `form`'s place, as
    /// `expand`'s, as a top-level `include`'s forms are. Else `expand`'s.
    pub fn expand_top(&mut self, form: &Syn, interner: &mut Interner) -> R<Vec<Syn>> {
        // A procedural macro may make definitions too, which no signature
        // says ahead.
        let makes = form.list().and_then(|l| l.first().copied()).and_then(|h| h.sym()).is_some_and(|h| self.defined.get(&h).is_some_and(|m| m.defn || m.procedural.is_some()));
        if !makes {
            return Ok(vec![self.expand(form, interner)?]);
        }
        let mut out = Vec::new();
        let (uses, depth, recheck, contracts) = limits(form)?;
        (self.withs.limits, self.withs.recheck, self.withs.contracts) = ((uses, depth), recheck, contracts);
        self.withs.trusted.clear();
        self.withs.chain.clear();
        self.withs.made_syntax.clear();
        self.expand_defn(form, interner, &mut { self.withs.limits.0 }, &mut out)?;
        // A macro it defined is defined where the use is, as a program
        // expanded before it is checked holds its names to the globals
        // (`defined_before`); its templates' checks after the definitions,
        // each expanded as a form of its own.
        let made: Vec<Sym> = self.withs.made_syntax.iter().map(|m| m.0).collect();
        for n in made {
            self.defined_at.insert(n, form.at());
            for t in self.template_checks(n, interner)? {
                let e = self.expand(&t, interner)?;
                out.push(self.aliases_resolved(&e, interner)?);
            }
        }
        Ok(out.into_iter().map(|f| f.placed(form.at())).collect())
    }

    /// A use of `h`, `s`, about to be expanded, entered in the chain of uses
    /// its expansion is inside (`Withs::chain`); refused where a limit is
    /// reached, the expansions' fuel spent or their depth, saying why
    /// (`limit_error`). Nothing more is looked at here, so that a use costs
    /// what its own expansion does (`TODO.md` §231).
    fn enter(&mut self, h: Sym, s: &Syn, budget: &mut usize, interner: &Interner) -> R<()> {
        let (max_uses, max_depth) = self.withs.limits;
        let last = |chain: &[(Sym, Syn, Option<usize>)]| {
            let inside: Vec<String> = chain.iter().rev().take(4).map(|(n, ..)| format!("`{}`", interner.name(*n))).collect();
            if inside.is_empty() { String::new() } else { format!(", inside {}", inside.join(", ")) }
        };
        if *budget == 0 {
            let why = format!("this macro's expansion does not end: {max_uses} uses expanded in one form, the last of `{}`{}", interner.name(h), last(&self.withs.chain));
            return Err(self.limit_error(h, s, why, interner));
        }
        *budget -= 1;
        if self.withs.chain.len() == max_depth {
            let why = format!("this macro's expansion does not end: its uses are {max_depth} deep, each in the expansion of the one before, the last of `{}`{}", interner.name(h), last(&self.withs.chain));
            return Err(self.limit_error(h, s, why, interner));
        }
        self.withs.chain.push((h, s.clone(), None));
        Ok(())
    }

    /// Why a limit was reached at use `s` of `h`, `why` unless the chain
    /// says better: its first use (outermost first, `s` last) that is,
    /// part by part, one of the same macro it is inside, which expansion,
    /// deterministic (a transformer pure), would come back to forever:
    /// "this use of `m` is one it was expanded from, unchanged[, through
    /// …]", at that use, the one an eager check would have refused. Looked
    /// for only here, on the way to an error, so that no use's expansion
    /// pays for it: a form's parts counted (each once, kept in the chain)
    /// only where one of its macro is around it, and compared only with one
    /// as large.
    fn limit_error(&mut self, h: Sym, s: &Syn, why: String, interner: &Interner) -> FxError {
        let n = self.withs.chain.len();
        let mut sizes: Vec<Option<usize>> = self.withs.chain.iter().map(|e| e.2).collect();
        sizes.push(None);
        let entry = |chain: &[(Sym, Syn, Option<usize>)], i: usize| if i == n { (h, s.clone()) } else { (chain[i].0, chain[i].1.clone()) };
        for i in 1..=n {
            let (hi, si) = entry(&self.withs.chain, i);
            if !self.withs.chain[..i].iter().any(|(m, ..)| *m == hi) {
                continue;
            }
            let mine = *sizes[i].get_or_insert_with(|| syn_size(&si));
            for j in (0..i).rev() {
                let (hj, sj) = entry(&self.withs.chain, j);
                if hj != hi || *sizes[j].get_or_insert_with(|| syn_size(&sj)) != mine || !same_syntax(&sj, &si) {
                    continue;
                }
                let mut through: Vec<Sym> = Vec::new();
                for (m, ..) in &self.withs.chain[j + 1..i] {
                    if !through.contains(m) {
                        through.push(*m);
                    }
                }
                let through = if through.is_empty() { String::new() } else { format!(", through {}", through.iter().map(|m| format!("`{}`", interner.name(*m))).collect::<Vec<_>>().join(", ")) };
                return FxError::at(si.at(), format!("this use of `{}` is one it was expanded from, unchanged{through}: its expansion would never end", interner.name(hi)));
            }
        }
        FxError::at(s.at(), why)
    }

    /// `s`, where a definition is: a use of a macro that makes definitions,
    /// what it makes; a `begin`, each of its; a definition, as `expand_in`
    /// expands it. Each definition pushed on `out`.
    fn expand_defn(&mut self, s: &Syn, interner: &mut Interner, budget: &mut usize, out: &mut Vec<Syn>) -> R<()> {
        let items = s.list().unwrap_or_default();
        let head = items.first().and_then(|h| h.sym());
        if let Some(h) = head
            && let Some(m) = self.defined.get(&h).cloned()
        {
            self.enter(h, s, budget, interner)?;
            let from = self.withs.made_syntax.len();
            let made = self.expand_use(h, &m, s, interner)?;
            let r = self.expand_defn(&made, interner, budget, out).and_then(|()| self.syntax_held(h, &m, s, from, interner));
            self.withs.chain.pop();
            return r;
        }
        if head.is_some_and(|h| interner.name(h) == "begin") {
            for d in &items[1..] {
                self.expand_defn(d, interner, budget, out)?;
            }
            return Ok(());
        }
        // A macro an expansion defines: defined now, for what comes after;
        // its names noted, for its templates' checks after the form's
        // definitions (`expand_top`) and for the driver to hold to the
        // globals (`Withs::made_syntax`).
        if head.is_some_and(|h| matches!(interner.name(h), "define-syntax" | "define-syntax-rec")) {
            let before: Vec<(Sym, Option<Rc<Macro>>)> = crate::top::syntax_names(s, interner).unwrap_or_default().into_iter().map(|(n, _)| (n, self.defined.get(&n).cloned())).collect();
            for n in self.define(s, interner)? {
                let was = before.iter().find(|(b, _)| *b == n).and_then(|(_, m)| m.clone());
                self.withs.made_syntax.push((n, s.at(), was));
            }
            return Ok(());
        }
        out.push(self.expand_in(s, interner, budget, &mut Vec::new())?);
        Ok(())
    }

    /// Whether template `s` uses a macro whose signature says its uses
    /// define a macro, `(ℓ (macro σ made))`.
    fn uses_syntax_macro(&self, s: &Syn) -> bool {
        let Some(items) = s.list() else { return false };
        let defines = items.first().and_then(|h| h.sym()).and_then(|h| self.defined.get(&h)).is_some_and(|m| matches!(&*m.sig, STy::Export(_, Bind::Rib(es)) if es.iter().any(|e| matches!(e.1, Delta::Syntax(_)))));
        defines || items.iter().any(|x| self.uses_syntax_macro(x))
    }

    /// Use `s` of macro `name`, `m`, its expansion done: each macro its
    /// signature says a use defines, `(ℓ (macro σ made))` in what it makes,
    /// defined by the expansion (`Withs::made_syntax` from `from` on), and
    /// of signature `σ`, so that what is said of its uses ahead holds.
    fn syntax_held(&mut self, name: Sym, m: &Macro, s: &Syn, from: usize, interner: &mut Interner) -> R<()> {
        let STy::Export(_, Bind::Rib(es)) = &*m.sig else { return Ok(()) };
        let (_, operands) = split(s).expect("a list");
        for (addr, d) in es {
            let Delta::Syntax(k) = d else { continue };
            let said = k.get();
            let shown = said.written(interner);
            let user = interner.name(name).to_string();
            let refused = |why: String| FxError::at(s.at(), format!("a use of `{user}`: {why}"));
            let part = addr.iter().try_fold(operands, |x, car| split(&x).map(|(a, d)| if *car { a } else { d }));
            let Some(n) = part.and_then(|p| p.sym()) else {
                return Err(refused(format!("its signature says a macro of `{shown}` is defined at a part that is not a name")));
            };
            let x = interner.name(n).to_string();
            if !self.withs.made_syntax[from..].iter().any(|d| d.0 == n) {
                return Err(refused(format!("its signature says it defines `{x}`, a macro of `{shown}`, and its expansion does not")));
            }
            let (poly, want, defn, desc) = self.signature(&said, interner)?;
            let have = self.defined[&n].clone();
            let opaque = have.procedural.as_ref().is_some_and(|p| !p.contract);
            let same = !opaque && poly.is_empty() && have.poly.is_empty() && have.defn == defn && have.desc == desc && self.sub(&have.sig, &want, &mut Vec::new()) && self.sub(&want, &have.sig, &mut Vec::new());
            if !same {
                return Err(refused(format!("its signature says `{x}` is a macro of `{shown}`, and its expansion defines one of another signature")));
            }
        }
        Ok(())
    }

    /// The macros a refused form's expansion defined, undone: each name what
    /// it was before.
    pub(crate) fn made_undone(&mut self, made: Vec<MadeSyntax>) {
        for (n, _, was) in made.into_iter().rev() {
            match was {
                Some(m) => self.defined.insert(n, m),
                None => self.defined.remove(&n),
            };
        }
    }

    /// Form `s`, a program's item, expanded; `withs`: the places of the
    /// `with` forms whose bodies `s` is in.
    fn expand_in(&mut self, s: &Syn, interner: &mut Interner, budget: &mut usize, withs: &mut Vec<At>) -> R<Syn> {
        self.expand_region(s, &Rc::new(STy::Item), &Rc::new(HashSet::default()), interner, budget, withs)
    }

    /// `s`, of signature `core`, expanded: each use of a macro in it, as
    /// its walk finds them, expanded, and what that makes in its turn,
    /// each where it is, in what is bound around it (`TODO.md` §295). A
    /// list a macro's name heads is no use where a binder around it binds
    /// the name (a `let`'s, a `lambda`'s, a use's whose signature says
    /// so), the program wrote the head, and it is no description's: an
    /// application, as R7RS and Herman's have it. `bound`: the macros'
    /// names bound around `s` by what is around it. A head a template
    /// wrote is the macro, whatever is bound at the use (hygiene); a
    /// template's own binders are fresh names, which bind no macro's.
    fn expand_region(&mut self, s: &Syn, core: &Rc<STy>, bound: &Rc<HashSet<Sym>>, interner: &mut Interner, budget: &mut usize, withs: &mut Vec<At>) -> R<Syn> {
        let uses = if self.names_macro(s, interner) || names_path(s, interner) { self.uses_found(s, core, bound, interner)? } else { HashMap::default() };
        self.expand_at(s, Path::ROOT, &uses, interner, budget, withs)
    }

    /// Whether a macro's name is written in `s`, outside a quoted datum.
    fn names_macro(&self, s: &Syn, interner: &Interner) -> bool {
        match &s.view() {
            V::Symbol(n) => self.defined.contains_key(n),
            V::List { items, tail } => {
                !items[0].sym().is_some_and(|h| interner.name(h) == "quote")
                    && (items.iter().any(|i| self.names_macro(i, interner)) || tail.as_ref().is_some_and(|t| self.names_macro(t, interner)))
            }
            _ => false,
        }
    }

    /// The uses of macros in `s`, of signature `core`, `bound` the macros'
    /// names bound around it: each by its path, with the macros' names
    /// bound around it, as the walk of `s` finds them, each use whole
    /// (`Aligner::program`).
    fn uses_found(&mut self, s: &Syn, core: &Rc<STy>, bound: &Rc<HashSet<Sym>>, interner: &mut Interner) -> R<HashMap<Path, Part>> {
        self.ensure_kernel(interner)?;
        let none = HashMap::default();
        let (a, _, _, read) = Aligner::program(self, interner, &none, core, s, true, bound)?;
        let apps = a.apps.as_ref().expect("read by scope");
        let mut out: HashMap<Path, Part> = read
            .into_iter()
            .filter(|(at, _)| !apps.contains(&a.nodes[*at].path))
            .map(|(at, here)| {
                let names = if here.is_empty() { bound.clone() } else { Rc::new(bound.iter().copied().chain(here).collect()) };
                (a.nodes[at].path, Part::Use(names))
            })
            .collect();
        // Each path, `a::b::c`, where a value or a description is named
        // (`TODO.md` §296); none where a name is bound.
        for node in &a.nodes {
            match node.kids {
                Kids::Ref(n, ns, _) if path_named(a.name(n)) => _ = out.insert(node.path, Part::Path(ns)),
                Kids::Binder(n, _) if path_named(a.name(n)) => {
                    return Err(FxError::at(node.syn.at(), format!("`{}` is a path, `module::name`, not a name that may be bound", a.name(n))));
                }
                _ => {}
            }
        }
        Ok(out)
    }

    /// Path `s`, `a::b::c`, named `n`, where a value is (`ns`, a value's) or
    /// a description: `(with (with a b) c)`, or `(select (with a b) c)`
    /// (`TODO.md` §296), each `with` at the part of `s` it reads and noted,
    /// for the checkers to refuse if its module gives no value of its name,
    /// as a template's (`Withs::projections`): each name of a path is of
    /// the module before it, never one bound around it.
    fn path_written(&mut self, s: &Syn, n: Sym, ns: Ns, interner: &mut Interner) -> R<Syn> {
        let name = interner.name(n).to_string();
        let parts: Vec<&str> = name.split("::").collect();
        if parts.iter().any(|p| p.is_empty()) {
            return Err(FxError::at(s.at(), format!("`{name}` is not a path: a path is names joined by `::`, `module::name`")));
        }
        let at = s.at();
        // The place of the path's first `k` characters, and from `k` on.
        let upto = |k: usize| At { end: at.start + k as i64, ..at };
        let from = |k: usize| At { start: at.start + k as i64, ..at };
        let mut out = Syn::named(upto(parts[0].chars().count()), parts[0], interner);
        let mut len = parts[0].chars().count();
        for (k, p) in parts[1..].iter().enumerate() {
            let last = k + 2 == parts.len();
            let start = len + 2;
            len = start + p.chars().count();
            let x = Syn::named(At { end: at.start + len as i64, ..from(start) }, p, interner);
            if last && ns == Ns::Desc {
                out = Syn::lst(upto(len), vec![Syn::named(upto(len), "select", interner), out, x]);
                break;
            }
            let whole: String = name.chars().take(len).collect();
            let f = Syn::lst(upto(len), vec![Syn::named(upto(len), "with", interner), out, x]);
            self.withs.projections.insert(f.span(), (interner.intern(&whole), x.span(), true));
            out = f;
        }
        Ok(out)
    }

    /// `s`, at `path` in what `uses_found` read: each use there expanded,
    /// and what it makes, in what is bound around it.
    fn expand_at(&mut self, s: &Syn, path: Path, uses: &HashMap<Path, Part>, interner: &mut Interner, budget: &mut usize, withs: &mut Vec<At>) -> R<Syn> {
        if let (V::Symbol(n), Some(Part::Path(ns))) = (s.view(), uses.get(&path)) {
            return self.path_written(s, n, *ns, interner);
        }
        let V::List { items, tail } = &s.view() else { return Ok(s.clone()) };
        let head = items[0].sym();
        if head.is_some_and(|h| interner.name(h) == "quote") {
            return Ok(s.clone());
        }
        if let Some(Part::Use(bound)) = uses.get(&path) {
            let h = head.expect("a macro's name");
            let m = self.defined[&h].clone();
            if m.defn {
                return Err(FxError::at(s.at(), format!("`{}` makes definitions, which are made at the top level, not where an expression is", interner.name(h))));
            }
            self.enter(h, s, budget, interner)?;
            // A name the program wrote (a template's is the macro, by
            // hygiene), in a `with`'s body.
            if items[0].at().expansion == 0 {
                for w in withs.iter() {
                    self.withs.with_uses.entry(w.span()).or_default().push((h, items[0].span()));
                }
            }
            let core = Rc::new(if m.desc { STy::Type } else { STy::Expr });
            let out = self.expand_use(h, &m, s, interner).and_then(|out| self.expand_region(&out, &core, bound, interner, budget, withs));
            self.withs.chain.pop();
            return out;
        }
        // A template's `(with m name)`: `m`'s `name`, or refused.
        if let (Some(h), None, [_, m, n]) = (head, tail, &items[..])
            && interner.name(h) == "with"
            && items[0].at().expansion != 0
            && let (Some(m), Some(x)) = (m.sym(), n.sym())
            && !matches!(interner.name(m), "#%fx" | "#%toplevel")
        {
            self.withs.projections.insert(s.span(), (x, n.span(), false));
        }
        // A definition of a macro's name: refused, as a form's is.
        if let (Some(h), Some(n)) = (head, items.get(1).and_then(|n| n.sym()))
            && matches!(interner.name(h), "define" | "define*")
            && self.defined.contains_key(&n)
        {
            return Err(FxError::at(items[1].at(), format!("`{}` is a macro's name, which is not defined again", interner.name(n))));
        }
        // `(with m body …)`: its body in it.
        let with = head.is_some_and(|h| interner.name(h) == "with");
        let mut out = Vec::new();
        // Each item's path, the car of the cdrs before it.
        let mut rest = path;
        for (k, i) in items.iter().enumerate() {
            let inside = with && k >= 2;
            if inside {
                withs.push(s.at());
            }
            let r = self.expand_at(i, rest.push(true), uses, interner, budget, withs);
            if inside {
                withs.pop();
            }
            out.push(r?);
            rest = rest.push(false);
        }
        let tail = match tail {
            Some(t) => Some(self.expand_at(t, rest, uses, interner, budget, withs)?),
            None => None,
        };
        Ok(Syn::of_list(s.at(), &out, tail))
    }

    /// Form `form`, a program's after expansion, each local value binder
    /// renamed, and each reference to it, as a program's walk finds their
    /// scopes (`binding-shapes.md`, step 1): the same program, if the
    /// kernel's binding structure is the checkers'. A definition's name is
    /// kept, and so is every binder of a name a reference reaches only past
    /// what a `with` or `include` binds, which the walk does not know yet.
    pub fn alpha_renamed(&mut self, form: &Syn, interner: &mut Interner) -> R<Syn> {
        self.ensure_kernel(interner)?;
        let none = HashMap::default();
        let mut renamed: HashMap<Path, String> = HashMap::default();
        {
            let (a, _, found, _) = Aligner::program(self, interner, &none, &Rc::new(STy::Item), form, false, &HashSet::default())?;
            // The names definitions give, which other forms see.
            let mut defined = HashSet::default();
            for node in &a.nodes {
                if let (STy::Item | STy::Defn, Kids::Form(x)) = (&*node.core, &node.kids)
                    && let Some((b, r)) = &a.nodes[*x].export
                {
                    for level in a.eval(b, *r, node.syn.at())? {
                        if let Level::Rib(atoms) = level {
                            defined.extend(atoms.iter().filter_map(|x| if let Atom::Lit(t, _) = x { Some(*t) } else { None }));
                        }
                    }
                }
            }
            // Each reference's binder, innermost first; a name looked for
            // past a module's names, kept.
            let mut target: HashMap<usize, usize> = HashMap::default();
            let mut kept: HashSet<Sym> = HashSet::default();
            for (at, env, _, _) in &found {
                let Kids::Ref(n, Ns::Value, _) = a.nodes[*at].kids else { continue };
                for level in env.levels() {
                    match level {
                        Level::Rib(atoms) | Level::Earlier(atoms) => {
                            let b = atoms.iter().find_map(|x| match x {
                                Atom::Lit(b, Ns::Value) if matches!(a.nodes[*b].kids, Kids::Binder(m, _) if m == n) => Some(*b),
                                _ => None,
                            });
                            if let Some(b) = b {
                                target.insert(*at, b);
                                break;
                            }
                        }
                        Level::Shape(_) => {
                            kept.insert(n);
                            break;
                        }
                        Level::Cage(_) => {}
                    }
                }
            }
            kept.extend(a.unplaced.iter().copied());
            // Numbered in the order the binders are written, a list's
            // first part before its rest, as the FX-26 walk numbers them
            // (`macros-walk.fx`'s `walked-forms`).
            let mut binders: Vec<usize> = (0..a.nodes.len())
                .filter(|t| matches!(a.nodes[*t].kids, Kids::Binder(n, Ns::Value) if !defined.contains(t) && !kept.contains(&n)))
                .collect();
            sort_by_path(&mut binders, |t| a.nodes[t].path, form);
            binders.dedup_by(|x, y| a.nodes[*x].path == a.nodes[*y].path);
            for (k, t) in binders.into_iter().enumerate() {
                let Kids::Binder(n, _) = a.nodes[t].kids else { unreachable!("a binder") };
                renamed.insert(a.nodes[t].path, format!("{}%{}", a.name(n), k + 1));
            }
            for (at, b) in &target {
                if let Some(name) = renamed.get(&a.nodes[*b].path).cloned() {
                    renamed.insert(a.nodes[*at].path, name);
                }
            }
        }
        Ok(rename_paths(form, Path::ROOT, &renamed, interner))
    }

    /// A use of macro `name`, parsed by its signature, then the first clause
    /// whose pattern matches it transcribed.
    fn expand_use(&mut self, name: Sym, m: &Macro, s: &Syn, interner: &mut Interner) -> R<Syn> {
        if let Some(p) = &m.procedural {
            if p.contract {
                return self.contract_expanded(name, &m.sig, m.defn, p, s, interner);
            }
            return self.expand_procedural(name, p, s, interner);
        }
        let (_, operands) = split(s).expect("a list");
        // A use a template made where its definition aligned one fits by
        // that alignment (`typed-macros.md`, "Decided: a use a template made
        // is not aligned again"); aligned again only if asked, and then a
        // refusal is the binding-shape check's fault.
        let trusted = self.withs.trusted.contains(&s.at());
        if !trusted || self.withs.recheck {
            let none = HashMap::default();
            let mut u = Aligner { m: self, interner, mode: Mode::Use, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new(), heads: None, pending: Vec::new(), apps: None, whole: false };
            let fault = if trusted { " (a use a template made, which its macro's definition found fits: a fault in the binding-shape check, not in the program)" } else { "" };
            u.align(&m.sig, &operands, None, Path::ROOT).map_err(|e| FxError::at(e.span, format!("a use of `{}`: {}{fault}", interner.name(name), e.message)))?;
        }
        for c in &m.clauses {
            let mut binds = HashMap::default();
            let mark_of = |n: Sym| self.mark_of(n).map(|m| m.id);
            if !matches(&c.pattern.get(), &operands, &(&c.names, &c.marks, &mark_of), &mut binds, interner) {
                continue;
            }
            // Of a clause checked once (`template_checks`): its promise kept.
            let typed = c.pvars.iter().any(|(_, p)| p.hole.is_some());
            let made = fixpt_read::record_expansion(interner.name(name), s.span(), m.text.clone(), typed);
            self.expansion_begun(made, c.def_env.clone());
            return self
                .transcribe(c, &c.template.get(), Path::ROOT, &binds, &mut Made::default(), &mut Vec::new(), made, interner)
                .map_err(|e| FxError::at(s.at(), format!("a use of `{}`: {}", interner.name(name), e.message)));
        }
        Err(FxError::at(s.at(), format!("a use of `{}` that no clause of it matches", interner.name(name))))
    }

    /// A use of procedural macro `name`, `s`: its transformer run on it
    /// (`procedural::run`), what it gave read back at the use's place, a
    /// syntactic closure's opened (`procedural::closed`).
    fn expand_procedural(&mut self, name: Sym, p: &procedural::Procedural, s: &Syn, interner: &mut Interner) -> R<Syn> {
        let made = fixpt_read::record_expansion(interner.name(name), s.span(), None, false);
        self.expansion_begun(made, p.def_env.clone());
        self.procedural_run(name, p, s, made, interner)
    }

    /// A use `s` of procedural macro `name`, whose contract is signature
    /// `sig`, expanded and held to it (`typed-macros.md`, "Decided:
    /// procedural macros checked by their contracts"): the use aligned with
    /// it, as any use is; then, unless `FIXPT_MACRO_CONTRACTS=0`, the
    /// transformer run on it, and again on it with each binder's name made
    /// fresh throughout its scope. The second's fresh names where their
    /// binders' scopes are (placement); with them named back, the first
    /// (commutation). The first is the expansion. Of a contract that makes
    /// definitions (`defn`), the expansion is definitions, and defines of
    /// the use's names exactly those it says (`defined_held`); a name it
    /// defines is a binder, renamed as any other.
    fn contract_expanded(&mut self, name: Sym, sig: &Rc<STy>, defn: bool, p: &procedural::Procedural, s: &Syn, interner: &mut Interner) -> R<Syn> {
        let shown = interner.name(name).to_string();
        let refused = |why: &str| FxError::at(s.at(), format!("a use of `{shown}`: {why}"));
        let (head, operands) = split(s).expect("a list");
        let none = HashMap::default();
        let mut u = Aligner { m: self, interner, mode: Mode::Use, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new(), heads: None, pending: Vec::new(), apps: None, whole: false };
        u.align(sig, &operands, None, Path::ROOT).map_err(|e| FxError::at(e.span, format!("a use of `{shown}`: {}", e.message)))?;
        let made = fixpt_read::record_expansion(&shown, s.span(), None, false);
        self.expansion_begun(made, p.def_env.clone());
        let out = self.procedural_run(name, p, s, made, interner)?;
        if !self.withs.contracts {
            return Ok(out);
        }
        let made_ty = Rc::new(if defn { STy::Defn } else { STy::Expr });
        if defn {
            self.defined_held(sig, &operands, &out, made, interner).map_err(|e| refused(&e.message))?;
        }
        let (parts, fresh) = self.contract_renames(sig, &operands, interner).map_err(|e| refused(&e.message))?;
        if fresh.is_empty() {
            return Ok(out);
        }
        // The use α-renamed: each binder part its fresh name; in each part
        // in a binder's scope, the references to it, as the part's own
        // binding structure finds them (its macros' uses read by their
        // signatures), and nothing else of it.
        let mut done: HashMap<u64, Syn> = HashMap::default();
        for (raw, (renames, core, part)) in &parts {
            let r = if matches!(**core, STy::Bvar | STy::Dvar) {
                renamed_syn(part, renames, interner)
            } else {
                self.references_renamed(part, core, renames, interner).map_err(|e| {
                    if e.message.contains("is a procedural macro, whose binding structure no signature says") {
                        refused("its contract cannot be checked: a part of it holds a use of a procedural macro with no contract")
                    } else {
                        refused(&e.message)
                    }
                })?
            };
            done.insert(*raw, r);
        }
        let use2 = Syn::of_list(s.at(), &[head], Some(substituted(&operands, &done)));
        let out2 = self.procedural_run(name, p, &use2, made, interner)?;
        // The two expansions the same up to their own binders' names: each
        // aligned (nothing expanded) and compared node by node, a reference
        // by the binder that binds it, or by its name if free.
        let ours = |e: FxError| refused(&format!("its expansion: {}", e.message));
        let (a, b) = (self.alpha_nodes(&out, &made_ty, interner).map_err(ours)?, self.alpha_nodes(&out2, &made_ty, interner).map_err(ours)?);
        if alpha_same(&a, &b) {
            return Ok(out);
        }
        // Which way it is not: a fresh name, or its alias (`%~K.N:x′`, a name
        // the transformer wrote where its macro is defined), free in the
        // second, placed outside its binder's scope; else the transformer
        // read a name.
        let escaped = b.iter().find_map(|n| match n {
            AlphaNode::Free(x, _) => fresh.get(x).copied().or_else(|| {
                let name = interner.name(*x);
                let base = name.strip_prefix(&format!("%~{}:", self.tag_of(made)))?;
                fresh.iter().find(|(f, _)| interner.name(**f) == base).map(|(_, o)| *o)
            }),
            _ => None,
        });
        Err(match escaped {
            Some(x) => refused(&format!("its expansion places `{}` where its contract does not put it in `{0}`'s scope", interner.name(x))),
            None => refused("its expansion depends on how its use's bound names are spelled"),
        })
    }

    /// Part `part` of a use, of syntax type `core`, each free reference in
    /// it to a name `renames` names made what it names, as the part's own
    /// binding structure finds them (aligned as a program's form is, its
    /// macros' uses by their signatures); its binders, and what it quotes,
    /// as they are.
    fn references_renamed(&self, part: &Syn, core: &Rc<STy>, renames: &HashMap<Sym, Sym>, interner: &mut Interner) -> R<Syn> {
        let none = HashMap::default();
        let (a, _, found, _) = Aligner::program(self, interner, &none, core, part, false, &HashSet::default())?;
        let mut at: HashMap<u64, Sym> = HashMap::default();
        for (i, env, _, _) in &found {
            if let Kids::Ref(n, ns, _) = a.nodes[*i].kids
                && let Some(to) = renames.get(&n)
                && a.bound_by(env, n, ns).is_none()
            {
                at.insert(a.nodes[*i].syn.0.raw(), *to);
            }
        }
        Ok(renamed_at(part, &at, interner))
    }

    /// Output `s`'s nodes, aligned as a program's form is (nothing
    /// expanded, its macros' uses by their signatures) and walked, each as
    /// α-equivalence takes it (`AlphaNode`).
    fn alpha_nodes(&self, s: &Syn, made: &Rc<STy>, interner: &mut Interner) -> R<Vec<AlphaNode>> {
        let none = HashMap::default();
        let (a, _, found, _) = Aligner::program(self, interner, &none, made, s, false, &HashSet::default())?;
        let envs: HashMap<usize, Env> = found.into_iter().map(|(i, env, _, _)| (i, env)).collect();
        Ok(a.nodes
            .iter()
            .enumerate()
            .map(|(i, n)| match &n.kids {
                Kids::Pair(x, y) => AlphaNode::Pair(*x, *y),
                Kids::Nil => AlphaNode::Nil,
                Kids::PVar(_) => AlphaNode::Other(n.syn),
                Kids::Binder(_, ns) => AlphaNode::Binder(*ns == Ns::Desc),
                Kids::Ref(x, ns, _) => match envs.get(&i).and_then(|env| a.bound_by(env, *x, *ns)) {
                    Some(b) => AlphaNode::Bound(b),
                    None => AlphaNode::Free(*x, *ns == Ns::Desc),
                },
                Kids::Desc(xs) => AlphaNode::Desc(xs.clone()),
                Kids::Seq(x, m) => AlphaNode::Seq(*x, *m),
                Kids::Form(x) => AlphaNode::Form(*x),
                Kids::Other => AlphaNode::Other(n.syn),
            })
            .collect())
    }

    /// The parts of use operands `operands`, aligned with contract `sig`,
    /// that a binder's scope reaches: each with what is renamed in it, its
    /// binders' names each to a fresh one, the innermost binder of a name
    /// first; and each fresh name with the name it stands for. Found as a
    /// pattern's are: each of the use's parts at a leaf of the signature
    /// made a pattern variable, the pattern aligned and walked, each
    /// variable's environment the binders in scope where it is.
    #[allow(clippy::type_complexity)]
    fn contract_renames(&self, sig: &Rc<STy>, operands: &Syn, interner: &mut Interner) -> R<(HashMap<u64, (HashMap<Sym, Sym>, Rc<STy>, Syn)>, HashMap<Sym, Sym>)> {
        let (pattern, parts) = self.contract_pattern(sig, operands, interner)?;
        let none = HashMap::default();
        let mut p = Aligner { m: self, interner, mode: Mode::Pattern, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new(), heads: None, pending: Vec::new(), apps: None, whole: false };
        let root = p.align(sig, &pattern, None, Path::ROOT)?;
        let mut found = Vec::new();
        p.walk(root, &Env::default(), false, 0, &mut found, &mut Vec::new())?;
        let part_of = |n: Sym, i: &Interner| i.name(n).strip_prefix("%part:").and_then(|k| k.parse::<usize>().ok());
        let mut binders: HashMap<Sym, Sym> = HashMap::default();
        let mut fresh: HashMap<Sym, Sym> = HashMap::default();
        let mut scoped: Vec<(usize, Vec<Sym>, Rc<STy>)> = Vec::new();
        for (at, env, _, _) in &found {
            let Kids::PVar(n) = p.nodes[*at].kids else { continue };
            let Some(k) = part_of(n, p.interner) else { continue };
            if matches!(&*p.nodes[*at].core, STy::Bvar | STy::Dvar) {
                binders.insert(n, parts[k].sym().ok_or_else(|| FxError::at(parts[k].at(), "a binder that is not a name"))?);
            }
            // The binders in its scope, innermost first.
            let mut in_scope = Vec::new();
            for level in env.to_vec() {
                match level {
                    Level::Rib(atoms) | Level::Earlier(atoms) => {
                        for a in atoms.iter() {
                            match a {
                                Atom::Var(b, _, _) => in_scope.push(*b),
                                _ => return Err(FxError::at(parts[k].at(), "a part in the scope of the binders another part exports: not yet in a procedural macro's contract")),
                            }
                        }
                    }
                    _ => return Err(FxError::at(parts[k].at(), "a part in the scope of a ribcage or a module: not yet in a procedural macro's contract")),
                }
            }
            scoped.push((k, in_scope, p.nodes[*at].core.clone()));
        }
        // Each binder a fresh name; each part, what is renamed in it.
        let mut fresh_of: HashMap<Sym, Sym> = HashMap::default();
        for (b, x) in &binders {
            let k = part_of(*b, interner).expect("a part");
            let to = interner.intern(&format!("%contract:{k}:{}", interner.name(*x)));
            fresh_of.insert(*b, to);
            fresh.insert(to, *x);
        }
        let mut out: HashMap<u64, (HashMap<Sym, Sym>, Rc<STy>, Syn)> = HashMap::default();
        for (k, in_scope, core) in scoped {
            let mut renames: HashMap<Sym, Sym> = HashMap::default();
            // A binder part renames its own name.
            if let Some(to) = binders.keys().find(|b| part_of(**b, interner) == Some(k)).and_then(|b| fresh_of.get(b)) {
                renames.insert(binders[binders.keys().find(|b| part_of(**b, interner) == Some(k)).expect("one")], *to);
            }
            for b in in_scope {
                let (Some(x), Some(to)) = (binders.get(&b), fresh_of.get(&b)) else { continue };
                renames.entry(*x).or_insert(*to);
            }
            if !renames.is_empty() {
                out.insert(parts[k].0.raw(), (renames, core, parts[k]));
            }
        }
        Ok((out, fresh))
    }

    /// Definitions `out`, what a transformer made of use operands
    /// `operands` in expansion `made`, held to contract `sig`: definitions,
    /// aligned as a program's are, that define of the use's names exactly
    /// those the contract says its uses define; any other name they define
    /// their own, an alias of the expansion (`%~K.N:x`), which nothing outside
    /// it names.
    fn defined_held(&self, sig: &Rc<STy>, operands: &Syn, out: &Syn, made: u32, interner: &mut Interner) -> R<()> {
        let none = HashMap::default();
        let not_yet = |at: &Syn| FxError::at(at.at(), "a contract whose uses define what a part of theirs defines: not yet");
        // What the contract says a use defines, of its names.
        let (pattern, parts) = self.contract_pattern(sig, operands, interner)?;
        let mut said: Vec<(Sym, Ns)> = Vec::new();
        {
            let mut p = Aligner { m: self, interner, mode: Mode::Pattern, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new(), heads: None, pending: Vec::new(), apps: None, whole: false };
            let root = p.align(sig, &pattern, None, Path::ROOT)?;
            p.walk(root, &Env::default(), false, 0, &mut Vec::new(), &mut Vec::new())?;
            if let Some((b, r)) = p.nodes[root].export.clone() {
                let (atoms, cages) = exports(&p.eval(&b, r, pattern.at())?);
                if !cages.is_empty() {
                    return Err(not_yet(operands));
                }
                for a in atoms {
                    match a {
                        Atom::Var(n, ns, _) => {
                            let k = p.interner.name(n).strip_prefix("%part:").and_then(|k| k.parse::<usize>().ok()).expect("a part");
                            said.push((parts[k].sym().ok_or_else(|| FxError::at(parts[k].at(), "a binder that is not a name"))?, ns));
                        }
                        Atom::RibOf(_) => return Err(not_yet(operands)),
                        Atom::Lit(..) => {}
                    }
                }
            }
        }
        // What the expansion defines.
        let mut defines: Vec<(Sym, Ns)> = Vec::new();
        {
            let ours = |e: FxError| FxError::at(e.span, format!("its expansion: {}", e.message));
            let (a, _, _, _) = Aligner::program(self, interner, &none, &Rc::new(STy::Defn), out, false, &HashSet::default()).map_err(ours)?;
            for i in 0..a.nodes.len() {
                let (STy::Item | STy::Defn, Kids::Form(x)) = (&*a.nodes[i].core, &a.nodes[i].kids) else { continue };
                let Some((b, r)) = a.nodes[*x].export.clone() else { continue };
                for level in a.eval(&b, r, a.nodes[i].syn.at()).map_err(ours)? {
                    let Level::Rib(atoms) = level else { continue };
                    for t in atoms.iter() {
                        if let Atom::Lit(t, ns) = t
                            && let Kids::Binder(n, _) = a.nodes[*t].kids
                            && !defines.contains(&(n, *ns))
                        {
                            defines.push((n, *ns));
                        }
                    }
                }
            }
        }
        let own = format!("%~{}:", self.tag_of(made));
        if let Some((n, _)) = defines.iter().find(|d| !said.contains(d) && !interner.name(d.0).starts_with(&own)) {
            return Err(FxError::at(out.at(), format!("its expansion defines `{}`, which its contract does not say a use defines, nor is it its own (an alias, as `rename` makes one)", interner.name(*n))));
        }
        if let Some((n, _)) = said.iter().find(|d| !defines.contains(d)) {
            return Err(FxError::at(out.at(), format!("its contract says a use defines `{}`, and its expansion does not", interner.name(*n))));
        }
        Ok(())
    }

    /// Use operands `operands` as a pattern of contract `sig`: each of the
    /// use's parts at a leaf of the signature a pattern variable of its own,
    /// `%part:k`, the part `parts[k]`.
    fn contract_pattern(&self, sig: &Rc<STy>, operands: &Syn, interner: &mut Interner) -> R<(Syn, Vec<Syn>)> {
        let none = HashMap::default();
        let mut u = Aligner { m: self, interner, mode: Mode::Use, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new(), heads: None, pending: Vec::new(), apps: None, whole: false };
        u.align(sig, operands, None, Path::ROOT)?;
        let leaf = |t: &STy| matches!(t, STy::Expr | STy::Lambda | STy::Bvar | STy::Dvar | STy::Id | STy::Data | STy::Type | STy::Label | STy::Kind | STy::Defn | STy::Item);
        let mut leaves: HashSet<u64> = HashSet::default();
        for n in &u.nodes {
            if n.hole.is_some() {
                return Err(FxError::at(n.syn.at(), "a procedural macro's contract of typed parts: not yet"));
            }
            if leaf(&n.core) {
                leaves.insert(n.syn.0.raw());
            }
        }
        drop(u);
        // The pattern: each leaf a variable of its own.
        let mut parts: Vec<Syn> = Vec::new();
        let pattern = pseudo_pattern(operands, &leaves, &mut parts, interner);
        Ok((pattern, parts))
    }

    /// Procedural macro `name`'s transformer run on use `s`, by expansion
    /// `made`: what it gave, read back at the use's place, a syntactic
    /// closure's opened.
    fn procedural_run(&mut self, name: Sym, p: &procedural::Procedural, s: &Syn, made: u32, interner: &mut Interner) -> R<Syn> {
        // In the runtime the syntax is in, if the session lent it: in the
        // expansion's phase-1 namespace; else in the transformers' session,
        // the datum and what it gave copied between the heaps. On the use's
        // datum, what it gives made syntax at once, no text between either
        // way (`TODO.md` §278, stages 4 and 6).
        let out = match self.phase1_run(p, s) {
            Some(out) => out,
            None => self.procedural_apart(p, s),
        };
        let out = out.map_err(|e| FxError::at(s.at(), format!("a use of `{}`: its transformer: {e}", interner.name(name))))?;
        let placed = At { expansion: made, ..s.at() };
        let at = crate::heap_syn::syn_of_datum(out, placed, interner)
            .map_err(|e| FxError::at(s.at(), format!("a use of `{}`: what its transformer gave is not syntax: {e}", interner.name(name))))?;
        self.procedural_opened(p, at, made, interner)
    }

    /// Transformer `code`, of `style`, defined in the phase-1 namespace of
    /// the runtime lent with the syntax, where it is defined: none where no
    /// runtime is lent, or it has no phase 1.
    fn phase1_define(&mut self, style: procedural::Style, code: &str, forms: &[crate::phase1::Form]) -> Option<Result<(), String>> {
        if !self.withs.world.borrow().session {
            return None;
        }
        crate::heap_syn::with_runtime(|rt| {
            crate::phase1::Phase1::current(rt).ok()?;
            Some(crate::phase1::Phase1::current_for(rt, forms).map_err(String::from).and_then(|ph| ph.transformer(rt, style.ty(), &procedural::key(style, code), &procedural::helpers(code)).map(|_| ())))
        })
        .flatten()
    }

    /// `(begin-for-syntax form …)`, `s`: its forms in force from now on, for
    /// each transformer defined after (`Withs::phase1`), checked, compiled
    /// and run in their namespace now, so that one refused is refused here
    /// (in the session's runtime if it is lent, else the transformers'
    /// session). Phase 1's alone: nothing of it is the program's. `dir`, the
    /// directory of the file `s` is written in, which its loads are read
    /// from (`phase1::Form`). A refusal at a place in one of its forms is
    /// said there, at the part whose text holds it.
    pub(crate) fn for_syntax(&mut self, s: &Syn, interner: &mut Interner, dir: &str) -> R<()> {
        let items = s.list().unwrap_or_default();
        let new: Vec<Syn> = items.iter().skip(1).cloned().collect();
        let old = self.withs.phase1.len();
        let mut forms = (*self.withs.phase1).clone();
        forms.extend(new.iter().map(|f| crate::phase1::Form { text: f.written(interner), dir: dir.to_string() }));
        let session = self.withs.world.borrow().session;
        let lent = session.then(|| crate::heap_syn::with_runtime(|rt| crate::phase1::Phase1::current(rt).ok().map(|_| crate::phase1::Phase1::current_for(rt, &forms).map(|_| ())))).flatten().flatten();
        let made = match lent {
            Some(made) => made,
            None => procedural::with_forms_checked(&forms),
        };
        if let Err(r) = made {
            let at = match r.at {
                Some((i, a, _)) if i >= old && i - old < new.len() => written_part(new[i - old].clone(), interner, a).at(),
                _ => s.at(),
            };
            return Err(FxError::at(at, format!("`begin-for-syntax`: {}", r.why)));
        }
        self.withs.phase1 = Rc::new(forms);
        Ok(())
    }

    /// Transformer `p` called on use `s` in expansion `made` in the phase-1
    /// namespace of the runtime lent with the syntax (`phase1.rs`), made and
    /// the transformer defined in it if they are not yet: its value, raw
    /// (nothing collects before the caller makes it syntax); or none where
    /// no runtime is lent (a checker's own heap), or it has no phase 1 (its
    /// front end not compiled).
    fn phase1_run(&mut self, p: &procedural::Procedural, s: &Syn) -> Option<Result<fixpt_heap::Value, String>> {
        if !self.withs.world.borrow().session {
            return None;
        }
        let datum = s.plain();
        crate::heap_syn::with_runtime(|rt| crate::phase1::run_transformer(rt, p.style, &p.code, &p.phase1, datum)).flatten()
    }

    /// Transformer `p` called on use `s` in expansion `made` in the
    /// transformers' session, its datum copied there and what it gave
    /// copied back into the heap lent (`procedural::apply_copied`): raw.
    fn procedural_apart(&mut self, p: &procedural::Procedural, s: &Syn) -> Result<fixpt_heap::Value, String> {
        let own = !self.withs.world.borrow().session;
        // Where the call will collect, in the front end's heap (`TODO.md`
        // §278): a test's, of a checker's own heap, the datum tenured.
        if own {
            crate::heap_syn::collect_young_if_asked();
        }
        let datum = s.plain();
        let out = crate::heap_syn::with_heap(|h| procedural::apply_copied(p.style, &p.code, &p.phase1, h, datum))?;
        Ok(if own { crate::heap_syn::collect_young_if_asked_keeping(out) } else { out })
    }

    /// What transformer `p` gave, made syntax at the use's place in
    /// expansion `made`, `at`: a syntactic closure's opened
    /// (`procedural::closed`), and the keywords in it taken as keywords.
    fn procedural_opened(&mut self, p: &procedural::Procedural, at: Syn, made: u32, interner: &mut Interner) -> R<Syn> {
        let opened = match p.style {
            procedural::Style::Er => procedural::tagged(&at, &self.tag_of(made), interner),
            procedural::Style::Sc => procedural::closed(&at, true, &self.tag_of(made), interner)?,
            procedural::Style::Rsc => procedural::closed(&at, false, &self.tag_of(made), interner)?,
        };
        // A name the transformer renamed that is another of its file's
        // macros: that macro, by the name the importer has it by (Heist's
        // report, 2026-11-18: else a standard name, `(with #%fx name)`).
        let opened = match &p.def_env {
            hygiene::DefEnv::File { internal, .. } if !internal.is_empty() => {
                let tag = self.tag_of(made);
                let renames: HashMap<Sym, Sym> = internal.iter().map(|(n, i)| (interner.intern(&procedural::alias(interner.name(*n), &tag)), *i)).collect();
                renamed_syn(&opened, &renames, interner)
            }
            _ => opened,
        };
        let defined: HashSet<String> = self.defined.keys().map(|k| interner.name(*k).to_string()).collect();
        let is_keyword = |n: &str| {
            self.k.forms.contains_key(n)
                || self.k.definitions.contains_key(n)
                || self.k.heads.contains(n)
                || self.k.words.contains(n)
                || self.k.type_forms.contains(n)
                || reserved(n)
                || matches!(n, "else" | "=>" | "quote" | "quasiquote" | "unquote" | "unquote-splicing")
                || transformer_word(n)
                || defined.contains(n)
        };
        Ok(procedural::keywords(&opened, &is_keyword, interner))
    }

    /// Template `t`, at `path` in it, transcribed by expansion `made`: each
    /// part the template makes at its own place in the `define-syntax`, of
    /// that expansion (provenance, not identity:
    /// `docs/research/loads-and-places.md`, "Decided: identity by
    /// position"), each pattern variable's what the use gave. `iters`: the
    /// repetition of each ellipsis it is under, outermost first; a binder's
    /// fresh name is by its path and the repetitions it is in.
    #[allow(clippy::too_many_arguments)]
    fn transcribe(&mut self, c: &Clause, t: &Syn, path: Path, binds: &HashMap<Sym, Syn>, fresh: &mut Made, iters: &mut Vec<usize>, made: u32, interner: &mut Interner) -> R<Syn> {
        let at = t.at().in_expansion(made);
        let typed = match c.actions.get(&path) {
            Some(Action::StandardType) => Some(interner.intern("#%fx")),
            Some(Action::ModuleType(m)) => Some(*m),
            Some(Action::InstanceType(m)) => Some(interner.intern(&procedural::alias(interner.name(*m), &self.tag_of(made)))),
            _ => None,
        };
        if let Some(m) = typed {
            return Ok(selected(m, t, made, interner));
        }
        if let (Some(Action::FrameType(m, frame, instance)), Some(n)) = (c.actions.get(&path), t.sym()) {
            let m = if *instance { interner.intern(&procedural::alias(interner.name(*m), &self.tag_of(made))) } else { *m };
            let (select, with) = (interner.intern("select"), interner.intern("with"));
            let alias = interner.intern(&format!("%ft:{}", interner.name(n)));
            let module = Syn::lst(at, vec![Syn::symbol(at, with, interner), Syn::symbol(at, m, interner), Syn::symbol(at, *frame, interner)]);
            return Ok(Syn::lst(at, vec![Syn::symbol(at, select, interner), module, Syn::symbol(at, alias, interner)]));
        }
        match &t.view() {
            V::Symbol(n) => {
                if let Some(b) = binds.get(n) {
                    // A typed hole's expression, held to its type; in a
                    // template's check, its call, where the template has it.
                    if self.checking {
                        return Ok(respanned(b, at));
                    }
                    return Ok(match c.contracts.get(n) {
                        Some(ty) => Syn::lst(b.at(), vec![Syn::named(b.at(), "the", interner), in_expansion(&ty.get(), made), *b]),
                        None => b.clone(),
                    });
                }
                Ok(match c.actions.get(&path) {
                    Some(Action::Rename(binder, depth)) => {
                        let key = (*binder, iters[..(*depth).min(iters.len())].to_vec());
                        let name = match fresh.fresh.get(&key) {
                            Some(f) => *f,
                            None => {
                                let tag = self.fresh_tag();
                                let f = interner.intern(&format!("%{}:{}", interner.name(*n), tag));
                                fresh.fresh.insert(key, f);
                                f
                            }
                        };
                        Syn::symbol(at, name, interner)
                    }
                    Some(Action::Alias) => {
                        let a = interner.intern(&procedural::alias(interner.name(*n), &self.tag_of(made)));
                        Syn::symbol(at, a, interner)
                    }
                    Some(Action::Mark(i)) => Syn::symbol(at, *i, interner),
                    _ => Syn::new(at, t.view().clone(), interner),
                })
            }
            // `(... ...)`, the ellipsis of a macro the template defines.
            V::List { items, tail } if items.len() == 2 && tail.is_none() && is_ellipsis(&items[0], interner) && is_ellipsis(&items[1], interner) => Ok(Syn::new(at, items[0].view().clone(), interner)),
            V::List { items, tail } => {
                let head = match c.actions.get(&path) {
                    Some(Action::MacroHead(h)) => Some(*h),
                    _ => None,
                };
                // Each item's path, the car of the cdrs before it.
                let mut rest = path;
                let mut out = Vec::new();
                let mut i = 0;
                while i < items.len() {
                    let item = rest.push(true);
                    // `p ...`: `p` once for each element of what the use gave
                    // of the pattern variables in it under more ellipses than
                    // this, together.
                    if items.get(i + 1).is_some_and(|x| is_ellipsis(x, interner)) {
                        let drivers: Vec<Sym> = c.pvars.iter().filter(|(n, p)| p.depth > iters.len() && find_symbol(&items[i], *n).is_some()).map(|(n, _)| *n).collect();
                        let lists: Vec<Vec<Syn>> = drivers.iter().map(|n| elements(&binds[n])).collect();
                        if let Some((k, _)) = lists.iter().enumerate().find(|(_, l)| l.len() != lists[0].len()) {
                            let (a, b) = (interner.name(drivers[0]), interner.name(drivers[k]));
                            return Err(FxError::at(items[i].at(), format!("`{a}` and `{b}`, repeated together, are given {} and {} times", lists[0].len(), lists[k].len())));
                        }
                        // The binders of the template's repeated in it,
                        // and those it refers to that were repeated before.
                        let under: Vec<(&Path, &Path)> = c
                            .actions
                            .iter()
                            .filter_map(|(at, a)| match a {
                                Action::Rename(b, d) if *d > iters.len() && at.starts_with(item) => Some((at, b)),
                                _ => None,
                            })
                            .collect();
                        // Every count it is repeated by agrees: the pattern
                        // variables', and the repeated binders' it refers to.
                        let mut known: Vec<usize> = under.iter().filter_map(|(_, b)| fresh.counts.get(&((*b).clone(), iters.clone())).copied()).collect();
                        known.extend(lists.first().map(|l| l.len()));
                        let Some(&times) = known.first() else {
                            return Err(FxError::at(items[i].at(), "this part is repeated before the repetition that binds what it refers to"));
                        };
                        if known.iter().any(|k| *k != times) {
                            return Err(FxError::at(items[i].at(), "this part repeats binders and parts that were repeated, or given, different numbers of times"));
                        }
                        for (at, b) in &under {
                            if at == b {
                                fresh.counts.insert(((*b).clone(), iters.clone()), times);
                            }
                        }
                        for r in 0..times {
                            let mut each = binds.clone();
                            for (n, l) in drivers.iter().zip(&lists) {
                                each.insert(*n, l[r].clone());
                            }
                            iters.push(r);
                            let x = self.transcribe(c, &items[i], item, &each, fresh, iters, made, interner);
                            iters.pop();
                            out.push(x?);
                        }
                        rest = rest.push(false).push(false);
                        i += 2;
                        continue;
                    }
                    out.push(self.transcribe(c, &items[i], item, binds, fresh, iters, made, interner)?);
                    rest = rest.push(false);
                    i += 1;
                }
                if let Some(h) = head {
                    out[0] = Syn::symbol(out[0].at(), h, interner);
                }
                let tail = match tail {
                    Some(x) => Some(self.transcribe(c, x, rest, binds, fresh, iters, made, interner)?),
                    None => None,
                };
                // A checked use's: trusted to fit, as it is expanded.
                if made != 0 && c.checked_uses.contains(&t.at().start) {
                    self.withs.trusted.insert(at);
                }
                Ok(list_of(at, out, tail))
            }
            _ => Ok(Syn::new(at, t.view().clone(), interner)),
        }
    }
}

impl Aligner<'_> {
    fn name(&self, n: Sym) -> &str {
        self.interner.name(n)
    }

    /// `s`, at `path`, aligned with type `t`; `root`, the node its
    /// addresses are from, if not itself.
    fn align(&mut self, t: &Rc<STy>, s: &Syn, root: Option<usize>, path: Path) -> R<usize> {
        let at = self.node_new(t, s, path);
        self.fill(at, t, s, root.unwrap_or(at))?;
        Ok(at)
    }

    /// Transformer `s_owned` a template writes, at node `at` (`STy::Rules`):
    /// each name a reference, but a form's word, `_`, a macro's or a
    /// trailmark's name; a list, its parts so; `(... ...)` the defined
    /// macro's ellipsis, a quoted datum as it is. Nothing of it in another
    /// mode, where it is the defined macro's alone.
    fn rules(&mut self, at: usize, s_owned: Syn, root: usize) -> R<Option<Step>> {
        if self.mode != Mode::Template {
            return Ok(None);
        }
        self.nodes[at].many = true;
        let s = &s_owned;
        let fail = |why: &str| FxError::at(s.at(), why.to_string());
        let dots = "`...` in a macro a template defines is the template's (R7RS), and repeats nothing here: the defined macro's is written `(... ...)`";
        match s.view() {
            V::Symbol(n) => {
                let name = self.name(n);
                if name == "..." {
                    return Err(fail(dots));
                }
                let k = &self.m.k;
                let word = name == "_"
                    || reserved(name)
                    || k.forms.contains_key(name)
                    || k.definitions.contains_key(name)
                    || self.word(n, true)
                    || k.type_forms.contains(name)
                    || matches!(name, "else" | "=>" | "quote" | "quasiquote" | "unquote" | "unquote-splicing")
                    || transformer_word(name)
                    || self.m.defined.contains_key(&n)
                    || self.m.mark_of(n).is_some();
                if !word {
                    self.nodes[at].kids = Kids::Ref(n, Ns::Value, Free::Inner);
                }
                Ok(None)
            }
            V::List { items, tail } => {
                let is_dots = |x: &Syn| is_ellipsis(x, self.interner);
                if items.len() == 2 && tail.is_none() && is_dots(&items[0]) && is_dots(&items[1]) {
                    return Ok(None);
                }
                if is_dots(&items[0]) {
                    return Err(fail("`(... template)` other than `(... ...)`: not yet"));
                }
                if items.iter().any(is_dots) {
                    return Err(fail(dots));
                }
                if items[0].sym().is_some_and(|h| self.name(h) == "quote") {
                    return Ok(Some((at, Rc::new(STy::Data), s_owned, root)));
                }
                let r = Rc::new(STy::Rules);
                // A `define-syntax` in it: its signature a datum.
                if items.len() == 4 && tail.is_none() && items[0].sym().is_some_and(|h| self.name(h) == "define-syntax") {
                    let nil = Rc::new(STy::Nil);
                    let rest = Rc::new(STy::Pair(Rc::new(STy::Data), Rc::new(STy::Pair(r.clone(), nil))));
                    return Ok(Some((at, Rc::new(STy::Pair(r.clone(), Rc::new(STy::Pair(r, rest)))), s_owned, root)));
                }
                Ok(Some((at, Rc::new(STy::Pair(r.clone(), r)), s_owned, root)))
            }
            V::Nil => {
                self.nodes[at].kids = Kids::Nil;
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// A node for `s`, at `path`, of type `t`, to be filled.
    fn node_new(&mut self, t: &Rc<STy>, s: &Syn, path: Path) -> usize {
        let at = self.nodes.len();
        // The node's syntax is the form's own, shared, not a copy.
        self.nodes.push(Node { syn: *s, path, core: t.clone(), imports: Vec::new(), export: None, many: false, hole: None, desc: false, repeated: false, head: false, kids: Kids::Other });
        at
    }

    fn fill(&mut self, at: usize, t: &Rc<STy>, s: &Syn, root: usize) -> R<()> {
        self.run((at, t.clone(), s.clone(), root))
    }

    /// Step `first` filled, and every part it leaves to fill after it
    /// (`work`), in a loop: a list's rest, a form's operands and a list's
    /// first part each a step, so that neither a long list nor deep
    /// nesting takes stack. The parts left are filled first first.
    fn run(&mut self, first: Step) -> R<()> {
        let base = self.work.len();
        let mut next = Some(first);
        loop {
            while let Some((at, t, s, root)) = next {
                next = match self.fill_step(at, t, s, root) {
                    Ok(n) => n,
                    Err(e) => {
                        self.work.truncate(base);
                        return Err(e);
                    }
                };
            }
            if self.work.len() == base {
                return Ok(());
            }
            next = self.work.pop();
        }
    }

    /// One step of `fill`: what is left to fill, a list's rest or the same
    /// part at a type unfolded, so that a long list takes no stack.
    fn fill_step(&mut self, at: usize, t: Rc<STy>, s_owned: Syn, root: usize) -> R<Option<Step>> {
        let s = &s_owned;
        let t = &t;
        let fail = |why: String| FxError::at(s.at(), why);
        match &**t {
            STy::Import(body, b) => {
                self.nodes[at].imports.push((b.clone(), root));
                return Ok(Some((at, body.clone(), s_owned, root)));
            }
            STy::Many(body) => {
                self.nodes[at].many = true;
                return Ok(Some((at, body.clone(), s_owned, root)));
            }
            STy::Typed(body, h) => {
                self.nodes[at].hole = Some(h.clone());
                return Ok(Some((at, body.clone(), s_owned, root)));
            }
            STy::Export(body, b) => {
                if self.nodes[at].export.is_some() {
                    return Err(fail("two exports at one part".into()));
                }
                self.nodes[at].export = Some((b.clone(), root));
                return Ok(Some((at, body.clone(), s_owned, root)));
            }
            _ => {}
        }
        self.nodes[at].core = t.clone();
        // What it is, looked at once.
        let shape = s.shape();
        // A pattern's variable, or one placed in a template: at any type.
        if let Shape::Symbol(n) = shape {
            let lit = matches!(&*self.m.unfold(t), STy::Literal(_) | STy::Mark(..));
            // A trailmark's name in a pattern is the trailmark, where the
            // signature writes it, and no variable.
            let mark = self.mode == Mode::Pattern && self.m.mark_of(n).is_some();
            if mark && !matches!(&*self.m.unfold(t), STy::Mark(..) | STy::Union(_)) {
                return Err(fail(format!("`{}` is a trailmark, which a pattern matches where its signature writes `(trailmark {0})`, and no pattern variable", self.name(n))));
            }
            let pvar = match self.mode {
                Mode::Pattern => !lit && !mark && self.name(n) != "_" && self.name(n) != "...",
                Mode::Template => self.pvars.contains_key(&n),
                Mode::Use | Mode::Program => false,
            };
            if pvar {
                // A pattern's variable where a name or a list may be: the
                // name's shape, if one member is a name's.
                if self.mode == Mode::Pattern
                    && let STy::Union(ms) = &*self.m.unfold(t)
                {
                    let names: Vec<&Rc<STy>> = ms.iter().filter(|m| matches!(&*self.m.unfold(m), STy::Bvar | STy::Dvar | STy::Id | STy::Label)).collect();
                    if let [one] = &names[..] {
                        let one = (*one).clone();
                        return Ok(Some((at, one, s_owned, root)));
                    }
                }
                self.nodes[at].kids = Kids::PVar(n);
                return Ok(None);
            }
        }
        if matches!(&**t, STy::Rules) {
            return self.rules(at, s_owned, root);
        }
        // `(p ...)`, a pattern's or a template's: `p` aligned with the list's
        // element type, repeated; the list exports what each element does.
        if matches!(self.mode, Mode::Pattern | Mode::Template) && let Some(x) = ellipsis(s, self.interner) {
            let Some((elem, cage)) = self.m.seq_of(t) else {
                return Err(fail(format!("`{}` repeats a part by `...` where the form takes no list of them", self.show(s))));
            };
            let p = self.nodes[at].path.push(true);
            let e = self.align(&elem, &x, None, p)?;
            self.nodes[e].repeated = true;
            // A pattern variable where elements of more than one shape may
            // be: the shape it fits, and what that exports.
            if let (Kids::PVar(_), STy::Union(ms)) = (&self.nodes[e].kids, &*elem) {
                let fit: Vec<&Rc<STy>> = ms.iter().filter(|m| self.m.fits(m, &x, self.mode, self.interner, self.pvars)).collect();
                if let [one] = &fit[..] {
                    let one = (*one).clone();
                    if let STy::Export(_, b) = &*one {
                        self.nodes[e].export = Some((b.clone(), e));
                    }
                    self.nodes[e].core = self.m.peel(&one).clone();
                }
            }
            self.nodes[at].kids = Kids::Seq(e, cage);
            // What each element exports, the list does, of each.
            if self.nodes[at].export.is_none() {
                self.nodes[at].export = self.nodes[e].export.clone();
            }
            return Ok(None);
        }
        if matches!(self.mode, Mode::Pattern | Mode::Template) && matches!(shape, Shape::Symbol(n) if self.name(n) == "...") {
            return Err(fail("`...` follows the part it repeats, last in a list".into()));
        }
        match &**t {
            STy::Rules => unreachable!("taken above"),
            STy::Var(_) => unreachable!("a signature closed"),
            STy::Mu(..) => Ok(Some((at, unfold_mu(t), s_owned, at))),
            STy::Union(ms) => {
                let mut fit: Vec<&Rc<STy>> = ms.iter().filter(|m| self.m.fits(m, s, self.mode, self.interner, self.pvars)).collect();
                // A program's name that a form's word may be too, `else`
                // or a variable bound to `else`: the form's word, if a
                // member writes it.
                if self.mode == Mode::Program && fit.len() > 1 {
                    fit.retain(|m| self.m.fits(m, s, Mode::Use, self.interner, self.pvars));
                }
                match &fit[..] {
                    [one] => {
                        let one = (*one).clone();
                        Ok(Some((at, one, s_owned, at)))
                    }
                    [] => Err(fail(format!("`{}` is of none of the shapes this part may have", self.show(s)))),
                    _ => Err(fail(format!("`{}` could be of more than one of this part's shapes", self.show(s)))),
                }
            }
            STy::Pair(a, d) => {
                if !matches!(shape, Shape::List | Shape::Dotted) {
                    return Err(fail(format!("`{}` is not a list as this part must be", self.show(s))));
                }
                // Taken apart, not copied: a long list's rest is not made
                // again at each of its parts.
                let (x, y) = split_owned(s_owned).expect("a list");
                // A use's paths none: only its fit is wanted, and a list's
                // part's path is as long as where it is (`TODO.md` §231).
                let (ap, dp) = if self.mode == Mode::Use {
                    (Path::ROOT, Path::ROOT)
                } else {
                    let path = self.nodes[at].path;
                    (path.push(true), path.push(false))
                };
                let x_at = self.node_new(a, &x, ap);
                // The rest, its node made here and filled after the first
                // part; a program's keeps only its place (what a rest is,
                // its parts say).
                let rest = self.nodes.len();
                let syn = if self.mode == Mode::Program { Syn::nil(y.at()) } else { y.clone() };
                self.nodes.push(Node { syn, path: dp, core: d.clone(), imports: Vec::new(), export: None, many: false, hole: None, desc: false, repeated: false, head: false, kids: Kids::Other });
                self.nodes[at].kids = Kids::Pair(x_at, rest);
                self.work.push((rest, d.clone(), y, root));
                Ok(Some((x_at, a.clone(), x, root)))
            }
            STy::Nil => match shape {
                Shape::Nil => {
                    self.nodes[at].kids = Kids::Nil;
                    Ok(None)
                }
                _ => Err(fail(format!("`{}` is more than this part may have", self.show(s)))),
            },
            STy::Literal(n) => match shape.sym() {
                Some(m) if m == *n => Ok(None),
                _ => Err(fail(format!("`{}` where `{}` is written", self.show(s), self.name(*n)))),
            },
            // A trailmark: a name bound to this one, where it is read (a
            // pattern's and a template's, where the macro is defined).
            STy::Mark(n, id) => match shape.sym() {
                Some(m) if self.m.mark_of(m).is_some_and(|k| k.id == *id) => Ok(None),
                _ => Err(fail(format!("`{}` where the trailmark `{}` is written", self.show(s), self.name(*n)))),
            },
            // A program's binder: any name the checkers let it bind, which
            // they decide.
            STy::Bvar | STy::Dvar if self.mode == Mode::Program && shape.sym().is_some() => {
                let n = shape.sym().expect("a name");
                let ns = if matches!(&**t, STy::Dvar) { Ns::Desc } else { Ns::Value };
                self.nodes[at].kids = Kids::Binder(n, ns);
                Ok(None)
            }
            // A use's binder may be a macro's name, which it shadows where
            // it binds (`TODO.md` §295); a template's own may not, not yet.
            STy::Bvar | STy::Dvar => match shape.sym() {
                Some(n) if self.mode == Mode::Template && self.m.defined.contains_key(&n) => Err(fail(format!("`{}` is a macro's name, which is not bound", self.name(n)))),
                Some(n) if self.m.mark_of(n).is_some() => Err(fail(format!("`{}` is a trailmark, which is not bound", self.name(n)))),
                // A value's binder a use gives: as a program's, any name the
                // checkers let it bind, a keyword too (`fields`, Heist's),
                // which a template's form, read by its head, does not see
                // bound.
                Some(n) if (self.mode == Mode::Use && matches!(&**t, STy::Bvar)) || (!reserved(self.name(n)) && !(matches!(&**t, STy::Dvar) && self.word(n, false))) => {
                    if self.writes() {
                        let ns = if matches!(&**t, STy::Dvar) { Ns::Desc } else { Ns::Value };
                        self.nodes[at].kids = Kids::Binder(n, ns);
                    }
                    Ok(None)
                }
                _ => Err(fail(format!("`{}` is not a name that may be bound", self.show(s)))),
            },
            STy::Kind => Ok(None),
            STy::Id => match shape.sym() {
                Some(n) => {
                    if self.writes() {
                        self.nodes[at].kids = Kids::Ref(n, Ns::Value, Free::Toplevel);
                    }
                    Ok(None)
                }
                None => Err(fail(format!("`{}` is not a variable", self.show(s)))),
            },
            STy::Label => match shape {
                Shape::Keyword(_) => Ok(None),
                // A use's any name but a word the kernel's forms read, which
                // a template's label never is (`fits_shaped`), its form's.
                Shape::Symbol(n) if self.mode == Mode::Use && self.m.literal_word(n) => Err(fail(format!("`{}` is a reserved word, not a tag or label", self.name(n)))),
                Shape::Symbol(_) if matches!(self.mode, Mode::Use | Mode::Program) => Ok(None),
                // A product's field by its position, a program's.
                Shape::Atom if self.mode == Mode::Program && matches!(s.view(), V::Number(_)) => Ok(None),
                Shape::Symbol(n) => Err(fail(format!("a tag or label in a template is a keyword: `#:{}`, not `{0}`", self.name(n)))),
                _ => Err(fail(format!("`{}` is not a tag or label", self.show(s)))),
            },
            STy::Data => {
                if self.mode == Mode::Template && let Some(n) = self.pvar_in(s) {
                    return Err(fail(format!("pattern variable `{}` inside a quoted datum: only a whole one is placed", self.name(n))));
                }
                Ok(None)
            }
            // A description a template writes, name by name; the binders of
            // the `poly`s at its top, what it exports (what a definition's
            // type puts in scope in what it is defined as).
            STy::Type if self.writes() => {
                self.nodes[at].desc = true;
                self.desc(at, s)?;
                if self.nodes[at].export.is_none() {
                    let atoms = self.poly_binders(at);
                    self.nodes[at].export = Some((Bind::Direct(atoms), at));
                }
                Ok(None)
            }
            STy::Type => Ok(None),
            // A template writes a lambda (its form aligned as any of the
            // kernel's); a use gives one, of the shape the checkers take.
            // A program's lambda, as any expression of one.
            STy::Lambda if self.mode == Mode::Program => Ok(Some((at, Rc::new(STy::Expr), s_owned, root))),
            STy::Lambda => match (shape, self.mode) {
                (Shape::List, Mode::Template) if s.head_sym().is_some_and(|h| self.name(h) == "lambda") => self.form_owned(at, s_owned, false),
                _ if self.mode != Mode::Template && lambda_shaped(s, self.interner) => Ok(None),
                _ => Err(fail(format!("`{}` is not a lambda, as this part must be", self.show(s)))),
            },
            STy::Expr => match (shape, self.mode) {
                (Shape::Symbol(n), Mode::Program) if !matches!(self.name(n), "#t" | "#f" | "#u") => {
                    self.nodes[at].kids = Kids::Ref(n, Ns::Value, Free::Toplevel);
                    Ok(None)
                }
                (Shape::Symbol(n), _) if reserved(self.name(n)) => Err(fail(format!("`{}` is a form's name, not an expression", self.name(n)))),
                // `#u`, unit: a literal, which the parsers read as a name.
                (Shape::Symbol(n), _) if self.name(n) == "#u" => Ok(None),
                (Shape::Symbol(n), Mode::Template | Mode::Program) => {
                    self.nodes[at].kids = Kids::Ref(n, Ns::Value, Free::Toplevel);
                    Ok(None)
                }
                (Shape::List | Shape::Dotted, Mode::Template | Mode::Program) => self.form_owned(at, s_owned, false),
                (Shape::Nil, _) => Err(fail("`()` is not an expression".into())),
                _ => Ok(None),
            },
            STy::Defn => match (shape, self.mode) {
                (Shape::List | Shape::Dotted, Mode::Template | Mode::Program) => self.form_owned(at, s_owned, true),
                _ => Err(fail(format!("`{}` is not a definition", self.show(s)))),
            },
            // A module's item: a definition by its head, a string, or an
            // expression.
            STy::Item => {
                if self.defines(s) {
                    return self.form_owned(at, s_owned, true);
                }
                if matches!(s.view(), V::Str(_)) {
                    self.nodes[at].export = Some((Bind::Rib(Vec::new()), at));
                    return Ok(None);
                }
                Ok(Some((at, Rc::new(STy::Expr), s_owned, root)))
            }
            STy::Import(..) | STy::Export(..) | STy::Many(_) | STy::Typed(..) => unreachable!("taken off"),
        }
    }

    /// The expressions a quasiquote's datum `s`, at `path`, unquotes at
    /// `depth` 1, each aligned, onto `kids`: a nested `quasiquote` deepens,
    /// an `unquote` or `unquote-splicing` shallows, as R7RS counts.
    fn unquoted(&mut self, s: &Syn, path: Path, depth: u32, kids: &mut Vec<usize>) -> R<()> {
        match &s.view() {
            V::List { items, tail } => {
                let head = items[0].sym().map(|h| self.name(h).to_string());
                if items.len() == 2 && tail.is_none() {
                    let inner = path.extend(&[false, true]);
                    match head.as_deref() {
                        Some("unquote" | "unquote-splicing") if depth == 1 => {
                            kids.push(self.align(&Rc::new(STy::Expr), &items[1], None, inner)?);
                            return Ok(());
                        }
                        Some("unquote" | "unquote-splicing") => return self.unquoted(&items[1], inner, depth - 1, kids),
                        Some("quasiquote") => return self.unquoted(&items[1], inner, depth + 1, kids),
                        _ => {}
                    }
                }
                let mut p = path;
                for i in items {
                    self.unquoted(i, p.push(true), depth, kids)?;
                    p = p.push(false);
                }
                match tail {
                    Some(t) => self.unquoted(t, p, depth, kids),
                    None => Ok(()),
                }
            }
            V::Vector(items) if items.iter().any(|i| self.unquotes(i)) => {
                items.iter().for_each(|i| self.symbols_into(i));
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Whether `s` is a definition, by its head: a `begin` one if all it
    /// holds are.
    fn defines(&self, s: &Syn) -> bool {
        let l = s.list();
        let Some([h, rest @ ..]) = l.as_deref() else { return false };
        match h.sym().map(|h| self.name(h)) {
            Some("begin") => !rest.is_empty() && rest.iter().all(|r| self.defines(r)),
            Some(h) => self.m.k.definitions.contains_key(h) || self.m.k.scope_definitions.contains_key(h),
            None => false,
        }
    }

    /// Each name in `s`, unplaced.
    fn symbols_into(&mut self, s: &Syn) {
        match &s.view() {
            V::Symbol(n) => self.unplaced.push(*n),
            V::List { items, tail } => items.iter().chain(tail.as_ref()).for_each(|i| self.symbols_into(i)),
            V::Vector(items) => items.iter().for_each(|i| self.symbols_into(i)),
            _ => {}
        }
    }

    /// Whether `s` has an `unquote` or `unquote-splicing` in it.
    fn unquotes(&self, s: &Syn) -> bool {
        match &s.view() {
            V::Symbol(n) => matches!(self.name(*n), "unquote" | "unquote-splicing"),
            V::List { items, tail } => items.iter().chain(tail.as_ref()).any(|i| self.unquotes(i)),
            V::Vector(items) => items.iter().any(|i| self.unquotes(i)),
            _ => false,
        }
    }

    /// Whether this aligns what is written, a template's or a program's,
    /// its binders and references found.
    fn writes(&self) -> bool {
        matches!(self.mode, Mode::Template | Mode::Program)
    }

    /// A form in a template, at node `at`: a kernel form, a macro's use, or
    /// an application, aligned with its signature; a definition's, if
    /// `defn`, where a template makes definitions, else an expression's.
    /// What it aligns next, if anything: the type, the path, and whether
    /// it is the form's operands (else the whole form).
    fn form(&mut self, at: usize, s: &Syn, defn: bool) -> R<Option<(Rc<STy>, Path, bool)>> {
        let V::List { items, tail } = &s.view() else { unreachable!("a list") };
        let head = items[0].sym().filter(|h| !self.pvars.contains_key(h));
        // Where a form is expanded: a list a macro's name heads, a use,
        // whole (pending, for the walk to say what binds its head around
        // it), unless read as an application, its head bound around it.
        let head = match (&self.apps, head) {
            (Some(apps), Some(h)) if self.m.defined.contains_key(&h) => {
                let app = apps.contains(&self.nodes[at].path);
                self.nodes[at].head = true;
                self.pending.push((at, defn));
                if app {
                    None
                } else if self.whole {
                    self.use_whole(at, defn);
                    return Ok(None);
                } else {
                    head
                }
            }
            _ => head,
        };
        // A list whose head a `(macro σ made)` entry may bind: pending, read by
        // its scope (`Macros::template_aligned`), a use of that macro by
        // `σ` once its binder is found one, else an application (where a
        // definition is, unread until then).
        if let Some(heads) = self.heads
            && let Some(h) = items[0].sym()
            && self.unknown_head(h)
        {
            self.nodes[at].head = true;
            self.pending.push((at, defn));
            match heads.get(&s.0.raw()) {
                Some(Head::Macro(k)) => {
                    let (sig, mdefn, mdesc) = self.m.withs.syntax_sigs[k].clone();
                    let n = self.name(h);
                    let not_one = |what: &str| FxError::at(s.at(), format!("`{}` is not a definition: a macro that makes definitions makes {what}", self.show(s)));
                    match (defn, mdefn, mdesc) {
                        (false, true, _) => return Err(FxError::at(s.at(), format!("`{n}` makes definitions, which are made at the top level, not where an expression is"))),
                        (false, _, true) => return Err(FxError::at(s.at(), format!("`{n}` makes a description, not an expression"))),
                        (true, _, true) => return Err(not_one("them by a macro that makes definitions, not a description's")),
                        (true, false, _) => return Err(not_one("them by a macro that makes definitions, not an expression's")),
                        _ => {}
                    }
                    let p = self.nodes[at].path.push(false);
                    return Ok(Some((sig, p, true)));
                }
                // Unread, it exports nothing yet.
                _ if defn => {
                    self.nodes[at].export = Some((Bind::Rib(Vec::new()), at));
                    return Ok(None);
                }
                _ => {}
            }
        }
        let not_one = |what: &str| FxError::at(s.at(), format!("`{}` is not a definition: a macro that makes definitions makes {what}", self.show(s)));
        let sig = match head.map(|h| (h, self.name(h))) {
            Some((h, _)) if self.m.defined.get(&h).is_some_and(|m| m.procedural.as_ref().is_some_and(|p| !p.contract)) => {
                return Err(FxError::at(s.at(), format!("`{}` is a procedural macro, whose binding structure no signature says: not in a template", self.name(h))));
            }
            // A program's `(module-parameters ((name T) … (name kind) …))`:
            // a module's values or descriptions by what each is given, which
            // only the kind's word tells (`parse::binder_is_kind`).
            Some((_, "module-parameters")) if defn && self.mode == Mode::Program && items.len() == 2 => Some(self.parameters_sig(&items[1])),
            // A `define-generative` names its conversions
            // (`docs/research/generative-types.md` §7), said so here rather
            // than as a form its signature does not fit.
            Some((_, "define-generative")) if defn && self.mode == Mode::Template && items.len() == 3 && tail.is_none() => {
                return Err(FxError::at(s.at(), "a template's `define-generative` names its conversions, `#:seal` and `#:unseal`"));
            }
            // `(define-syntax name [σ] transformer)` an expansion makes: its
            // name a binder it exports, its signature a datum, its
            // transformer a template's macro (`STy::Rules`), a `syntax-rules`
            // one in a template (a procedural one's code is phase 1's).
            Some((_, "define-syntax")) if defn && tail.is_none() && matches!(items.len(), 3 | 4) => {
                let t = items[items.len() - 1];
                let rules = t.list().and_then(|l| l.first().and_then(|h| h.sym())).is_some_and(|h| self.name(h) == "syntax-rules");
                if self.mode == Mode::Template && !rules {
                    return Err(FxError::at(t.at(), "a template's `define-syntax` defines a `syntax-rules` macro: a procedural one's transformer is phase 1's code, not yet in a template"));
                }
                let nil = Rc::new(STy::Nil);
                let mut rest = Rc::new(STy::Pair(Rc::new(STy::Rules), nil));
                if items.len() == 4 {
                    rest = Rc::new(STy::Pair(Rc::new(STy::Data), rest));
                }
                Some(Rc::new(STy::Export(Rc::new(STy::Pair(Rc::new(STy::Bvar), rest)), Bind::Rib(vec![(vec![true], Delta::Var)]))))
            }
            Some((h, n)) if defn => match self.m.defined.get(&h) {
                Some(m) if m.defn => Some(m.sig.clone()),
                Some(m) if m.desc => return Err(not_one("them by a macro that makes definitions, not a description's")),
                Some(_) => return Err(not_one("them by a macro that makes definitions, not an expression's")),
                None => match self.m.k.definitions.get(n).or_else(|| self.m.k.scope_definitions.get(n).filter(|_| self.mode == Mode::Program)) {
                    Some(sig) => Some(sig.clone()),
                    None => return Err(not_one("`define`, `define*`, `define-rec`, a `begin` of them, or a use of another such")),
                },
            },
            None if defn => return Err(not_one("`define`, `define*`, `define-rec`, a `begin` of them, or a use of another such")),
            Some((h, _)) if self.m.defined.get(&h).is_some_and(|m| m.defn) => {
                return Err(FxError::at(s.at(), format!("`{}` makes definitions, which are made at the top level, not where an expression is", self.name(h))));
            }
            Some((h, _)) if self.m.defined.get(&h).is_some_and(|m| m.desc) => {
                return Err(FxError::at(s.at(), format!("`{}` makes a description, not an expression", self.name(h))));
            }
            Some((_, n)) if self.m.k.definitions.contains_key(n) && !self.m.k.forms.contains_key(n) => {
                return Err(FxError::at(s.at(), format!("`{n}` makes a definition, made at the top level by a macro that makes definitions, not where an expression is")));
            }
            Some((_, "quasiquote")) if self.mode == Mode::Program => {
                let [_, x] = &items[..] else { return Err(FxError::at(s.at(), "`(quasiquote datum)`")) };
                let p = self.nodes[at].path.extend(&[false, true]);
                let mut kids = Vec::new();
                self.unquoted(x, p, 1, &mut kids)?;
                self.nodes[at].kids = Kids::Desc(kids);
                return Ok(None);
            }
            Some((_, "with")) if self.mode == Mode::Program && {
                let named = |m: &str| m == "#%fx" || m == "#%toplevel";
                tail.is_none() && matches!(&items[..], [_, m, n] if m.sym().is_some_and(|m| named(self.name(m))) && n.sym().is_some())
            } => return Ok(None),
            Some((_, "with")) if self.mode == Mode::Template => {
                let named = |m: &str| m == "#%fx" || m == "#%toplevel";
                let standard = tail.is_none() && matches!(&items[..], [_, m, n] if m.sym().is_some_and(|m| named(self.name(m))) && n.sym().is_some());
                if standard {
                    return Ok(None);
                }
                // `(with m name)`: the value `name` of module `m`, a
                // template's binder or a use's, the name as written; `m`'s
                // or refused, where it is checked (`Macros::projections`).
                if let (None, [_, m, n]) = (tail, &items[..])
                    && m.sym().is_some()
                    && n.sym().is_some()
                {
                    let sig = Rc::new(STy::Pair(Rc::new(STy::Id), Rc::new(STy::Pair(Rc::new(STy::Data), Rc::new(STy::Nil)))));
                    let (_, operands) = split(s).expect("a list");
                    let p = self.nodes[at].path.push(false);
                    let x = self.align(&sig, &operands, None, p)?;
                    if let Kids::Pair(m, _) = self.nodes[x].kids
                        && let Kids::Ref(n, ns, _) = self.nodes[m].kids
                    {
                        self.nodes[m].kids = Kids::Ref(n, ns, Free::Bound);
                    }
                    self.nodes[at].kids = Kids::Form(x);
                    return Ok(None);
                }
                return Err(FxError::at(s.at(), "a template's `with` is `(with module name)`, the value `name` of the module, or `(with #%fx name)` or `(with #%toplevel name)` (one opening a module over a body waits for scopes of a module's names)"));
            }
            Some((h, _)) if self.m.defined.contains_key(&h) => Some(self.m.defined[&h].sig.clone()),
            // A form the kernel has not, but `scope-forms`: in a program's
            // walk; in a template too, if it binds nothing (`bloblet-ref`,
            // `TODO.md` §247).
            Some((_, n))
                if self.m.k.scope_forms.get(n).is_some_and(|t| self.mode == Mode::Program || self.m.binds_nothing(t)) =>
            {
                Some(self.m.k.scope_forms[n].clone())
            }
            Some((_, n)) if self.m.k.forms.contains_key(n) && !n.starts_with('%') => Some(self.m.k.forms[n].clone()),
            // A program's reserved word at a list's head with no binding
            // structure of its own: a variable's name there (`else`, `read`),
            // so an application, as the checkers take it; every form they
            // parse has its entry (`tests/scopes.rs` finds one missing).
            Some((_, n)) if self.mode == Mode::Program && reserved(n) => None,
            Some((_, n)) if reserved(n) => {
                return Err(FxError::at(s.at(), format!("the prototype does not know `{n}`'s binding structure: not yet in a template")));
            }
            _ => None,
        };
        let path = self.nodes[at].path.clone();
        // A keyword at a list's head constructs, a tag written or placed.
        let construct = matches!(items[0].view(), V::Keyword(_)) || items[0].sym().and_then(|h| self.pvars.get(&h)).is_some_and(|p| matches!(&*p.core, STy::Label));
        // Aligned next, by `run`, not here: a form nested in a form takes
        // no stack.
        Ok(Some(match sig {
            _ if construct && !defn => (self.m.k.forms["%construct"].clone(), path, false),
            Some(sig) => (sig, path.push(false), true),
            None => (self.m.k.forms["%app"].clone(), path, false),
        }))
    }

    /// A macro's use at node `at`, where a form is expanded: whole, its
    /// parts not aligned; where a definition is, defining nothing the
    /// form's walk sees (what it defines is seen once it is expanded).
    fn use_whole(&mut self, at: usize, defn: bool) {
        self.nodes[at].kids = Kids::Other;
        if defn {
            self.nodes[at].export = Some((Bind::Rib(Vec::new()), at));
        }
    }

    /// Program form `s`, of signature `core`, aligned and walked, each list
    /// a macro's name heads read by its scope (`TODO.md` §295): an
    /// application where the program wrote its head (a template's is its
    /// macro, by hygiene), it is no description's, and a binder around it
    /// binds the name, or `bound` has it (the macros' names bound around
    /// `s`); else a use, `whole` (where a form is expanded) or by its
    /// signature. Read to a fixed point: aligned, walked, and each list read
    /// otherwise than it is now, with none such around it, read anew, as
    /// what binds a head is read by the lists around it alone; so each
    /// round settles at least one for good, and it ends.
    #[allow(clippy::type_complexity)]
    fn program<'a>(m: &'a Macros, interner: &'a Interner, none: &'a HashMap<Sym, PInfo>, core: &Rc<STy>, s: &Syn, whole: bool, bound: &HashSet<Sym>) -> R<(Aligner<'a>, usize, Found, Vec<(usize, Vec<Sym>)>)> {
        let mut apps: HashSet<Path> = HashSet::default();
        loop {
            let mut a = Aligner { m, interner, mode: Mode::Program, pvars: none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new(), heads: None, pending: Vec::new(), apps: Some(apps), whole };
            let root = a.align(core, s, None, Path::ROOT)?;
            let mut found = Vec::new();
            a.walk(root, &Env::default(), false, 0, &mut found, &mut Vec::new())?;
            let read = a.heads_bound(&found, bound);
            let apps_now = a.apps.as_ref().expect("read by scope");
            let changed: Vec<Path> = read.iter().filter(|(at, here)| {
                let node = &a.nodes[*at];
                let items = node.syn.list().expect("a list");
                let h = items[0].sym().expect("a macro's name");
                let app = items[0].at().expansion == 0 && !m.defined[&h].desc && (bound.contains(&h) || here.contains(&h));
                app != apps_now.contains(&node.path)
            }).map(|(at, _)| a.nodes[*at].path).collect();
            if changed.is_empty() {
                return Ok((a, root, found, read));
            }
            apps = a.apps.take().expect("read by scope");
            for p in &changed {
                if !changed.iter().any(|q| q != p && p.starts_with(*q)) && !apps.remove(p) {
                    apps.insert(*p);
                }
            }
        }
    }

    /// Each pending list, with the macros' names a binder around it binds,
    /// by the walk's `found`.
    fn heads_bound(&self, found: &Found, bound: &HashSet<Sym>) -> Vec<(usize, Vec<Sym>)> {
        let envs: HashMap<usize, &Env> = found.iter().filter(|f| self.nodes[f.0].head).map(|(i, env, ..)| (*i, env)).collect();
        let mut out = Vec::new();
        for (at, _) in &self.pending {
            let mut here: Vec<Sym> = Vec::new();
            for level in envs[at].levels() {
                let (Level::Rib(atoms) | Level::Earlier(atoms)) = level else { continue };
                for x in atoms.iter() {
                    if let Atom::Lit(b, Ns::Value) = x
                        && let Kids::Binder(n, _) = self.nodes[*b].kids
                        && self.m.defined.contains_key(&n)
                        && !bound.contains(&n)
                        && !here.contains(&n)
                    {
                        here.push(n);
                    }
                }
            }
            out.push((*at, here));
        }
        out
    }

    /// `form` of `s`, which is taken: what it aligns next, its operands
    /// moved out of it, not copied, at every form a program nests.
    fn form_owned(&mut self, at: usize, s: Syn, defn: bool) -> R<Option<Step>> {
        let Some((t, path, operands)) = self.form(at, &s, defn)? else { return Ok(None) };
        let s = if operands { split_owned(s).expect("a list").1 } else { s };
        let x = self.node_new(&t, &s, path);
        self.nodes[at].kids = Kids::Form(x);
        Ok(Some((x, t, s, x)))
    }

    /// The binding structure of a program's `module-parameters`' list
    /// `bs`: each a value's binder, its type in the scope of those before
    /// it, or a description's.
    fn parameters_sig(&self, bs: &Syn) -> Rc<STy> {
        let entry = |d| Bind::Rib(vec![(vec![true], d)]);
        let ps = bs.list().unwrap_or_default();
        let mut list = Rc::new(STy::Nil);
        for p in ps.iter().rev() {
            let one = if binder_is_kind(p, self.interner) {
                STy::Export(Rc::new(STy::Pair(Rc::new(STy::Dvar), Rc::new(STy::Data))), entry(Delta::Dvar))
            } else {
                STy::Export(Rc::new(STy::Pair(Rc::new(STy::Bvar), Rc::new(STy::Pair(Rc::new(STy::Type), Rc::new(STy::Data))))), entry(Delta::Var))
            };
            // A `union` of one, so that its addresses are from it.
            list = Rc::new(STy::Pair(Rc::new(STy::Union(vec![Rc::new(one)])), list));
        }
        let entries = (0..ps.len()).map(|k| ([vec![true], vec![false; k], vec![true]].concat(), Delta::Rib)).collect();
        // Each module not `qualified` included in the items, as the
        // checkers make the file (`Checker::modules_made`).
        let included = ps.iter().enumerate().filter(|(_, p)| !binder_is_kind(p, self.interner) && p.list().is_some_and(|l| l.len() == 2));
        let shapes = included.map(|(k, _)| Ring::Shape([vec![true], vec![false; k], vec![true, true]].concat()));
        let rings = std::iter::once(Ring::Rib(entries)).chain(shapes).collect();
        Rc::new(STy::Export(Rc::new(STy::Pair(list, Rc::new(STy::Nil))), Bind::Cage(rings)))
    }

    /// Whether `n` is a word of descriptions, written as it is: one read
    /// anywhere (`pure`, `heap`, a region constant `@r`, or a name already
    /// `#%`'s), or, `head`, one a list's head may be (`subr`, `listof`).
    fn word(&self, n: Sym, head: bool) -> bool {
        let name = self.name(n);
        name.starts_with('@') || name.starts_with("#%") || self.m.k.words.contains(name) || (head && self.m.k.heads.contains(name))
    }

    /// Description `s`, which a template writes, at node `at`, aligned name
    /// by name: each name referred to in the description namespace, the top
    /// level's if the template does not bind it (`Free::Qualified`); but a
    /// word of descriptions written as it is, a pattern variable placed, and
    /// what `poly`, `dlambda`, `mu` and `dletrec` bind in scope in what
    /// follows. Labels, a `restrict`'s names and an `io` effect's kind are
    /// written as they are; `(globals g …)`'s names and `(select m n)`'s
    /// module are values.
    fn desc(&mut self, at: usize, s: &Syn) -> R<()> {
        let fail = |why: String| FxError::at(s.at(), why);
        let items = match &s.view() {
            V::Symbol(n) => {
                self.nodes[at].kids = if self.pvars.contains_key(n) {
                    Kids::PVar(*n)
                } else if self.word(*n, false) {
                    Kids::Other
                } else {
                    Kids::Ref(*n, Ns::Desc, Free::Qualified)
                };
                return Ok(());
            }
            V::List { items, tail: None } => items.clone(),
            V::List { .. } => return Err(fail("a description is a list, not a dotted one".into())),
            _ => return Ok(()),
        };
        // A macro's use: its operands aligned with its signature, if it
        // makes a description.
        if let Some(h) = items[0].sym().filter(|h| !self.pvars.contains_key(h))
            && let Some(m) = self.m.defined.get(&h)
        {
            // Where a form is expanded, a use whole, as in `form`.
            if self.whole && m.desc {
                self.nodes[at].head = true;
                self.pending.push((at, false));
                self.use_whole(at, false);
                return Ok(());
            }
            if !m.desc {
                let what = if m.defn { "definitions" } else { "an expression" };
                return Err(fail(format!("`{}` makes {what}, not a description", self.name(h))));
            }
            let (sig, (_, operands)) = (m.sig.clone(), split(s).expect("a list"));
            let p = self.nodes[at].path.push(false);
            let x = self.align(&sig, &operands, None, p)?;
            self.nodes[at].kids = Kids::Form(x);
            return Ok(());
        }
        let head = items[0].sym().filter(|h| !self.pvars.contains_key(h)).map(|h| self.name(h).to_string());
        let kids = self.desc_kids(at, &items);
        match head.as_deref() {
            Some("poly" | "dlambda") if self.mode == Mode::Program && items.len() > 3 => {
                let atoms = self.desc_binders(kids[1], &items[1])?;
                for (k, i) in kids[2..].iter().zip(&items[2..]) {
                    self.desc_scoped(*k, i, atoms.clone())?;
                }
                Ok(())
            }
            Some(h @ ("poly" | "dlambda")) => {
                let [_, bs, body] = &items[..] else {
                    return Err(fail(format!("`({h} ((name kind) …) description)`")));
                };
                let atoms = self.desc_binders(kids[1], bs)?;
                self.desc_scoped(kids[2], body, atoms)
            }
            Some("mu") => {
                let [_, n, body] = &items[..] else {
                    return Err(fail("`(mu name type)`".into()));
                };
                let a = self.desc_binder(kids[1], n)?;
                self.desc_scoped(kids[2], body, vec![a])
            }
            // Each name in scope in each description and the body.
            Some("dletrec") => {
                let [_, bs, body] = &items[..] else {
                    return Err(fail("`(dletrec ((name description) …) description)`".into()));
                };
                let entries = bs.list().map(|l| l.to_vec()).unwrap_or_default();
                let ek = self.desc_kids(kids[1], &entries);
                let (mut atoms, mut parts) = (Vec::new(), Vec::new());
                for (k, e) in ek.iter().zip(&entries) {
                    let listed = e.list();
                    let Some([n, d]) = listed.as_deref() else {
                        return Err(FxError::at(e.at(), "`(name description)`"));
                    };
                    let p = self.desc_kids(*k, &[n.clone(), d.clone()]);
                    atoms.push(self.desc_binder(p[0], n)?);
                    parts.push((p[1], d.clone()));
                }
                for (k, d) in parts {
                    self.desc_scoped(k, &d, atoms.clone())?;
                }
                self.desc_scoped(kids[2], body, atoms)
            }
            // `(label type)`s.
            Some("productof" | "sumof") => {
                for (k, f) in kids[1..].iter().zip(&items[1..]) {
                    let listed = f.list();
                    let Some([label, ty]) = listed.as_deref() else {
                        // A program's flat sum's tag type, `(sumof u8 …)`.
                        if self.mode == Mode::Program {
                            self.desc(*k, f)?;
                            continue;
                        }
                        return Err(FxError::at(f.at(), "`(label type)`"));
                    };
                    let p = self.desc_kids(*k, &[label.clone(), ty.clone()]);
                    // A label a use gives, placed.
                    if let Some(n) = label.sym().filter(|n| self.pvars.contains_key(n)) {
                        self.nodes[p[0]].core = Rc::new(STy::Label);
                        self.nodes[p[0]].kids = Kids::PVar(n);
                    }
                    self.desc(p[1], ty)?;
                }
                Ok(())
            }
            Some("restrict") if items.len() >= 2 => self.desc(kids[1], &items[1]),
            // A file's module type, given descriptions and module values,
            // which a name alone does not tell apart: the checker decides
            // by what binds it, so a program's walk leaves the names
            // unplaced (`binding-shapes.md`, step 3, decides them by shape).
            Some("load-moduleof" | "load-input-moduleof") if self.mode == Mode::Program => {
                for i in &items[2..] {
                    self.symbols_into(i);
                }
                Ok(())
            }
            Some("io") => Ok(()),
            // Values: a global's name, written as it is, since no local can
            // shadow it; a module's, the top level's.
            Some(h @ ("globals" | "select")) => {
                let names: &[usize] = if h == "select" { &kids[1..kids.len().min(2)] } else { &kids[1..] };
                let free = if h == "select" { Free::Qualified } else { Free::Plain };
                for &k in names {
                    let syn = self.nodes[k].syn.clone();
                    if h == "select" && syn.sym().is_none() {
                        self.select_path(k, &syn)?;
                        continue;
                    }
                    let Some(n) = syn.sym() else {
                        return Err(FxError::at(syn.at(), "a name"));
                    };
                    self.nodes[k].core = Rc::new(STy::Id);
                    self.nodes[k].kids = if self.pvars.contains_key(&n) { Kids::PVar(n) } else { Kids::Ref(n, Ns::Value, free) };
                }
                Ok(())
            }
            // Each member's type in the scope of the abstract and
            // transparent types before it, a value's name a label. An
            // `abs`'s or `desc`'s label written as a keyword is apart from
            // its binder, after it, `(abs #:t u type)`: a template's labels
            // are written so, as labels in templates are, or are names a use
            // gives (`typed-macros.md`, "a `moduleof`'s label and binder
            // written apart").
            Some("moduleof") => {
                let template = self.mode != Mode::Program;
                let mut atoms = Vec::new();
                for (k, m) in kids[1..].iter().zip(&items[1..]) {
                    let parts = m.list().map(|l| l.to_vec()).unwrap_or_default();
                    let word = parts.first().and_then(|h| h.sym()).map(|h| self.name(h).to_string());
                    if parts.len() < 2 {
                        self.desc(*k, m)?;
                        continue;
                    }
                    let p = self.desc_kids(*k, &parts);
                    let binds = matches!(word.as_deref(), Some("abs" | "desc"));
                    let keyword = matches!(parts[1].view(), V::Keyword(_));
                    let apart = binds && keyword && parts.len() == 4 && parts[2].sym().is_some();
                    let given = parts[1].sym().filter(|n| self.pvars.contains_key(n));
                    if template && !keyword && given.is_none() {
                        return match (binds, parts[1].sym()) {
                            (_, None) => Err(FxError::at(parts[1].at(), "a list of names in a template's `moduleof`: not yet")),
                            (true, Some(_)) => Err(FxError::at(parts[1].at(), "a template's `abs` or `desc` writes its label as a keyword, its binder after it: `(abs #:t t type)`")),
                            (false, Some(_)) => Err(FxError::at(parts[1].at(), "a template's `val` writes its label as a keyword: `(val #:x type)`")),
                        };
                    }
                    // A value's label a use gives, placed.
                    if let (Some(n), false) = (given, binds) {
                        self.nodes[p[1]].core = Rc::new(STy::Label);
                        self.nodes[p[1]].kids = Kids::PVar(n);
                    }
                    // An `abs`'s last part is a kind, of words alone: not a
                    // description, nothing in it named.
                    let first = if apart { 3 } else { 2 };
                    if word.as_deref() != Some("abs") {
                        for (q, x) in p[first..].iter().zip(&parts[first..]) {
                            self.desc_scoped(*q, x, atoms.clone())?;
                        }
                    }
                    if apart {
                        atoms.push(self.desc_binder(p[2], &parts[2])?);
                    } else if binds && parts[1].sym().is_some() {
                        atoms.push(self.desc_binder(p[1], &parts[1])?);
                    }
                }
                Ok(())
            }
            Some("subr" | "->" | "->*") => self.desc_subr(s, &items, &kids),
            Some(_) if self.word(items[0].sym().expect("a name"), true) => {
                for (k, i) in kids[1..].iter().zip(&items[1..]) {
                    self.desc(*k, i)?;
                }
                Ok(())
            }
            // A description function applied, its name the head.
            _ => {
                for (k, i) in kids.iter().zip(&items) {
                    self.desc(*k, i)?;
                }
                Ok(())
            }
        }
    }

    /// A procedure type, `(subr …)`, `(-> …)` or `(->* …)`, its parts `items`
    /// at nodes `kids`: each parameter named, `(x : T)`, a value's binder in
    /// scope in the types after it, the result and the specification's
    /// clauses (`Checker::parse_subr_type`, `specified`), and a repeated
    /// one's in its own type only as the repetitions before it bound it,
    /// which a name cannot say; `(ensures r Q)`'s `r` in scope in `Q`. A
    /// `(bool …)` result's propositions are written as they are.
    fn desc_subr(&mut self, s: &Syn, items: &[Syn], kids: &[usize]) -> R<()> {
        let clause = |c: &Self, x: &Syn| x.list().and_then(|l| l.first().copied()).and_then(|h| h.sym()).is_some_and(|h| matches!(c.name(h), "requires" | "ensures"));
        let plain = items.len() - items.iter().rev().take_while(|c| clause(self, c)).count();
        if plain < 3 || kids.len() != items.len() {
            return Err(FxError::at(s.at(), "`(subr effect (param …) result)` or `(-> (param …) result)`, then a specification's clauses"));
        }
        let (pi, ri) = (plain - 2, plain - 1);
        for i in 1..pi {
            self.desc(kids[i], &items[i])?;
        }
        let mut atoms = Vec::new();
        if !matches!(items[pi].view(), V::Nil) {
            let Some(ps) = items[pi].list().map(|l| l.to_vec()) else {
                return Err(FxError::at(items[pi].at(), "a procedure type's parameters are a list"));
            };
            let pk = self.desc_kids(kids[pi], &ps);
            for (k, p) in pk.iter().zip(&ps) {
                let named = p.list().filter(|q| q.len() == 3 && q[1].sym().is_some_and(|c| self.name(c) == ":")).map(|q| q.to_vec());
                let Some(parts) = named else {
                    self.desc_scoped(*k, p, atoms.clone())?;
                    continue;
                };
                let q = self.desc_kids(*k, &parts);
                let a = self.value_binder(q[0], &parts[0])?;
                self.nodes[q[2]].imports.push((Bind::Direct(atoms.clone()), q[2]));
                if self.nodes[*k].repeated {
                    self.nodes[q[2]].imports.push((Bind::Earlier(vec![a.clone()]), q[2]));
                }
                self.desc(q[2], &parts[2])?;
                atoms.push(a);
            }
        }
        let result = &items[ri];
        if result.list().and_then(|l| l.first().copied()).and_then(|h| h.sym()).is_some_and(|h| self.name(h) == "bool" && !self.pvars.contains_key(&h)) {
            if let Some(n) = self.pvar_in(result) {
                return Err(FxError::at(result.at(), format!("pattern variable `{}` in a `(bool …)` result's propositions: not yet", self.name(n))));
            }
        } else {
            self.desc_scoped(kids[ri], result, atoms.clone())?;
        }
        for (k, c) in kids[plain..].iter().zip(&items[plain..]) {
            let parts = c.list().expect("a clause").to_vec();
            let q = self.desc_kids(*k, &parts);
            match (self.name(parts[0].sym().expect("a clause")), &q[..]) {
                ("requires", [_, p]) => {
                    self.nodes[*p].imports.push((Bind::Direct(atoms.clone()), *p));
                    self.spec(*p, &parts[1])?;
                }
                ("ensures", [_, r, p]) => {
                    let mut scope = atoms.clone();
                    scope.push(self.value_binder(*r, &parts[1])?);
                    self.nodes[*p].imports.push((Bind::Direct(scope), *p));
                    self.spec(*p, &parts[2])?;
                }
                _ => return Err(FxError::at(c.at(), "a specification is `(requires proposition)`, then `(ensures name proposition)`")),
            }
        }
        Ok(())
    }

    /// A value's binder `n` a description writes (a procedure type's
    /// parameter named, its result's name), at node `at`: a pattern variable
    /// (a `bvar` the use gives), or a name the template binds; what it binds.
    fn value_binder(&mut self, at: usize, n: &Syn) -> R<Atom> {
        self.nodes[at].core = Rc::new(STy::Bvar);
        match n.sym() {
            Some(m) if self.pvars.contains_key(&m) => {
                self.nodes[at].kids = Kids::PVar(m);
                Ok(Atom::Var(m, Ns::Value, 0))
            }
            Some(m) if !reserved(self.name(m)) && !self.word(m, false) => {
                self.nodes[at].kids = Kids::Binder(m, Ns::Value);
                Ok(Atom::Lit(at, Ns::Value))
            }
            _ => Err(FxError::at(n.at(), format!("`{}` is not a name that may be bound", self.show(n)))),
        }
    }

    /// A specification's proposition or integer `s`, at node `at`
    /// (`Checker::spec_prop`, `spec_expr`): each name a value's, a
    /// parameter's or the result's, which the template binds or a use
    /// gives, else the top level's (which the checkers refuse there); a
    /// call's head a global procedure's, written as it is, as a
    /// `(globals …)`'s names are (a local of its name where the macro is
    /// used is refused, not taken: `Checker::spec_callee`); the logic's
    /// words, numbers, `#t` and `#f` as they are.
    fn spec(&mut self, at: usize, s: &Syn) -> R<()> {
        let name = |c: &mut Self, at: usize, n: Sym, free: Free| {
            c.nodes[at].core = Rc::new(STy::Id);
            c.nodes[at].kids = if c.pvars.contains_key(&n) { Kids::PVar(n) } else { Kids::Ref(n, Ns::Value, free) };
        };
        match &s.view() {
            V::Symbol(n) => name(self, at, *n, Free::Qualified),
            V::List { items, tail: None } => {
                let kids = self.desc_kids(at, items);
                match items[0].sym() {
                    Some(h) if !self.pvars.contains_key(&h) && matches!(self.name(h), "<" | "<=" | "=" | ">" | ">=" | "not" | "and" | "or" | "implies" | "+" | "-" | "*") => {}
                    Some(h) => name(self, kids[0], h, Free::Plain),
                    None => return Err(FxError::at(s.at(), "a specification's proposition or integer")),
                }
                for (k, i) in kids[1..].iter().zip(&items[1..]) {
                    self.spec(*k, i)?;
                }
            }
            V::List { .. } => return Err(FxError::at(s.at(), "a specification's proposition is a list, not a dotted one")),
            _ => {}
        }
        Ok(())
    }

    /// A node for each of `items`, the parts of the list at node `at`, at
    /// their paths in it: `at`'s kids.
    fn desc_kids(&mut self, at: usize, items: &[Syn]) -> Vec<usize> {
        let mut path = self.nodes[at].path;
        let mut kids = Vec::new();
        // `p ...` last: `p` repeated, the `...` no part of its own.
        let repeated = items.len() >= 2 && is_ellipsis(&items[items.len() - 1], self.interner);
        let items = if repeated { &items[..items.len() - 1] } else { items };
        for i in items {
            kids.push(self.nodes.len());
            self.nodes.push(Node { syn: i.clone(), path: path.push(true), core: Rc::new(STy::Type), imports: Vec::new(), export: None, many: false, hole: None, desc: false, repeated: false, head: false, kids: Kids::Other });
            path = path.push(false);
        }
        if repeated && let Some(&k) = kids.last() {
            self.nodes[k].repeated = true;
        }
        self.nodes[at].kids = Kids::Desc(kids.clone());
        kids
    }

    /// A `select`'s module at node `at`: a name, as above, or a path to a
    /// module, `(with m x)`, its base `m` read as a `select`'s module is
    /// and `x` the label of a value of it (`docs/fx26.md`, "A *path* to a
    /// module").
    fn select_path(&mut self, at: usize, s: &Syn) -> R<()> {
        if let Some(n) = s.sym() {
            self.nodes[at].core = Rc::new(STy::Id);
            self.nodes[at].kids = if self.pvars.contains_key(&n) { Kids::PVar(n) } else { Kids::Ref(n, Ns::Value, Free::Qualified) };
            return Ok(());
        }
        let items = match &s.view() {
            V::List { items, tail: None } => items.clone(),
            _ => Vec::new(),
        };
        let is_path = matches!(&items[..], [h, _, x] if h.sym().is_some_and(|h| self.name(h) == "with") && x.sym().is_some());
        if !is_path {
            return Err(FxError::at(s.at(), "a module's name, or a path to one, `(with module name)`"));
        }
        let kids = self.desc_kids(at, &items);
        self.select_path(kids[1], &items[1])
    }

    /// Description `s` at node `at`, in the scope of `atoms`.
    fn desc_scoped(&mut self, at: usize, s: &Syn, atoms: Vec<Atom>) -> R<()> {
        self.nodes[at].imports.push((Bind::Direct(atoms), at));
        self.desc(at, s)
    }

    /// A description's binder `n`, at node `at`: a pattern variable (a
    /// `dvar` the use gives), or a name the template binds; what it binds.
    fn desc_binder(&mut self, at: usize, n: &Syn) -> R<Atom> {
        self.nodes[at].core = Rc::new(STy::Dvar);
        match n.sym() {
            Some(m) if self.pvars.contains_key(&m) => {
                self.nodes[at].kids = Kids::PVar(m);
                Ok(Atom::Var(m, Ns::Desc, 0))
            }
            Some(m) if self.mode == Mode::Program || (!reserved(self.name(m)) && !self.word(m, false)) => {
                self.nodes[at].kids = Kids::Binder(m, Ns::Desc);
                Ok(Atom::Lit(at, Ns::Desc))
            }
            _ => Err(FxError::at(n.at(), format!("`{}` is not a name that may be bound", self.show(n)))),
        }
    }

    /// `((name kind) …)` at node `at`, a binder's place or `distinct` third
    /// if any, each in the scope of those before it: what they bind.
    fn desc_binders(&mut self, at: usize, bs: &Syn) -> R<Vec<Atom>> {
        let entries = bs.list().map(|l| l.to_vec()).unwrap_or_default();
        let ek = self.desc_kids(at, &entries);
        let mut atoms = Vec::new();
        for (k, e) in ek.iter().zip(&entries) {
            let parts = e.list().map(|l| l.to_vec()).unwrap_or_default();
            let ([n, _] | [n, _, _]) = &parts[..] else {
                return Err(FxError::at(e.at(), "a binder is `(name kind)`"));
            };
            let p = self.desc_kids(*k, &parts);
            let a = self.desc_binder(p[0], n)?;
            if let Some(third) = parts.get(2) {
                self.desc_scoped(p[2], third, atoms.clone())?;
            }
            atoms.push(a);
        }
        Ok(atoms)
    }

    /// The binders of the `poly`s at the top of the description at node
    /// `at`, outermost first (`Checker::bind_signature`'s).
    fn poly_binders(&self, at: usize) -> Vec<Atom> {
        let mut out = Vec::new();
        let mut at = at;
        loop {
            let Kids::Desc(kids) = &self.nodes[at].kids else { return out };
            let is_poly = self.nodes[at].syn.list().and_then(|l| l.first().copied()).and_then(|h| h.sym()).is_some_and(|h| self.name(h) == "poly" && !self.pvars.contains_key(&h));
            if !is_poly || kids.len() != 3 {
                return out;
            }
            if let Kids::Desc(entries) = &self.nodes[kids[1]].kids {
                for e in entries {
                    if let Kids::Desc(parts) = &self.nodes[*e].kids {
                        match self.nodes[parts[0]].kids {
                            Kids::PVar(n) => out.push(Atom::Var(n, Ns::Desc, 0)),
                            Kids::Binder(..) => out.push(Atom::Lit(parts[0], Ns::Desc)),
                            _ => {}
                        }
                    }
                }
            }
            at = kids[2];
        }
    }

    /// The binder node that binds a reference to `n`, of namespace `ns`, in
    /// environment `env`, the innermost: in a program's walk, a binder is
    /// its node (`Atom::Lit`). None if the reference is free there.
    fn bound_by(&self, env: &Env, n: Sym, ns: Ns) -> Option<usize> {
        for level in env.to_vec() {
            let (Level::Rib(atoms) | Level::Earlier(atoms)) = &level else { continue };
            for x in atoms.iter() {
                match x {
                    Atom::Lit(i, _) if matches!(self.nodes[*i].kids, Kids::Binder(m, d) if m == n && d == ns) => return Some(*i),
                    Atom::Var(b, d, _) if *b == n && *d == ns => return Some(usize::MAX),
                    _ => {}
                }
            }
        }
        None
    }

    /// Whether `h`, at a list's head in a template, may be a name a `(syntax
    /// σ)` entry binds: no macro's, form's or trailmark's, and no pattern
    /// variable's but a binder's.
    fn unknown_head(&self, h: Sym) -> bool {
        let n = self.name(h);
        let k = &self.m.k;
        match self.pvars.get(&h) {
            Some(p) => matches!(&*p.core, STy::Bvar),
            None => {
                !reserved(n)
                    && !self.m.defined.contains_key(&h)
                    && self.m.mark_of(h).is_none()
                    && !k.forms.contains_key(n)
                    && !k.definitions.contains_key(n)
                    && !k.scope_forms.contains_key(n)
                    && !k.scope_definitions.contains_key(n)
            }
        }
    }

    /// How each pending list is read by the scopes the walk found, `found`:
    /// a use of a macro if its head's innermost binder is what a `(macro σ made)`
    /// entry binds, a pattern variable or a template's binder at that part
    /// of a use; else an application. Each with its node, and its binder if
    /// a template's.
    fn heads_read(&self, found: &Found) -> R<Vec<(usize, Head, Option<usize>)>> {
        let mut by_pvar: HashMap<Sym, Kept> = HashMap::default();
        let mut by_node: HashMap<usize, Kept> = HashMap::default();
        for node in &self.nodes {
            let Some((Bind::Rib(es), root)) = &node.export else { continue };
            for (addr, d) in es {
                let Delta::Syntax(k) = d else { continue };
                let t = self.nav(*root, addr, node.syn.at())?;
                match self.nodes[t].kids {
                    Kids::PVar(n) => _ = by_pvar.insert(n, *k),
                    Kids::Binder(_, Ns::Value) => _ = by_node.insert(t, *k),
                    _ => {}
                }
            }
        }
        let envs: HashMap<usize, &Env> = found.iter().map(|(i, env, ..)| (*i, env)).collect();
        let mut out = Vec::new();
        for (at, _) in &self.pending {
            let h = self.nodes[*at].syn.list().and_then(|l| l.first().and_then(|h| h.sym())).expect("a head");
            let mut read = (Head::Application, None);
            'levels: for level in envs[at].levels() {
                let (Level::Rib(atoms) | Level::Earlier(atoms)) = level else { continue };
                for x in atoms.iter() {
                    match x {
                        Atom::Var(m, Ns::Value, _) if *m == h => {
                            read = (by_pvar.get(m).map_or(Head::Application, |k| Head::Macro(*k)), None);
                            break 'levels;
                        }
                        Atom::Lit(b, Ns::Value) if matches!(self.nodes[*b].kids, Kids::Binder(m, _) if m == h) => {
                            read = (by_node.get(b).map_or(Head::Application, |k| Head::Macro(*k)), Some(*b));
                            break 'levels;
                        }
                        _ => {}
                    }
                }
            }
            out.push((*at, read.0, read.1));
        }
        Ok(out)
    }

    /// A pattern variable written somewhere inside `s`.
    fn pvar_in(&self, s: &Syn) -> Option<Sym> {
        match &s.view() {
            V::Symbol(n) if self.pvars.contains_key(n) => Some(*n),
            V::List { items, tail } => items.iter().chain(tail.as_ref()).find_map(|x| self.pvar_in(x)),
            _ => None,
        }
    }

    fn show(&self, s: &Syn) -> String {
        s.written(self.interner)
    }

    /// The tree under `at`, walked with environment `env` (innermost first):
    /// each pattern variable, template binder and name referred to, with
    /// the environment where it is, and whether it is in a part of the
    /// signature that is `(many …)` (`many`, of what is around it).
    fn walk(&self, at: usize, env: &Env, many: bool, depth: usize, found: &mut Found, seqs: &mut Vec<(usize, usize)>) -> R<()> {
        // A list's rest in a loop, so that a long list takes no stack.
        let (mut at, mut env, mut many, mut depth) = (at, env.clone(), many, depth);
        loop {
            let node = &self.nodes[at];
            many = many || node.many;
            depth += usize::from(node.repeated);
            if node.repeated {
                seqs.push((at, depth));
            }
            for (b, root) in &node.imports {
                env = env.within(self.eval(b, *root, node.syn.at())?);
            }
            if node.head {
                found.push((at, env.clone(), many, depth));
            }
            match &node.kids {
                Kids::Pair(x, y) => {
                    self.walk(*x, &env, many, depth, found, seqs)?;
                    at = *y;
                }
                Kids::Form(x) | Kids::Seq(x, false) => at = *x,
                // An element of a ribcage's list, in the scope of what the
                // repetitions before it bound.
                Kids::Seq(x, true) => {
                    let mut levels: Vec<Level> = Vec::new();
                    let mut earlier = Vec::new();
                    for l in self.levels_of(*x, node.syn.at())? {
                        match l {
                            Level::Rib(atoms) | Level::Earlier(atoms) => earlier.extend(atoms.iter().cloned()),
                            Level::Cage(n) => levels.push(Level::Cage(n)),
                            Level::Shape(n) => levels.push(Level::Shape(n)),
                        }
                    }
                    levels.insert(0, Level::Earlier(Rc::new(earlier)));
                    env = env.within(levels);
                    at = *x;
                }
                Kids::Desc(kids) => {
                    for k in kids {
                        self.walk(*k, &env, many, depth, found, seqs)?;
                    }
                    return Ok(());
                }
                Kids::PVar(_) | Kids::Binder(..) | Kids::Ref(..) => {
                    found.push((at, env, many, depth));
                    return Ok(());
                }
                Kids::Nil | Kids::Other => return Ok(()),
            }
        }
    }

    /// What `b` binds, its addresses from `root`: levels, innermost first.
    fn eval(&self, b: &Bind, root: usize, span: At) -> R<Vec<Level>> {
        match b {
            Bind::Rib(entries) => Ok(vec![Level::Rib(Rc::new(self.rib(entries, root, span)?))]),
            Bind::Direct(atoms) => Ok(vec![Level::Rib(Rc::new(atoms.clone()))]),
            Bind::Earlier(atoms) => Ok(vec![Level::Earlier(Rc::new(atoms.clone()))]),
            Bind::Shape(addr) => Ok(vec![Level::Shape(self.nav(root, addr, span)?)]),
            // A part's own cage, in place, in a loop: a list's ribcage, each
            // element's then the rest's, takes no stack.
            Bind::Cage(rings) => {
                let mut out = Vec::new();
                let mut work: Vec<(&Ring, usize)> = rings.iter().rev().map(|r| (r, root)).collect();
                while let Some((r, root)) = work.pop() {
                    match r {
                        Ring::Rib(entries) => out.push(Level::Rib(Rc::new(self.rib(entries, root, span)?))),
                        Ring::Shape(addr) => out.push(Level::Shape(self.nav(root, addr, span)?)),
                        Ring::At(addr) => {
                            let t = self.nav(root, addr, span)?;
                            match (&self.nodes[t].kids, &self.exported(t).export) {
                                (Kids::PVar(_) | Kids::Seq(..), _) => out.extend(self.levels_of(t, span)?),
                                (_, Some((Bind::Cage(rs), r))) => work.extend(rs.iter().rev().map(|x| (x, *r))),
                                _ => out.extend(self.levels_of(t, span)?),
                            }
                        }
                    }
                }
                Ok(out)
            }
        }
    }

    /// What rib `entries` binds, its addresses from `root`: a part's own
    /// rib in place, in a loop, so that a list's (each element's, then the
    /// rest's) takes no stack.
    fn rib(&self, entries: &[(Addr, Delta)], root: usize, span: At) -> R<Vec<Atom>> {
        let mut out = Vec::new();
        let mut work: Vec<(&[(Addr, Delta)], usize)> = vec![(entries, root)];
        while let Some((es, root)) = work.pop() {
            let Some(((addr, delta), rest)) = es.split_first() else { continue };
            work.push((rest, root));
            let t = self.nav(root, addr, span)?;
            let node = &self.nodes[t];
            let value = !matches!(&*node.core, STy::Dvar);
            match (delta, &node.kids) {
                (Delta::None, _) => {}
                (Delta::Var | Delta::Syntax(_), Kids::PVar(n)) if value => out.push(Atom::Var(*n, Ns::Value, 0)),
                (Delta::Var | Delta::Syntax(_), Kids::Binder(_, Ns::Value)) => out.push(Atom::Lit(t, Ns::Value)),
                (Delta::Var | Delta::Syntax(_), _) => return Err(FxError::at(node.syn.at(), "the signature says a value's binder is here")),
                (Delta::Dvar | Delta::Place, Kids::PVar(n)) if !value => {
                    out.push(Atom::Var(*n, Ns::Desc, 0));
                    if *delta == Delta::Place {
                        out.push(Atom::Var(*n, Ns::Value, 0));
                    }
                }
                (Delta::Dvar | Delta::Place, Kids::Binder(_, Ns::Desc)) => {
                    out.push(Atom::Lit(t, Ns::Desc));
                    if *delta == Delta::Place {
                        out.push(Atom::Lit(t, Ns::Value));
                    }
                }
                (Delta::Dvar | Delta::Place, _) => return Err(FxError::at(node.syn.at(), "the signature says a description's binder is here")),
                // A use's description: what its own `poly`s bind is the
                // use's, which nothing the template writes can name.
                (Delta::Rib, Kids::PVar(_)) if matches!(&*node.core, STy::Type) => {}
                (Delta::Rib, Kids::PVar(n)) => out.push(Atom::RibOf(*n)),
                (Delta::Rib, Kids::Seq(..)) => match &self.exported(t).export {
                    Some((Bind::Rib(es), r)) => out.extend(self.gathered(t, self.rib(es, *r, span)?)),
                    Some((Bind::Direct(atoms), _)) => out.extend(atoms.iter().cloned()),
                    _ => return Err(FxError::at(node.syn.at(), "the signature says what is here exports a rib, and it exports none")),
                },
                (Delta::Rib, _) => match &self.exported(t).export {
                    Some((Bind::Rib(es), r)) => work.push((es, *r)),
                    Some((Bind::Direct(atoms), _)) => out.extend(atoms.iter().cloned()),
                    // A use of a macro that makes definitions: none the
                    // template sees.
                    None if matches!(node.kids, Kids::Form(_)) => {}
                    _ => return Err(FxError::at(node.syn.at(), "the signature says what is here exports a rib, and it exports none")),
                },
                (Delta::Env, _) => return Err(FxError::at(node.syn.at(), "a ribcage (`env`) in a rib: write it `(at ℓ)` in a `cage`")),
            }
        }
        Ok(out)
    }

    fn levels_of(&self, t: usize, span: At) -> R<Vec<Level>> {
        let node = &self.nodes[t];
        match (&node.kids, &self.exported(t).export) {
            (Kids::PVar(n), _) => Ok(vec![Level::Cage(*n)]),
            (_, Some((b, r))) => Ok(self.gathered_levels(t, self.eval(b, *r, span)?)),
            // A ribcage's list by ellipsis: what each element exports.
            (Kids::Seq(e, true), None) => Ok(self.gathered_levels(t, self.levels_of(*e, span)?)),
            (Kids::Form(_), None) => Ok(Vec::new()),
            _ => Err(FxError::at(node.syn.at(), "the signature says what is here exports a ribcage, and it exports none")),
        }
    }

    /// Atoms `atoms` that node `t` exports: if `t` is a list by ellipsis,
    /// what its elements export, every repetition's.
    fn gathered(&self, t: usize, atoms: Vec<Atom>) -> Vec<Atom> {
        let Kids::Seq(e, _) = self.nodes[t].kids else { return atoms };
        if self.nodes[t].export.as_ref().is_some_and(|(_, r)| *r != e) {
            return atoms;
        }
        atoms
            .into_iter()
            .map(|a| match a {
                Atom::Var(n, ns, g) => Atom::Var(n, ns, g + 1),
                other => other,
            })
            .collect()
    }

    fn gathered_levels(&self, t: usize, levels: Vec<Level>) -> Vec<Level> {
        levels
            .into_iter()
            .map(|l| match l {
                Level::Rib(atoms) => Level::Rib(Rc::new(self.gathered(t, Rc::unwrap_or_clone(atoms)))),
                Level::Earlier(atoms) => Level::Earlier(Rc::new(self.gathered(t, Rc::unwrap_or_clone(atoms)))),
                cage => cage,
            })
            .collect()
    }

    /// Each template binder under node `at`, with `m`, the macro whose use
    /// it is in, onto `out`.
    fn binders_under(&self, at: usize, m: Sym, out: &mut Vec<(Sym, Sym)>) {
        match self.nodes[at].kids {
            Kids::Pair(x, y) => {
                self.binders_under(x, m, out);
                self.binders_under(y, m, out);
            }
            Kids::Form(x) | Kids::Seq(x, _) => self.binders_under(x, m, out),
            Kids::Desc(ref kids) => {
                for k in kids {
                    self.binders_under(*k, m, out);
                }
            }
            Kids::Binder(n, Ns::Value) => out.push((n, m)),
            _ => {}
        }
    }

    /// The nodes under node `at`, itself first, each before what is under
    /// it.
    fn under(&self, at: usize) -> Vec<usize> {
        let mut out = vec![at];
        match &self.nodes[at].kids {
            Kids::Pair(x, y) => {
                out.extend(self.under(*x));
                out.extend(self.under(*y));
            }
            Kids::Form(x) | Kids::Seq(x, _) => out.extend(self.under(*x)),
            Kids::Desc(kids) => kids.iter().for_each(|k| out.extend(self.under(*k))),
            _ => {}
        }
        out
    }

    /// The node whose export is what node `t` exports: a form's operands'
    /// (a definition's), else its own.
    fn exported(&self, t: usize) -> &Node {
        match self.nodes[t].kids {
            Kids::Form(x) => &self.nodes[x],
            _ => &self.nodes[t],
        }
    }

    fn nav(&self, root: usize, addr: &Addr, span: At) -> R<usize> {
        let mut at = root;
        for step in addr {
            match &self.nodes[at].kids {
                Kids::Pair(x, y) => at = if *step { *x } else { *y },
                Kids::PVar(n) => return Err(FxError::at(span, format!("an address into pattern variable `{}`: the prototype names a part only where the pattern names it", self.name(*n)))),
                _ => return Err(FxError::at(span, "an address to no part")),
            }
        }
        Ok(at)
    }

    /// Pattern variable `n`, of `info`, placed in the template where type
    /// `want` is, in environment `env`: Herman's rules.
    fn placed(&self, n: Sym, info: &PInfo, want: &Rc<STy>, env: &[Level], span: At) -> R<()> {
        use STy::*;
        let name = self.name(n);
        let have = &info.core;
        let want_u = self.m.unfold(want);
        let fits = match (&**have, &*want_u) {
            (Bvar, Bvar) | (Dvar, Dvar) => return Ok(()),
            // A pattern's binder referred to, a value's or a description's.
            (Bvar, Expr | Id) => return self.in_scope(n, Ns::Value, env, span),
            (Dvar, Type) => return self.in_scope(n, Ns::Desc, env, span),
            // A place's binder, referred to as the value it also binds.
            (Dvar, Expr | Id) => return self.in_scope(n, Ns::Value, env, span),
            (Expr, Expr) | (Id, Expr | Id) | (Lambda, Lambda | Expr) => true,
            // An untyped part where a lambda is wanted: it promises nothing,
            // and its uses' expansions are checked; a typed hole says it is
            // a lambda (`typed-macros.md`, "Typed holes": two tiers).
            (Expr, Lambda) if info.hole.is_some() => {
                return Err(FxError::at(span, format!("`{name}` is placed where a lambda is wanted: a typed hole there is a lambda, `(lambda #:type T)`")));
            }
            (Expr, Lambda) => true,
            (Data, Data) | (Type, Type) | (Label, Label) | (Kind, Kind) => return Ok(()),
            // In a macro the template defines, whose own check is the
            // defined macro's, where it is defined.
            (_, Rules) => true,
            (Expr | Id | Data | Type | Label | Bvar | Dvar | Kind | Lambda | Defn, _) | (_, Expr | Id | Data | Type | Label | Bvar | Dvar | Kind | Lambda | Defn) => false,
            _ => self.m.sub(have, want, &mut Vec::new()),
        };
        if !fits {
            return Err(FxError::at(span, format!("`{name}` is placed where its syntax type is not one the form takes there")));
        }
        if normal(env) != normal(&info.declared) {
            let (found, said) = (self.scope_said(env), self.scope_said(&info.declared));
            return Err(FxError::at(span, format!("`{name}` is placed in {found}, but its signature says it is in {said}")));
        }
        Ok(())
    }

    /// Environment `env` as a refusal says it (Heist's should-work note,
    /// entry 2): its levels outermost first, each by the pattern's binders
    /// it holds, `x`, `(x ...)` every repetition's, a rib's in the order of
    /// their names; as `macros-scopes.fx`'s `scope-said`.
    fn scope_said(&self, env: &[Level]) -> String {
        let levels: Vec<String> = normal(env)
            .iter()
            .rev()
            .filter_map(|l| match l {
                Level::Rib(atoms) => Some(self.atoms_said(atoms)),
                Level::Earlier(atoms) => Some(format!("the earlier repetitions' {}", self.atoms_said(atoms))),
                Level::Cage(n) => Some(format!("what `{}` gives", self.name(*n))),
                Level::Shape(_) => None,
            })
            .collect();
        match levels.split_first() {
            None => "no scope of the pattern's binders".to_string(),
            Some((first, rest)) => rest.iter().fold(format!("the scope of {first}"), |s, l| format!("{s}, and inside that of {l}")),
        }
    }

    fn atoms_said(&self, atoms: &[Atom]) -> String {
        let mut names: Vec<String> = atoms
            .iter()
            .filter_map(|a| match a {
                // Gathered by `k` lists, `((x ...) ...)`; a description's
                // binder said so.
                Atom::Var(n, ns, k) => {
                    let s = (0..*k).fold(self.name(*n).to_string(), |s, _| format!("({s} ...)"));
                    Some(if *ns == Ns::Desc { format!("`{s}`, a description") } else { format!("`{s}`") })
                }
                Atom::RibOf(n) => Some(format!("`({} ...)`", self.name(*n))),
                Atom::Lit(..) => None,
            })
            .collect();
        names.sort();
        names.dedup();
        names.join(" and ")
    }
}

impl Aligner<'_> {
    /// Pattern binder `n`, of namespace `ns`, referred to in `env`: in its
    /// scope, and where no other of the pattern's binders of that namespace
    /// may shadow it (Herman's shadow restriction). A value's binder never
    /// shadows a description's; every description's shares one namespace.
    fn in_scope(&self, n: Sym, ns: Ns, env: &[Level], span: At) -> R<()> {
        let name = self.name(n);
        // By its name: a reference finds its binder whichever repetitions
        // are gathered (the ellipses it is under say which, `Clause`'s
        // depths).
        let named = |a: &Atom| matches!(a, Atom::Var(m, k, _) if *m == n && *k == ns);
        let Some(i) = env.iter().position(|l| matches!(l, Level::Rib(atoms) | Level::Earlier(atoms) if atoms.iter().any(named))) else {
            return Err(FxError::at(span, format!("`{name}` is referred to where the template does not bind it")));
        };
        if matches!(&env[i], Level::Earlier(_)) {
            return Err(FxError::at(span, format!("`{name}` is bound by the repetitions before this one, which its name does not tell apart: a repeated part refers to no binder it repeats in its own scope")));
        }
        let shadows = |a: &Atom| match a {
            Atom::Lit(..) => false,
            Atom::Var(_, k, _) => *k == ns,
            Atom::RibOf(_) => true,
        };
        if env[..i].iter().any(|l| matches!(l, Level::Cage(_)) || matches!(l, Level::Rib(atoms) | Level::Earlier(atoms) if atoms.iter().any(shadows))) {
            return Err(FxError::at(span, format!("`{name}` is referred to where another of the pattern's binders may shadow it (Herman's shadow restriction): a use giving both one name would change what it refers to")));
        }
        Ok(())
    }
}

impl Macros {
    /// Whether syntax of type `a` is all of type `b`, binding structure
    /// alike: coinductive, as FX-26's recursive types are, each pair a `mu`
    /// is of assumed while it is compared (`assumed`), by structure: the
    /// types a `mu` unfolds to are finitely many (Brandt and Henglein), so
    /// the pairs are.
    fn sub(&self, a: &Rc<STy>, b: &Rc<STy>, assumed: &mut Vec<(Rc<STy>, Rc<STy>)>) -> bool {
        use STy::*;
        if same(a, b) {
            return true;
        }
        if matches!((&**a, &**b), (Mu(..), _) | (_, Mu(..))) {
            if assumed.iter().any(|(x, y)| same(x, a) && same(y, b)) {
                return true;
            }
            assumed.push((a.clone(), b.clone()));
        }
        match (&**a, &**b) {
            (Import(x, p), Import(y, q)) | (Export(x, p), Export(y, q)) => bind_same(p, q) && self.sub(x, y, assumed),
            (Many(x), _) | (Typed(x, _), _) => self.sub(x, b, assumed),
            (_, Many(y)) | (_, Typed(y, _)) => self.sub(a, y, assumed),
            (Mu(..), _) => self.sub(&unfold_mu(a), b, assumed),
            (_, Mu(..)) => self.sub(a, &unfold_mu(b), assumed),
            (Union(ms), _) => ms.iter().all(|m| self.sub(m, b, assumed)),
            (_, Union(ms)) => ms.iter().any(|m| self.sub(a, m, assumed)),
            (Import(..) | Export(..), _) | (_, Import(..) | Export(..)) => false,
            (Pair(a1, d1), Pair(a2, d2)) => self.sub(a1, a2, assumed) && self.sub(d1, d2, assumed),
            (Lambda, Expr) => true,
            (x, y) => x == y,
        }
    }
}

/// An environment as compared: the template's own binders left out (made
/// fresh, they bind nothing a use wrote), each rib in order, empty ones
/// gone.
fn normal(env: &[Level]) -> Vec<Level> {
    env.iter()
        .filter_map(|l| match l {
            Level::Rib(atoms) => {
                let mut a: Vec<Atom> = atoms.iter().filter(|a| !matches!(a, Atom::Lit(..))).cloned().collect();
                a.sort();
                (!a.is_empty()).then_some(Level::Rib(Rc::new(a)))
            }
            Level::Earlier(atoms) => {
                let mut a: Vec<Atom> = atoms.iter().filter(|a| !matches!(a, Atom::Lit(..))).cloned().collect();
                a.sort();
                (!a.is_empty()).then_some(Level::Earlier(Rc::new(a)))
            }
            Level::Cage(n) => Some(Level::Cage(*n)),
            Level::Shape(n) => Some(Level::Shape(*n)),
        })
        .collect()
}

/// What an export binds of what a use gives, as compared: its pattern
/// variables' atoms, each once, sorted, and the ribcages, sorted; the
/// template's own binders, made fresh, none of it.
fn exports(levels: &[Level]) -> (Vec<Atom>, Vec<Sym>) {
    let mut atoms = Vec::new();
    let mut cages = Vec::new();
    for l in normal(levels) {
        match l {
            Level::Rib(a) | Level::Earlier(a) => atoms.extend(a.iter().cloned()),
            Level::Cage(n) => cages.push(n),
            Level::Shape(_) => {}
        }
    }
    atoms.sort();
    atoms.dedup();
    cages.sort();
    cages.dedup();
    (atoms, cages)
}

/// An export's names, as said, in order: `` `a` `` for a binder, `` what `a`
/// defines `` for a rib or ribcage; `nothing` if none.
fn shown_exports(e: &(Vec<Atom>, Vec<Sym>), interner: &Interner) -> String {
    let mut out: Vec<String> = e.0.iter().filter_map(|a| match a {
        Atom::Var(n, _, _) => Some(format!("`{}`", interner.name(*n))),
        Atom::RibOf(n) => Some(format!("what `{}` defines", interner.name(*n))),
        Atom::Lit(..) => None,
    }).collect();
    out.extend(e.1.iter().map(|n| format!("what `{}` defines", interner.name(*n))));
    out.sort();
    out.dedup();
    if out.is_empty() { "nothing".to_string() } else { out.join(", ") }
}

/// A macro as its `define-syntax` writes it: its name, its signature if
/// written, and its `syntax-rules`' literals and clauses.
struct Written {
    name: Sym,
    sig: Option<Syn>,
    lits: Vec<Sym>,
    clauses: Vec<Syn>,
    span: At,
    /// A procedural macro's transformer: its style, and the procedure.
    procedural: Option<(procedural::Style, Syn)>,
    /// A trailmark, `(trailmark ["where it belongs"])`: what it says.
    mark: Option<Option<String>>,
}

/// The macros `form` defines: a `define-syntax`'s one, or each of a
/// `define-syntax-rec`'s, `(define-syntax-rec (name [σ] (syntax-rules …)) …)`,
/// all defined together, so that each template may use any of them.
fn written(form: &Syn, interner: &Interner) -> R<Vec<Written>> {
    let usage = "`(define-syntax name [signature] (syntax-rules [#:trailmarks (name …)] ((_ . pattern) template) …))`";
    let rec = "`(define-syntax-rec (name [signature] (syntax-rules [#:trailmarks (name …)] clause …)) …)`";
    let items = form.list().ok_or_else(|| FxError::at(form.at(), usage))?;
    if items.first().and_then(|h| h.sym()).is_some_and(|h| interner.name(h) == "define-syntax-rec") {
        if items.len() < 2 {
            return Err(FxError::at(form.at(), rec));
        }
        let mut out: Vec<Written> = Vec::new();
        for m in &items[1..] {
            let l = m.list();
            let Some([name, rest @ ..]) = l.as_deref() else {
                return Err(FxError::at(m.at(), rec));
            };
            let w = written_one(name, rest, m.at(), rec, interner)?;
            if w.mark.is_some() {
                return Err(FxError::at(m.at(), "a trailmark is defined alone, by `define-syntax`"));
            }
            if out.iter().any(|o| o.name == w.name) {
                return Err(FxError::at(name.at(), format!("`{}` is defined twice in this `define-syntax-rec`", interner.name(w.name))));
            }
            out.push(w);
        }
        return Ok(out);
    }
    let [_, name, rest @ ..] = &items[..] else {
        return Err(FxError::at(form.at(), usage));
    };
    Ok(vec![written_one(name, rest, form.at(), usage, interner)?])
}

fn written_one(name: &Syn, rest: &[Syn], at: At, usage: &str, interner: &Interner) -> R<Written> {
    let name = name.sym().filter(|n| !reserved(interner.name(*n))).ok_or_else(|| FxError::at(name.at(), format!("{usage}: a macro's name, not a form's")))?;
    let rules = |s: &Syn| s.list().and_then(|l| l.first().copied()).and_then(|h| h.sym()).is_some_and(|h| interner.name(h) == "syntax-rules");
    // A procedural macro: `(er-macro-transformer proc)`, `(sc-macro-
    // transformer proc)` or `(rsc-macro-transformer proc)`; after its
    // signature, its contract, if it is written.
    if let (sig, [t]) = match rest {
        [sig, t] => (Some(sig.clone()), std::slice::from_ref(t)),
        _ => (None, rest),
    } && let Some(items) = t.list()
        && let Some(style) = items.first().and_then(|h| h.sym()).and_then(|h| procedural::Style::named(interner.name(h)))
    {
        let [_, code] = &items[..] else {
            return Err(FxError::at(t.at(), format!("`({} procedure)`", interner.name(items[0].sym().expect("a head")))));
        };
        return Ok(Written { name, sig, lits: Vec::new(), clauses: Vec::new(), span: at, procedural: Some((style, code.clone())), mark: None });
    }
    // A trailmark: `(trailmark)`, or `(trailmark "where it belongs")`.
    if let [t] = rest
        && let Some(items) = t.list()
        && items.first().and_then(|h| h.sym()).is_some_and(|h| interner.name(h) == "trailmark")
    {
        let said = match &items[1..] {
            [] => None,
            [s] => match s.view() {
                V::Str(text) => Some(text.to_string()),
                _ => return Err(FxError::at(t.at(), "`(trailmark)`, or `(trailmark \"where it belongs\")`")),
            },
            _ => return Err(FxError::at(t.at(), "`(trailmark)`, or `(trailmark \"where it belongs\")`")),
        };
        return Ok(Written { name, sig: None, lits: Vec::new(), clauses: Vec::new(), span: at, procedural: None, mark: Some(said) });
    }
    let (sig, rules) = match rest {
        [r] if rules(r) => (None, r),
        [sig, r] if rules(r) => (Some(sig.clone()), r),
        // The clauses are a transformer's, which says how to read them.
        [_, c, ..] if c.list().is_some_and(|l| l.len() == 2) => {
            return Err(FxError::at(c.at(), "a macro's clauses are a transformer's: `(syntax-rules [#:trailmarks (name …)] ((_ . pattern) template) …)`, after its signature if it is written"));
        }
        _ => return Err(FxError::at(at, usage.to_string())),
    };
    let parts = rules.list().expect("a list");
    let (lits, clauses) = rules_parts(&parts[1..], rules.at(), interner)?;
    Ok(Written { name, sig, lits, clauses, span: at, procedural: None, mark: None })
}

/// A `syntax-rules`' parts after its head: the names its `#:trailmarks
/// (name …)` lists, if it has one, and its clauses. A `()` or a list of
/// names first, R7RS's literals, refused, saying how it is written now.
pub(super) fn rules_parts(parts: &[Syn], at: At, interner: &Interner) -> R<(Vec<Sym>, Vec<Syn>)> {
    let usage = "`(syntax-rules [#:trailmarks (name …)] ((_ . pattern) template) …)`";
    match parts {
        [k, names, clauses @ ..] if matches!(k.view(), V::Keyword(w) if interner.name(w) == "trailmarks") => {
            let names = names.list().and_then(|l| l.iter().map(|x| x.sym()).collect::<Option<Vec<_>>>()).filter(|l| !l.is_empty()).ok_or_else(|| FxError::at(names.at(), "a `syntax-rules`' `#:trailmarks` are a list of names, one or more"))?;
            Ok((names, clauses.to_vec()))
        }
        [k, ..] if matches!(k.view(), V::Keyword(_)) => Err(FxError::at(k.at(), usage)),
        [first, ..] if matches!(first.view(), V::Nil) => Err(FxError::at(first.at(), "a `syntax-rules` has no list of literals: drop the `()` (names its patterns match are written `#:trailmarks (name …)`)")),
        [first, ..] if first.list().is_some_and(|l| l.iter().all(|x| x.sym().is_some())) => {
            let shown = first.written(interner);
            Err(FxError::at(first.at(), format!("a `syntax-rules`' names its patterns match are its trailmarks: `#:trailmarks {shown}`, each defined `(define-syntax name (trailmark))`")))
        }
        [] => Err(FxError::at(at, usage)),
        clauses => Ok((Vec::new(), clauses.to_vec())),
    }
}

/// The signature of operands `s` making definitions, as written: `(macro σ
/// (defn (ℓ δ) …))` of `(export σ (rho (ℓ δ) …))`, else `(-> s defn)`.
fn defn_arrow(s: Syn, at: At, interner: &mut Interner) -> Syn {
    let arrow = Syn::named(at, ADDRESSED, interner);
    let defn = Syn::named(at, "defn", interner);
    if let Some([e, body, b]) = s.list().as_deref()
        && e.sym().is_some_and(|e| interner.name(e) == "export")
        && let Some(rho) = b.list()
        && rho.first().and_then(|r| r.sym()).is_some_and(|r| interner.name(r) == "rho")
    {
        let made = Syn::lst(at, std::iter::once(defn).chain(rho[1..].iter().copied()).collect());
        return Syn::lst(at, vec![arrow, *body, made]);
    }
    Syn::lst(at, vec![arrow, s, defn])
}

/// Whether `body`, operands a signature's uses make definitions of, is the
/// old `(export σ (rho (ℓ δ) …))`, now `σ` with `(defn (ℓ δ) …)`.
fn old_defn_export(body: &Syn, interner: &Interner) -> bool {
    let head = |s: &Syn, n: &str| s.list().and_then(|l| l.first().and_then(|h| h.sym())).is_some_and(|h| interner.name(h) == n);
    matches!(body.list().as_deref(), Some([_, _, b]) if head(body, "export") && head(b, "rho"))
}

/// Why the old `(export σ (rho (ℓ δ) …))` is refused, how it is written now.
const OLD_DEFN_EXPORT: &str = "what a use defines is said in what it makes, `(macro/addressed σ (defn (ℓ δ) …))`, not by `(export σ (rho (ℓ δ) …))` around its parts: the `rho`'s entries go in the `defn`";

/// What is said of a name a macro takes for a trailmark that is none.
fn no_trailmark(name: &str) -> String {
    format!("`{name}` names no trailmark here: `(define-syntax {name} (trailmark))`")
}

fn bind(b: &Syn, interner: &Interner) -> R<Bind> {
    let usage = "a binding is `(rho (address δ) …)` or `(cage (rho …) (at address) …)`";
    let items = b.list().ok_or_else(|| FxError::at(b.at(), usage))?;
    let head = items.first().and_then(|h| h.sym()).map(|h| interner.name(h));
    let rib = |entries: &[Syn]| -> R<Vec<(Addr, Delta)>> {
        entries
            .iter()
            .map(|e| match e.list().as_deref() {
                // A macro's binder: its kind the macro's signature.
                Some([a, d]) if d.list().is_some_and(|l| l.len() >= 3 && l[0].sym().is_some_and(|h| addressed_head(interner.name(h)))) => Ok((addr(a, interner)?, Delta::Syntax(Kept::new(*d)))),
                Some([_, d]) if d.list().is_some_and(|l| l.first().and_then(|h| h.sym()).is_some_and(|h| interner.name(h) == "syntax")) => Err(FxError::at(d.at(), "a macro's binder is written with its signature, `(macro …)`, not `(syntax …)`")),
                Some([a, d]) => {
                    let d = match d.sym().map(|d| interner.name(d)) {
                        Some("none") => Delta::None,
                        Some("var") => Delta::Var,
                        Some("dvar") => Delta::Dvar,
                        Some("place") => Delta::Place,
                        Some("rib") => Delta::Rib,
                        Some("env") => Delta::Env,
                        _ => return Err(FxError::at(d.at(), "δ is `none`, `var`, `dvar`, `place`, `rib`, `env` or a macro's signature, `(macro σ made)`")),
                    };
                    Ok((addr(a, interner)?, d))
                }
                _ => Err(FxError::at(e.at(), usage)),
            })
            .collect()
    };
    match head {
        Some("rho") => Ok(Bind::Rib(rib(&items[1..])?)),
        Some("shape") if items.len() == 2 => Ok(Bind::Shape(addr(&items[1], interner)?)),
        Some("cage") => {
            let rings = items[1..]
                .iter()
                .map(|r| {
                    let parts = r.list().ok_or_else(|| FxError::at(r.at(), usage))?;
                    match parts.first().and_then(|h| h.sym()).map(|h| interner.name(h)) {
                        Some("rho") => Ok(Ring::Rib(rib(&parts[1..])?)),
                        Some("at") if parts.len() == 2 => Ok(Ring::At(addr(&parts[1], interner)?)),
                        _ => Err(FxError::at(r.at(), usage)),
                    }
                })
                .collect::<R<Vec<_>>>()?;
            Ok(Bind::Cage(rings))
        }
        _ => Err(FxError::at(b.at(), usage)),
    }
}

/// A typed hole's keywords and what each says, `#:type T` and, of an
/// `expr`, `#:effect E`, each once.
fn hole(parts: &[Syn], kind: &str, s: &Syn, interner: &Interner) -> R<Hole> {
    let expr = kind == "expr";
    let usage = if expr { "`(expr #:type T #:effect E)`, either left out".to_string() } else { format!("`({kind} #:type T)`") };
    let mut h = Hole { ty: None, effect: None };
    let mut rest = parts;
    while let [k, v, more @ ..] = rest {
        let slot = match &k.view() {
            V::Keyword(w) if interner.name(*w) == "type" => &mut h.ty,
            V::Keyword(w) if expr && interner.name(*w) == "effect" => &mut h.effect,
            _ => return Err(FxError::at(k.at(), format!("a syntax type: {usage}"))),
        };
        if slot.replace(Kept::new(*v)).is_some() {
            return Err(FxError::at(k.at(), format!("a syntax type: {usage}, each once")));
        }
        rest = more;
    }
    if !rest.is_empty() {
        return Err(FxError::at(s.at(), format!("a syntax type: {usage}")));
    }
    Ok(h)
}

/// An address, `A`s and `D`s read right to left, or `()`, none: its steps,
/// first first.
fn addr(a: &Syn, interner: &Interner) -> R<Addr> {
    if matches!(a.view(), V::Nil) {
        return Ok(Vec::new());
    }
    // `(path #:a #:d …)`: its steps from the root, first first.
    if let Some(items) = a.list()
        && items.first().and_then(|h| h.sym()).is_some_and(|h| interner.name(h) == "path")
    {
        return items[1..]
            .iter()
            .map(|k| match k.view() {
                V::Keyword(w) if interner.name(w) == "a" => Ok(true),
                V::Keyword(w) if interner.name(w) == "d" => Ok(false),
                _ => Err(FxError::at(k.at(), PATH_USAGE)),
            })
            .collect();
    }
    let name = a.sym().map(|a| interner.name(a)).filter(|n| !n.is_empty() && n.chars().all(|c| c == 'A' || c == 'D'));
    let Some(name) = name else {
        return Err(FxError::at(a.at(), PATH_USAGE));
    };
    Ok(name.chars().rev().map(|c| c == 'A').collect())
}

/// What an address is, said where one is not.
const PATH_USAGE: &str = "an address is `(path #:a #:d …)`, its steps from the root, `#:a` the car and `#:d` the cdr";

/// Herman's form of a signature, as an inferred one is shown, for now.
const ADDRESSED: &str = "macro/addressed";

/// Whether `h` heads a signature: `macro`, in shapes and facts, or
/// `macro/addressed`, Herman's (`typed-macros.md`, "Decided: signatures in
/// shapes and facts").
fn addressed_head(h: &str) -> bool {
    matches!(h, "macro/addressed" | "macro")
}

/// An address of signature `s` written as Herman's letters, `AAD`, which
/// the kernel's own signatures keep and a program's write `(path …)`.
fn lettered(s: &Syn, interner: &Interner) -> Option<Syn> {
    let items = s.list()?;
    let head = items.first().and_then(|h| h.sym()).map(|h| interner.name(h));
    let word = |a: &Syn| a.sym().is_some_and(|n| interner.name(n).chars().all(|c| c == 'A' || c == 'D'));
    let found = match head {
        Some("rho" | "defn") => items[1..].iter().find_map(|e| e.list().and_then(|l| l.first().copied()).filter(word)),
        Some("at" | "shape") => items.get(1).copied().filter(word),
        _ => None,
    };
    found.or_else(|| items.iter().find_map(|x| lettered(x, interner)))
}

/// `s`, at `path`, each symbol at a path of `renamed` renamed so.
/// What `Macros::uses_found` finds at a path: a use of a macro, with the
/// macros' names bound around it; or a path, `a::b::c`, naming a value or
/// a description.
enum Part {
    Use(Rc<HashSet<Sym>>),
    Path(Ns),
}

/// Whether `name` is a path, `a::b::c` (`TODO.md` §296): a program's, not
/// a name of the expander's own (`%…`).
fn path_named(name: &str) -> bool {
    !name.starts_with('%') && name.contains("::")
}

/// Whether a path is written in `s`, outside a quoted datum.
pub(crate) fn names_path(s: &Syn, interner: &Interner) -> bool {
    match &s.view() {
        V::Symbol(n) => path_named(interner.name(*n)),
        V::List { items, tail } => {
            !items[0].sym().is_some_and(|h| interner.name(h) == "quote") && (items.iter().any(|i| names_path(i, interner)) || tail.as_ref().is_some_and(|t| names_path(t, interner)))
        }
        _ => false,
    }
}

fn rename_paths(s: &Syn, path: Path, renamed: &HashMap<Path, String>, interner: &mut Interner) -> Syn {
    if let Some(n) = renamed.get(&path) {
        return Syn::named(s.at(), n, interner);
    }
    match &s.view() {
        V::List { items, tail } => {
            // Each item's path, the car of the cdrs before it.
            let mut rest = path;
            let mut out = Vec::new();
            for i in items {
                out.push(rename_paths(i, rest.push(true), renamed, interner));
                rest = rest.push(false);
            }
            let tail = tail.as_ref().map(|t| rename_paths(t, rest, renamed, interner));
            Syn::of_list(s.at(), &out, tail)
        }
        _ => s.clone(),
    }
}

/// `nodes` sorted by their paths in `form` (`path_of`), as their steps
/// sort, a car before a cdr (`true` before `false`): a part before what
/// follows it, a list's first part before its rest. That is the order a
/// walk of `form` meets them, so each path is numbered once by the walk,
/// not compared step by step (`paths.rs`); a path the walk does not meet
/// (none, as the aligner makes them) by its steps.
pub(crate) fn sort_by_path(nodes: &mut [usize], path_of: impl Fn(usize) -> Path, form: &Syn) {
    fn walk(s: &Syn, path: Path, out: &mut HashMap<Path, usize>) {
        let n = out.len();
        out.insert(path, n);
        if let V::List { items, tail } = &s.view() {
            let mut rest = path;
            for i in items {
                walk(i, rest.push(true), out);
                rest = rest.push(false);
                let n = out.len();
                out.insert(rest, n);
            }
            if let Some(t) = tail {
                walk(t, rest, out);
            }
        }
    }
    let mut order = HashMap::default();
    walk(form, Path::ROOT, &mut order);
    if nodes.iter().all(|k| order.contains_key(&path_of(*k))) {
        nodes.sort_by_key(|k| order[&path_of(*k)]);
    } else {
        nodes.sort_by_cached_key(|k| path_of(*k).steps().iter().map(|s| !s).collect::<Vec<bool>>());
    }
}

/// Whether module parameter `b` binds a description, not a module (as
/// `parse::binder_is_kind` reads it).
fn binder_is_kind(b: &Syn, interner: &Interner) -> bool {
    let kind = |k: &Syn| match k.list().as_deref() {
        Some([h, ..]) => h.sym().is_some_and(|h| interner.name(h) == "=>"),
        _ => k.sym().is_some_and(|k| matches!(interner.name(k), "region" | "place" | "effect" | "type" | "data" | "sendable" | "flat" | "size" | "conv")),
    };
    match b.list().as_deref() {
        Some([_, k]) => kind(k),
        Some([_, k, q]) => kind(k) || !q.sym().is_some_and(|q| interner.name(q) == "qualified"),
        _ => true,
    }
}

/// Whether `t` uses the variable of the `mu` `k` around it only under a
/// pair, a `mu` inside it looked into too: none unfolds to itself.
fn guarded(t: &STy, k: usize) -> bool {
    match t {
        STy::Var(j) => *j != k,
        STy::Mu(b, _) => guarded(b, k + 1),
        STy::Import(b, _) | STy::Export(b, _) | STy::Many(b) | STy::Typed(b, _) => guarded(b, k),
        STy::Union(ms) => ms.iter().all(|m| guarded(m, k)),
        _ => true,
    }
}

/// `(elem ...)`: `(mu l (union () (elem . l)))`, `elem` read under the
/// `mu`; and if `elem` exports, each element's export together, as a
/// `let`'s bindings do; a binder alone, `bvar` or `dvar`, exports itself.
fn seq(elem: Rc<STy>) -> Rc<STy> {
    let elem = match &*elem {
        STy::Bvar => Rc::new(STy::Export(elem, Bind::Rib(vec![(Vec::new(), Delta::Var)]))),
        STy::Dvar => Rc::new(STy::Export(elem, Bind::Rib(vec![(Vec::new(), Delta::Dvar)]))),
        _ => elem,
    };
    Rc::new(STy::Mu(Rc::new(STy::Union(seq_members(&elem))), None))
}

const ONEOF_APART: &str = "a `oneof`'s members must be told apart by their shapes in the source (an `expr` may be anything)";

/// Whether two of `ms` may be of the same syntax.
fn any_overlap(m: &Macros, ms: &[Rc<STy>]) -> bool {
    ms.iter().enumerate().any(|(i, a)| ms[i + 1..].iter().any(|b| m.overlap(a, b, OVERLAP_DEPTH)))
}

/// Whether `t` refers to a `mu` `k` or more out from it.
fn has_free(t: &Rc<STy>, k: usize) -> bool {
    let found = std::cell::Cell::new(false);
    map_vars(t, k, &|j, k| {
        if j >= k {
            found.set(true);
        }
        None
    });
    found.get()
}

/// `t`, under the `mu`s `env` (closed, the innermost last), closed: each
/// variable that refers to one of them that `mu`.
fn closed_by(t: &Rc<STy>, env: &[Rc<STy>]) -> Rc<STy> {
    map_vars(t, 0, &|j, k| (j >= k).then(|| env[env.len() - 1 - (j - k)].clone())).unwrap_or_else(|| t.clone())
}

/// Whether `a` and `b` are one type: the same, or alike in structure.
pub(crate) fn same(a: &Rc<STy>, b: &Rc<STy>) -> bool {
    Rc::ptr_eq(a, b) || a == b
}

/// `t` with each variable `k` or more `mu`s out raised by `d`: as it is
/// placed under `d` `mu`s more. What has none of them is shared.
pub(crate) fn shift(t: &Rc<STy>, d: usize, k: usize) -> Rc<STy> {
    map_vars(t, k, &|j, k| (j >= k).then(|| Rc::new(STy::Var(j + d)))).unwrap_or_else(|| t.clone())
}

/// `t` with the variable of the `mu` `k` around it replaced by `s`, and
/// those further out lowered by one, as that `mu` is gone.
fn subst(t: &Rc<STy>, k: usize, s: &Rc<STy>) -> Rc<STy> {
    map_vars(t, k, &|j, k| match j.cmp(&k) {
        std::cmp::Ordering::Equal if k == 0 => Some(s.clone()),
        std::cmp::Ordering::Equal => Some(shift(s, k, 0)),
        std::cmp::Ordering::Greater => Some(Rc::new(STy::Var(j - 1))),
        std::cmp::Ordering::Less => None,
    })
    .unwrap_or_else(|| t.clone())
}

/// `t` with each variable `j`, under `k` `mu`s more than `t` is, as `f`
/// says, if it says one changes; none if none does.
fn map_vars(t: &Rc<STy>, k: usize, f: &dyn Fn(usize, usize) -> Option<Rc<STy>>) -> Option<Rc<STy>> {
    let one = |b: &Rc<STy>, k: usize| map_vars(b, k, f);
    Some(Rc::new(match &**t {
        STy::Var(j) => return f(*j, k),
        STy::Mu(b, tag) => STy::Mu(one(b, k + 1)?, *tag),
        STy::Pair(a, d) => match (one(a, k), one(d, k)) {
            (None, None) => return None,
            (a2, d2) => STy::Pair(a2.unwrap_or_else(|| a.clone()), d2.unwrap_or_else(|| d.clone())),
        },
        STy::Import(b, x) => STy::Import(one(b, k)?, x.clone()),
        STy::Export(b, x) => STy::Export(one(b, k)?, x.clone()),
        STy::Many(b) => STy::Many(one(b, k)?),
        STy::Typed(b, h) => STy::Typed(one(b, k)?, h.clone()),
        STy::Union(ms) => {
            let each: Vec<Option<Rc<STy>>> = ms.iter().map(|m| one(m, k)).collect();
            if each.iter().all(Option::is_none) {
                return None;
            }
            STy::Union(each.into_iter().zip(ms).map(|(m2, m)| m2.unwrap_or_else(|| m.clone())).collect())
        }
        _ => return None,
    }))
}

/// `mu` `t` unfolded once: its body, its variable `t` again.
pub(crate) fn unfold_mu(t: &Rc<STy>) -> Rc<STy> {
    unfolded(t).unwrap_or_else(|| t.clone())
}

/// `t` unfolded once, if it is a `mu`.
pub(crate) fn unfolded(t: &Rc<STy>) -> Option<Rc<STy>> {
    match &**t {
        STy::Mu(b, _) => Some(subst(b, 0, t)),
        _ => None,
    }
}

/// `t`, under one `mu` it does not refer to, without it: none if it does.
pub(crate) fn lowered(t: &Rc<STy>) -> Option<Rc<STy>> {
    let refers = std::cell::Cell::new(false);
    let r = map_vars(t, 0, &|j, k| match j.cmp(&k) {
        std::cmp::Ordering::Equal => {
            refers.set(true);
            None
        }
        std::cmp::Ordering::Greater => Some(Rc::new(STy::Var(j - 1))),
        std::cmp::Ordering::Less => None,
    });
    if refers.get() { None } else { Some(r.unwrap_or_else(|| t.clone())) }
}

/// What reading a signature found to say (`contract::notes_taken`), said
/// once a thread each: its uses read it again and again.
fn say_signature_notes() {
    thread_local! {
        static SAID: std::cell::RefCell<fixpt_hash::HashSet<String>> = std::cell::RefCell::new(fixpt_hash::HashSet::default());
    }
    for n in contract::notes_taken() {
        if SAID.with(|s| s.borrow_mut().insert(n.clone())) {
            eprintln!("fixpt: warning: a signature: {n}");
        }
    }
}

/// The deepest part of `s` whose text, as `s` is written (`Syn::written`),
/// holds its character `at`: where a phase-1 form's refusal is
/// (`Macros::for_syntax`); `s` if no part of it does. The expander written
/// in FX-26's `syn-at`.
fn written_part(s: Syn, interner: &Interner, at: i64) -> Syn {
    let (items, tail, open) = match s.view() {
        V::List { items, tail } => (items, tail, 1),
        V::Vector(items) => (items, None, 2),
        _ => return s,
    };
    let mut o = open;
    for x in items {
        let n = x.written(interner).chars().count() as i64;
        if at >= o && at < o + n {
            return written_part(x, interner, at - o);
        }
        o += n + 1;
    }
    // ` . ` after the last item's space.
    if let Some(t) = tail {
        let t_at = o + 2;
        let n = t.written(interner).chars().count() as i64;
        if at >= t_at && at < t_at + n {
            return written_part(t, interner, at - t_at);
        }
    }
    s
}

/// A form's name, `#%fx` or `#%toplevel`: never bound, so never a binder or
/// a variable.
fn reserved(name: &str) -> bool {
    // The set made once, as the FX-26 expander's table (`reserved-table`):
    // a name looked for by its hash, not among the 140.
    static RESERVED: std::sync::OnceLock<HashSet<&'static str>> = std::sync::OnceLock::new();
    RESERVED
        .get_or_init(|| {
            let extra = ["#%fx", "#%toplevel", "define-syntax", "define-syntax-rec"];
            crate::top::KEYWORDS.iter().copied().chain(extra).collect()
        })
        .contains(name)
}

/// Whether `name` is a word of a macro's definition: `syntax-rules`, a
/// procedural transformer's style, a trailmark's.
fn transformer_word(name: &str) -> bool {
    matches!(name, "syntax-rules" | "trailmark") || procedural::Style::named(name).is_some()
}

/// `split` of `s`, which is taken: its rest shared, not copied.
fn split_owned(s: Syn) -> Option<(Syn, Syn)> {
    s.split()
}

/// A list's car and cdr, the cdr a list of the rest (or the tail).
fn split(s: &Syn) -> Option<(Syn, Syn)> {
    s.split()
}

/// `items` and `tail` as one list: a tail that is a list joined to it, an
/// empty one dropped.
fn list_of(at: At, mut items: Vec<Syn>, tail: Option<Syn>) -> Syn {
    let tail = match tail.map(|t| t.view()) {
        None | Some(V::Nil) => None,
        Some(V::List { items: more, tail }) => {
            items.extend(more);
            tail
        }
        Some(_) => tail.map(|t| t.placed(at)),
    };
    if items.is_empty() {
        return Syn::nil(at);
    }
    Syn::of_list(at, &items, tail)
}

/// Whether `s` matches pattern `p`, binding its variables in `binds`: a
/// name the pattern variable (`_` anything), a form's name or a keyword
/// itself.
/// `names`: the clause's pattern variables that are names, its trailmarks,
/// and the trailmark each name is bound to where the use is.
type MatchNames<'a> = (&'a HashSet<Sym>, &'a HashMap<Sym, usize>, &'a dyn Fn(Sym) -> Option<usize>);

fn matches(p: &Syn, s: &Syn, names: &MatchNames, binds: &mut HashMap<Sym, Syn>, interner: &Interner) -> bool {
    // `(x ...)`: each element of a list by `x`, each of its pattern
    // variables then the list of what it matched.
    if let Some(x) = ellipsis(p, interner) {
        let Some(elems) = (match &s.view() {
            V::Nil => Some(Vec::new()),
            _ => s.list().map(|l| l.to_vec()),
        }) else {
            return false;
        };
        let mut each = Vec::new();
        for e in &elems {
            let mut b = HashMap::default();
            if !matches(&x, e, names, &mut b, interner) {
                return false;
            }
            each.push(b);
        }
        for n in pattern_names(&x, interner) {
            let items: Vec<Syn> = each.iter().map(|b| b[&n].clone()).collect();
            binds.insert(n, list_of(s.at(), items, None));
        }
        return true;
    }
    match &p.view() {
        V::Symbol(n) if interner.name(*n) == "_" => true,
        V::Symbol(n) if reserved(interner.name(*n)) => s.sym() == Some(*n),
        // A trailmark: a name bound to the same one.
        V::Symbol(n) if names.1.contains_key(n) => s.sym().and_then(names.2) == names.1.get(n).copied(),
        // A name's pattern variable matches a name alone.
        V::Symbol(n) if names.0.contains(n) && s.sym().is_none() => false,
        V::Symbol(n) => {
            binds.insert(*n, s.clone());
            true
        }
        V::Nil => matches!(s.view(), V::Nil),
        V::List { .. } => match (split(p), split(s)) {
            (Some((pa, pd)), Some((sa, sd))) => matches(&pa, &sa, names, binds, interner) && matches(&pd, &sd, names, binds, interner),
            _ => false,
        },
        other => &s.view() == other,
    }
}

/// Whether `s` is the name `...`.
fn is_ellipsis(s: &Syn, interner: &Interner) -> bool {
    s.sym().is_some_and(|n| interner.name(n) == "...")
}

/// `x` of `(x ...)`, a part repeated, if `s` is one.
fn ellipsis(s: &Syn, interner: &Interner) -> Option<Syn> {
    match s.list().as_deref() {
        Some([x, dots]) if is_ellipsis(dots, interner) => Some(x.clone()),
        _ => None,
    }
}

/// What a pattern variable repeated was given: the list's elements.
fn elements(s: &Syn) -> Vec<Syn> {
    match &s.view() {
        V::Nil => Vec::new(),
        _ => s.list().map(|l| l.to_vec()).unwrap_or_default(),
    }
}

/// The pattern variables in pattern `p`: its names but `_`, `...` and the
/// forms' (which match themselves).
fn pattern_names(p: &Syn, interner: &Interner) -> Vec<Sym> {
    match &p.view() {
        V::Symbol(n) if !matches!(interner.name(*n), "_" | "...") && !reserved(interner.name(*n)) => vec![*n],
        V::List { items, tail } => items.iter().chain(tail.as_ref()).flat_map(|x| pattern_names(x, interner)).collect(),
        _ => Vec::new(),
    }
}

/// Whether `name` is a macro's template's check (`template_checks`), which
/// no program names, so that nothing shows it.
pub fn template_check(name: &str) -> bool {
    name.starts_with("%template:")
}

/// Name `n` where `s` writes it, the first.
fn find_symbol(s: &Syn, n: Sym) -> Option<Syn> {
    match &s.view() {
        V::Symbol(m) if *m == n => Some(*s),
        V::List { items, tail } => items.iter().chain(tail.as_ref()).find_map(|x| find_symbol(x, n)),
        _ => None,
    }
}

/// Whether `s` is a lambda as the checkers take one (`Checker::is_lambda`):
/// a `lambda`, `rlambda` or `vlambda`, in `plambda`s and `the`s.
fn lambda_shaped(s: &Syn, interner: &Interner) -> bool {
    let Some(items) = s.list() else { return false };
    match items.first().and_then(|h| h.sym()).map(|h| interner.name(h)) {
        Some("lambda" | "rlambda" | "vlambda") => true,
        Some("plambda") if items.len() == 3 => lambda_shaped(&items[2], interner),
        Some("the") if items.len() == 3 => lambda_shaped(&items[2], interner),
        _ => false,
    }
}

/// Whether syntax `s` names one of `names`.
fn names_one_of(s: &Syn, names: &[Sym]) -> bool {
    match &s.view() {
        V::Symbol(n) => names.contains(n),
        V::List { items, tail } => items.iter().chain(tail.as_ref()).any(|x| names_one_of(x, names)),
        _ => false,
    }
}

/// `s` at `at`, the place its parts were made for (a hole's call, where the
/// template has the hole).
fn respanned(s: &Syn, at: At) -> Syn {
    match &s.view() {
        V::List { items, tail } => {
            let items: Vec<Syn> = items.iter().map(|x| respanned(x, at)).collect();
            Syn::of_list(at, &items, tail.as_ref().map(|x| respanned(x, at)))
        }
        V::Vector(items) => Syn::vector(at, &items.iter().map(|x| respanned(x, at)).collect::<Vec<_>>()),
        _ => s.placed(at),
    }
}

/// Type `t`, which a template writes, read in module `m` (`#%toplevel`,
/// `#%fx` or a file's), at its place in expansion `made`: `(select m t)`;
/// of a definition's `(->* (param …) result)`, which is no type, each of
/// its types so.
fn selected(m: Sym, t: &Syn, made: u32, interner: &mut Interner) -> Syn {
    let at = t.at().in_expansion(made);
    if let Some([h, params, result]) = t.list().as_deref()
        && h.sym().is_some_and(|h| interner.name(h) == "->*")
        && let Some(ps) = params.list()
    {
        let ps: Vec<Syn> = ps.iter().map(|p| selected(m, p, made, interner)).collect();
        let ps = list_of(params.at().in_expansion(made), ps, None);
        return Syn::lst(at, vec![in_expansion(h, made), ps, selected(m, result, made, interner)]);
    }
    let select = interner.intern("select");
    Syn::lst(at, vec![Syn::symbol(at, select, interner), Syn::symbol(at, m, interner), in_expansion(t, made)])
}

/// `s`, each part of it at its place in expansion `made` (`transcribe`'s,
/// for a part nothing in is renamed or placed).
fn in_expansion(s: &Syn, made: u32) -> Syn {
    let at = s.at().in_expansion(made);
    match &s.view() {
        V::List { items, tail } => list_of(at, items.iter().map(|x| in_expansion(x, made)).collect(), tail.as_ref().map(|x| in_expansion(x, made))),
        V::Vector(items) => Syn::vector(at, &items.iter().map(|x| in_expansion(x, made)).collect::<Vec<_>>()),
        _ => s.placed(at),
    }
}

#[cfg(test)]
mod tests {
    /// The kernel's list `list`'s names, read in a heap of the test's own.
    fn kernel_names(list: &str) -> Vec<String> {
        let (mut heap, mut syms) = (fixpt_heap::Heap::unfixed(), crate::heap_syn::SymTable::default());
        let mut interner = fixpt_read::Interner::of_names(heap.names());
        crate::heap_syn::with_syntax(&mut heap, &mut syms, || {
            let forms = crate::heap_syn::read_syn_unplaced(super::KERNEL, &mut interner).expect("reads");
            super::kernel_list(&forms, &interner, list).iter().map(|w| interner.name(w.sym().expect("a name")).to_string()).collect()
        })
    }

    /// The kernel file's reserved words, which the expander written in
    /// FX-26 reads, are the Rust front end's keywords.
    #[test]
    fn the_kernels_reserved_words_are_the_keywords() {
        let words: Vec<String> = kernel_names("reserved-words");
        assert_eq!(words, crate::top::KEYWORDS);
    }

    /// The kernel's type forms are the checkers' (`parse.rs`'s `TYPE_FORMS`).
    #[test]
    fn the_kernels_type_forms_are_the_checkers() {
        let words: Vec<String> = kernel_names("type-forms");
        assert_eq!(words, crate::parse::TYPE_FORMS);
    }

    /// The FX-26 checker's keywords (`check-read-helpers.fx`'s
    /// `k-keywords`) are the Rust front end's.
    #[test]
    fn the_fx26_checkers_keywords_are_the_keywords() {
        let src = include_str!("check-read-helpers.fx");
        let list = src.split("(define k-keywords k-names").nth(1).expect("k-keywords");
        let list = &list[..list.find("))").expect("its end")];
        let words: Vec<&str> = list.split_whitespace().filter_map(|w| w.strip_prefix('\'')).collect();
        assert_eq!(words, crate::top::KEYWORDS);
    }

    /// The kernel's words of descriptions take in every type form's and
    /// effect form's name, which both checkers read at a list's head by the
    /// name alone; and the FX-26 checker's type forms are the Rust one's.
    #[test]
    fn the_description_heads_are_the_checkers() {
        let heads: Vec<String> = kernel_names("description-heads");
        for h in crate::parse::TYPE_FORMS.iter().chain(crate::parse::EFFECT_HEADS) {
            assert!(heads.iter().any(|x| x == h), "`{h}` is not among the kernel's `description-heads`");
        }
        let src = include_str!("check-read-helpers.fx");
        let list = src.split("(define k-type-forms k-names").nth(1).expect("k-type-forms");
        let list = &list[..list.find("))").expect("its end")];
        let words: Vec<&str> = list.split_whitespace().filter_map(|w| w.strip_prefix('\'')).collect();
        assert_eq!(words, crate::parse::TYPE_FORMS);
        // The effect forms' heads, `k-atom-head?`'s and `maxeff`.
        let src = include_str!("check-read.fx");
        let body = src.split("(define k-atom-head? (->* (string) bool)").nth(1).expect("k-atom-head?");
        let body = &body[..body.find("\n(define").expect("its end")];
        let mut atoms: Vec<&str> = body.split('"').skip(1).step_by(2).chain(["maxeff"]).collect();
        let mut want = crate::parse::EFFECT_HEADS.to_vec();
        atoms.sort();
        want.sort();
        assert_eq!(atoms, want);
    }

    /// Every form `parse_exp` reads by its head is a keyword, so a template
    /// that writes one is never read as a call of the top level's name.
    #[test]
    fn every_expression_form_is_a_keyword() {
        let src = include_str!("parse.rs");
        let body = src.split("fn parse_exp_syn(").nth(1).expect("parse_exp_syn");
        let body = &body[..body.find("\n    }\n").expect("its end")];
        let mut missing = Vec::new();
        for line in body.lines().filter(|l| l.starts_with("            \"") || l.starts_with("            head @ (") || l.starts_with("            loader @ (")) {
            let pattern = line.split("=>").next().unwrap_or("");
            for name in pattern.split('"').skip(1).step_by(2) {
                if !name.starts_with('%') && !crate::top::KEYWORDS.contains(&name) {
                    missing.push(name.to_string());
                }
            }
        }
        assert!(missing.is_empty(), "forms `parse_exp` reads that are not keywords: {missing:?}");
    }
}

/// Signature `sig`, inferred for `w`, as a message says it: in shapes and
/// facts, labelled by `w`'s first clause's pattern, if one says it; else in
/// Herman's form (`macros/shown.rs`).
fn shown_inferred(sig: &Syn, w: &Written, interner: &mut Interner) -> String {
    match shown::in_shapes(sig, w.clauses.first(), interner) {
        Some(c) => infer::sig_text(&c, interner),
        None => infer::sig_text(sig, interner),
    }
}

/// A hash of `s`'s atoms and shape, each atom by its value, below 2³¹ - 1
/// (FX-26's `syn-hash`, alike): a top-level form's key
/// (`Macros::form_begin`). Numbers count too, so that `(check 1)` and
/// `(check 2)` are not one key counted twice (Kayak's INCR_IMPED.md §5).
fn syn_hash(s: &Syn, interner: &Interner) -> i64 {
    const P: i64 = 2_147_483_647;
    let mix = |h: i64, x: i64| (h * 65599 + x) % P;
    let all = |h: i64, xs: &[Syn]| xs.iter().fold(h, |h, x| mix(h, syn_hash(x, interner)));
    let text = |t: &str| fixpt_heap::heap::string_hash_of(t) % P;
    match s.view() {
        V::Symbol(x) => mix(1, text(interner.name(x))),
        V::Str(t) => mix(2, text(&t)),
        V::Nil => 4,
        V::List { items, tail: None } => all(4, &items),
        V::List { items, tail: Some(t) } => mix(all(5, &items), syn_hash(&t, interner)),
        V::Vector(items) => all(6, &items),
        V::Number(n) => num_hash(&n),
        V::Char(c) => mix(9, c as i64),
        V::Bool(b) => mix(10, b as i64),
        V::Keyword(x) => mix(11, text(interner.name(x))),
        V::Bytevector(bs) => bs.iter().fold(12, |h, b| mix(h, *b as i64)),
    }
}

/// A number's part of [`syn_hash`]: an integer its value modulo the hash's
/// prime, as FX-26's `modulo` (a bignum's alike), a real its text as
/// `f64->string` writes it.
fn num_hash(n: &fixpt_read::Num) -> i64 {
    use fixpt_read::Num;
    const P: i64 = 2_147_483_647;
    let mix = |h: i64, x: i64| (h * 65599 + x) % P;
    match n {
        Num::Int(i) => mix(7, i.rem_euclid(P)),
        Num::Big { negative, digits, radix } => {
            let v = digits.chars().fold(0i64, |v, c| (v * *radix as i64 + c.to_digit(*radix).unwrap_or(0) as i64) % P);
            mix(7, if *negative { (P - v) % P } else { v })
        }
        Num::Ratio(a, b) => mix(mix(13, num_hash(a)), num_hash(b)),
        Num::Real(x) => mix(8, fixpt_heap::heap::string_hash_of(&fixpt_runtime::num::format_flonum(*x)) % P),
    }
}

/// `(elem ...)`'s members, its `mu`'s body, `elem` under it: `()`, and the pair of an
/// element and the list. An element that exports a rib, the pair exports
/// its entries, each said from the pair's root, `(A …)`, then the rest's,
/// `(D rib)`: an address is from its region's root, and an element written
/// out is in the pair's region (an element given by ellipsis is a region of
/// its own, which `seq_of` gives back its export as said from it).
pub(crate) fn seq_members(elem: &Rc<STy>) -> Vec<Rc<STy>> {
    let rest = Rc::new(STy::Var(0));
    let none = || Rc::new(STy::Export(Rc::new(STy::Nil), Bind::Rib(Vec::new())));
    match &**elem {
        STy::Export(e, Bind::Rib(es)) => {
            let mut both: Vec<(Addr, Delta)> = es.iter().map(|(a, d)| (std::iter::once(true).chain(a.iter().copied()).collect(), d.clone())).collect();
            both.push((vec![false], Delta::Rib));
            vec![none(), Rc::new(STy::Export(Rc::new(STy::Pair(e.clone(), rest)), Bind::Rib(both)))]
        }
        STy::Export(..) => {
            let pair = Rc::new(STy::Pair(elem.clone(), rest));
            vec![none(), Rc::new(STy::Export(pair, Bind::Rib(vec![(vec![true], Delta::Rib), (vec![false], Delta::Rib)])))]
        }
        _ => vec![Rc::new(STy::Nil), Rc::new(STy::Pair(elem.clone(), rest))],
    }
}

/// What macro `name`, its signature not written, is refused with, the one
/// inferred, `shown`, not fitting its clauses, `why`: refused, said so on a
/// line of its own, then what was inferred and how one is written.
fn refused_inferred(name: &str, shown: &str, why: &str) -> String {
    format!("`{name}` is refused: no signature is written, and the one inferred from its clauses does not fit them: {why}\n  inferred: {shown}\n  write one: (define-syntax {name} SIGNATURE (syntax-rules …))")
}
