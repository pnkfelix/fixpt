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
//!     | (mu v σ) | v | (union σ …)         recursion, alternatives
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
//! A macro whose signature is `(-> σ type)` makes a description: its uses
//! are where a description is, in a template's descriptions too, its
//! template a description (`docs/research/datatype-macro.md`, "Keyword
//! constructors: decided", 7).
//!
//! A macro whose signature is `(-> σ defn)` makes definitions
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
use fixpt_read::{Datum, Interner, Span, Sym, Syntax};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

mod infer;
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
    /// A module's item, as a program's walk takes one (`scope-forms`): a
    /// definition, a string (a comment), or an expression run as the module
    /// is made.
    Item,
    Nil,
    Literal(Sym),
    Pair(Rc<STy>, Rc<STy>),
    Import(Rc<STy>, Bind),
    Export(Rc<STy>, Bind),
    /// A `mu`, by its number in `Macros::mus`; and its variable, the same.
    Mu(usize),
    /// What may be placed any number of times.
    Many(Rc<STy>),
    /// An `expr` or `bvar` with its type, effect or both written: a typed
    /// hole (`typed-macros.md`, "Proposed: typed holes").
    Typed(Rc<STy>, Hole),
    Union(Vec<Rc<STy>>),
}

/// What a typed hole says: its type and its effect, each as written, if it
/// is (left out, the macro is polymorphic in it).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Hole {
    ty: Option<Syntax>,
    effect: Option<Syntax>,
}

impl Hole {
    /// Whether its effect is written `pure`, so that running it twice does
    /// nothing twice.
    fn pure(&self, interner: &Interner) -> bool {
        self.effect.as_ref().and_then(|e| e.as_symbol()).is_some_and(|e| interner.name(e) == "pure")
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
    Qualified,
    Plain,
    Bound,
}

/// A macro defined: its signature and clauses.
#[derive(Debug)]
struct Macro {
    sig: Rc<STy>,
    /// Whether it makes definitions, `(-> σ defn)`.
    defn: bool,
    /// Whether it makes a description, `(-> σ type)`.
    desc: bool,
    /// The binders of its signature's `(poly (binder …) σ)`, if it has one.
    poly: Vec<Syntax>,
    clauses: Vec<Clause>,
    /// The text it was read from, its templates' places in it.
    text: Option<std::sync::Arc<str>>,
    /// A procedural macro's transformer (`procedural`), which has no
    /// signature nor clauses: `sig` says nothing of it.
    procedural: Option<Rc<procedural::Procedural>>,
}

/// A clause: its pattern (of the operands), its template, and what is done
/// to the template's names where it is transcribed, by their paths in it.
#[derive(Debug)]
struct Clause {
    pattern: Syntax,
    /// Its pattern variables that are names (`bvar`, `dvar`, `id`), which
    /// match a name alone (a `label` may be a keyword).
    names: HashSet<Sym>,
    template: Syntax,
    actions: HashMap<Vec<bool>, Action>,
    /// Its pattern's variables, in the order the pattern has them.
    pvars: Vec<(Sym, PInfo)>,
    /// Each typed hole's type, as a use reads it (`(select #%toplevel T)`),
    /// which the use's expression is held to, `(the T e)`; none where the
    /// type names the macro's `poly` binders, which no use can write.
    contracts: HashMap<Sym, Syntax>,
    /// Where its macro is defined, what its aliases are read in.
    def_env: hygiene::DefEnv,
}

/// What becomes of one of a template's parts: a name made fresh, one name
/// for the binder found at a path and for each reference to it; a name
/// free in the template, its alias, `%~N:name`, which the resolution after
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
    Rename(Vec<bool>, usize),
    /// A name free in the template: its alias, `%~N:name`, which the
    /// resolution after expansion makes the name where the macro is
    /// defined (`hygiene`).
    Alias,
    ModuleType(Sym),
    StandardType,
    MacroHead(Sym),
}

/// What a file's macros are defined in (`Macros::define_file`): the
/// hidden global every load of the file is, `%shared:key`; the values and
/// types its module shows; each of its macros' names, and the name the
/// importer has it by, which no program writes; and which names are
/// standard.
pub struct FileScope<'a> {
    pub shared: Sym,
    pub values: std::collections::HashSet<Sym>,
    pub types: std::collections::HashSet<Sym>,
    pub internal: HashMap<Sym, Sym>,
    pub is_standard: &'a dyn Fn(Sym) -> bool,
}

/// The macros defined, and the syntax types of the kernel's forms, for
/// checking templates. Cloned to be put back (`Checker::macros_kept`).
#[derive(Clone, Default)]
pub struct Macros {
    mus: Vec<Rc<STy>>,
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
    defined_at: HashMap<Sym, Span>,
    /// Whether a template is being transcribed for its check, its holes'
    /// calls in place of a use's expressions (`template_checks`).
    checking: bool,
}

/// What the expander saw of `with`s, for the checkers, and the shapes it
/// knows of the modules forms open.
#[derive(Clone, Default)]
pub(crate) struct Withs {
    /// By each `with` form's place, the macros used in its body by names
    /// written in the source, each with the use's place: refused there if
    /// the module gives a value of the name (`Checker::with_as`), which the
    /// program would seem to call, and the expander cannot see.
    pub(crate) with_uses: HashMap<Span, Vec<(Sym, Span)>>,
    /// By each `(with m name)` form's place that a template wrote, the name
    /// and its place: refused there if the module gives no value of it
    /// (`Checker::with_as`), which would otherwise be what it is where the
    /// macro is used, a binding there capturing it.
    pub(crate) projections: HashMap<Span, (Sym, Span)>,
    /// The shapes known (`shapes`): the top level's names', files'.
    shapes: shapes::Known,
    /// Where the macro each expansion's aliases are of was defined, by the
    /// expansion's number (`hygiene::DefEnv`); a template's check is
    /// expansion 0.
    pub(crate) def_envs: HashMap<u32, hygiene::DefEnv>,
    /// How many binders at uses the resolution renamed, which would have
    /// captured a name a module file's own macro introduces (`%x~N`).
    pub(crate) captors: usize,
    /// Where the macros defined now are, unless a file's scope is given:
    /// the top level, or a module file's items, as its own macros are
    /// (`Checker::file_own_expanded`).
    pub(crate) def_env: hygiene::DefEnv,
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
fn kernel_list(forms: &[Syntax], interner: &Interner, name: &str) -> Vec<Syntax> {
    let def = forms.iter().find_map(|f| match f.as_proper_list() {
        Some([_, n, _, q]) if n.as_symbol().is_some_and(|n| interner.name(n) == name) => Some(q.clone()),
        _ => None,
    });
    let quoted = def.and_then(|q| q.as_proper_list().and_then(|l| l.get(1).cloned())).expect("the kernel's list");
    quoted.as_proper_list().expect("a list").to_vec()
}

/// What a transcription has made so far: each binder's fresh name, by its
/// path and the repetitions it is in; and how many times each repeated
/// binder was repeated, by its path and the repetitions around that.
#[derive(Default)]
struct Made {
    fresh: HashMap<(Vec<bool>, Vec<usize>), Sym>,
    counts: HashMap<(Vec<bool>, Vec<usize>), usize>,
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
    syn: Syntax,
    /// Its path from the template's (or pattern's) root.
    path: Vec<bool>,
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

/// Syntax aligned with syntax types, as a tree of `Node`s.
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
}

/// A part to fill: its node, its type, its syntax, and the node its
/// addresses are from.
type Step = (usize, Rc<STy>, Syntax, usize);

impl Macros {
    fn ensure_kernel(&mut self, interner: &mut Interner) -> R<()> {
        if !self.k.forms.is_empty() {
            return Ok(());
        }
        let forms = fixpt_read::Reader::new(KERNEL, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX26, interner)
            .read_all()
            .map_err(|e| FxError::at(e.span, format!("the kernel's syntax types: {}", e.message)))?;
        let mut k = Kernel::default();
        // `defn`, which the kernel's signatures name, and no macro's.
        let mut named: HashMap<Sym, Rc<STy>> = HashMap::from([(interner.intern("defn"), Rc::new(STy::Defn))]);
        for f in &kernel_list(&forms, interner, "kernel-forms") {
            let items = f.as_proper_list().expect("a kernel entry");
            let what = interner.name(items[0].as_symbol().expect("a head")).to_string();
            let name = items[1].as_symbol().expect("a name");
            let t = self.sty(&items[2], interner, &named, &mut Vec::new())?;
            match what.as_str() {
                "define" => _ = named.insert(name, t),
                "definition" => _ = k.definitions.insert(interner.name(name).to_string(), t),
                _ => _ = k.forms.insert(interner.name(name).to_string(), t),
            }
        }
        for f in &kernel_list(&forms, interner, "scope-forms") {
            let items = f.as_proper_list().expect("a scope entry");
            let what = interner.name(items[0].as_symbol().expect("a head")).to_string();
            let name = items[1].as_symbol().expect("a name");
            let t = self.sty(&items[2], interner, &named, &mut Vec::new())?;
            match what.as_str() {
                "define" => _ = named.insert(name, t),
                "definition" => _ = k.scope_definitions.insert(interner.name(name).to_string(), t),
                _ => _ = k.scope_forms.insert(interner.name(name).to_string(), t),
            }
        }
        let names = |list: &str, i: &Interner| kernel_list(&forms, i, list).iter().map(|w| i.name(w.as_symbol().expect("a word")).to_string()).collect::<HashSet<_>>();
        k.heads = names("description-heads", interner);
        k.words = names("description-words", interner);
        k.type_forms = names("type-forms", interner);
        self.k = Rc::new(k);
        Ok(())
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
        Some(match self.defined_at.get(&name) {
            Some(d) if d.file == at.file && d.start > at.start => Err(*d),
            _ => Ok(()),
        })
    }

    /// A syntax type read: `named`'s names (the kernel's abbreviations), and
    /// the `mu` variables in scope, innermost last.
    fn sty(&mut self, s: &Syntax, interner: &Interner, named: &HashMap<Sym, Rc<STy>>, mus: &mut Vec<(Sym, usize)>) -> R<Rc<STy>> {
        let bad = |why: &str| FxError::at(s.span, format!("a syntax type: {why}"));
        let t = match &s.datum {
            Datum::Nil => STy::Nil,
            Datum::Symbol(n) => {
                if let Some((_, id)) = mus.iter().rev().find(|(v, _)| v == n) {
                    STy::Mu(*id)
                } else if let Some(t) = named.get(n) {
                    return Ok(t.clone());
                } else {
                    match interner.name(*n) {
                        "expr" => STy::Expr,
                        "lambda" => STy::Lambda,
                        "bvar" => STy::Bvar,
                        "id" => STy::Id,
                        "data" => STy::Data,
                        "type" => STy::Type,
                        "label" => STy::Label,
                        "dvar" => STy::Dvar,
                        "kind" => STy::Kind,
                        "item" => STy::Item,
                        other => return Err(bad(&format!("`{other}` is none (`expr`, `bvar`, `id`, `data`, `type`, `label`, `lambda`, `dvar`, `kind`, `item`, or a `mu`'s variable)"))),
                    }
                }
            }
            // `(σ … σ ...)`: a list ending in any number of the last `σ`.
            Datum::List { items, tail: None } if items.len() >= 2 && is_ellipsis(&items[items.len() - 1], interner) => {
                let elem = self.sty(&items[items.len() - 2], interner, named, mus)?;
                let mut t = self.seq(elem);
                for x in items[..items.len() - 2].iter().rev() {
                    t = Rc::new(STy::Pair(self.sty(x, interner, named, mus)?, t));
                }
                return Ok(t);
            }
            Datum::List { items, tail } => {
                let head = items[0].as_symbol().map(|h| interner.name(h));
                match (head, &items[..], tail) {
                    (Some("import" | "export"), [_, body, b], None) => {
                        let body = self.sty(body, interner, named, mus)?;
                        let b = bind(b, interner)?;
                        if head == Some("import") { STy::Import(body, b) } else { STy::Export(body, b) }
                    }
                    (Some("mu"), [_, v, body], None) => {
                        let v = v.as_symbol().ok_or_else(|| bad("`(mu variable type)`"))?;
                        let id = self.mus.len();
                        self.mus.push(Rc::new(STy::Nil));
                        mus.push((v, id));
                        let body = self.sty(body, interner, named, mus);
                        mus.pop();
                        let body = body?;
                        if !guarded(&body, id) {
                            return Err(bad("a `mu`'s variable is used where no pair is around it (Herman's types are contractive)"));
                        }
                        self.mus[id] = body;
                        STy::Mu(id)
                    }
                    (Some("union"), [_, ms @ ..], None) => {
                        let ms = ms.iter().map(|m| self.sty(m, interner, named, mus)).collect::<R<Vec<_>>>()?;
                        for (i, a) in ms.iter().enumerate() {
                            for b in &ms[i + 1..] {
                                if self.overlap(a, b, OVERLAP_DEPTH) {
                                    return Err(bad("a `union`'s members must be told apart by their shapes in the source (an `expr` may be anything)"));
                                }
                            }
                        }
                        STy::Union(ms)
                    }
                    (Some("many"), [_, body], None) => STy::Many(self.sty(body, interner, named, mus)?),
                    // `(expr #:type T #:effect E)`, `(bvar #:type T)`: a list
                    // whose second is a keyword, which no syntax type is.
                    (Some(kind @ ("expr" | "bvar" | "lambda")), [_, k, ..], None) if matches!(k.datum, Datum::Keyword(_)) => {
                        let hole = hole(&items[1..], kind, s, interner)?;
                        let core = match kind {
                            "expr" => STy::Expr,
                            "bvar" => STy::Bvar,
                            _ => STy::Lambda,
                        };
                        STy::Typed(Rc::new(core), hole)
                    }
                    (Some("literal"), [_, n], None) => STy::Literal(n.as_symbol().ok_or_else(|| bad("`(literal name)`"))?),
                    _ => {
                        let rest = match (items.len(), tail) {
                            (1, None) => Rc::new(STy::Nil),
                            (1, Some(t)) => self.sty(t, interner, named, mus)?,
                            _ => self.sty(&Syntax::new(s.span, Datum::List { items: items[1..].to_vec(), tail: tail.clone() }), interner, named, mus)?,
                        };
                        STy::Pair(self.sty(&items[0], interner, named, mus)?, rest)
                    }
                }
            }
            _ => return Err(bad("not one")),
        };
        Ok(Rc::new(t))
    }

    /// `(elem ...)`: `(mu l (union () (elem . l)))`, and if `elem` exports,
    /// each element's export together, as a `let`'s bindings do; a binder
    /// alone, `bvar` or `dvar`, exports itself.
    fn seq(&mut self, elem: Rc<STy>) -> Rc<STy> {
        let elem = match &*elem {
            STy::Bvar => Rc::new(STy::Export(elem, Bind::Rib(vec![(Vec::new(), Delta::Var)]))),
            STy::Dvar => Rc::new(STy::Export(elem, Bind::Rib(vec![(Vec::new(), Delta::Dvar)]))),
            _ => elem,
        };
        let id = self.mus.len();
        self.mus.push(Rc::new(STy::Nil));
        let pair = Rc::new(STy::Pair(elem.clone(), Rc::new(STy::Mu(id))));
        let body = if matches!(&*elem, STy::Export(..)) {
            let none = Rc::new(STy::Export(Rc::new(STy::Nil), Bind::Rib(Vec::new())));
            vec![none, Rc::new(STy::Export(pair, Bind::Rib(vec![(vec![true], Delta::Rib), (vec![false], Delta::Rib)])))]
        } else {
            vec![Rc::new(STy::Nil), pair]
        };
        self.mus[id] = Rc::new(STy::Union(body));
        Rc::new(STy::Mu(id))
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
        let STy::Mu(id) = &**t else { return None };
        let STy::Union(ms) = &*self.mus[*id] else { return None };
        if let Some(elem) = self.cage_seq_of(*id, ms) {
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
                STy::Pair(a, _) if matches!(&**rest, STy::Mu(j) if j == id) => {
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
    fn cage_seq_of(&self, id: usize, ms: &[Rc<STy>]) -> Option<Rc<STy>> {
        let (mut elems, mut nil) = (Vec::new(), false);
        for m in ms {
            let STy::Export(core, Bind::Cage(rings)) = &**m else { return None };
            match (&**core, &rings[..]) {
                (STy::Nil, []) => nil = true,
                (STy::Pair(a, d), [Ring::At(rest), own]) if rest == &vec![false] => {
                    let STy::Import(r, inner) = &**d else { return None };
                    if !matches!(&**r, STy::Mu(j) if *j == id) {
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
    /// `(shape A)`), which a program's walk alone knows; `mu`s seen through
    /// once (`seen`).
    fn binds_nothing(&self, t: &STy, seen: &mut Vec<usize>) -> bool {
        match t {
            STy::Item | STy::Import(..) | STy::Export(..) => false,
            STy::Pair(a, d) => self.binds_nothing(a, seen) && self.binds_nothing(d, seen),
            STy::Many(b) | STy::Typed(b, _) => self.binds_nothing(b, seen),
            STy::Union(ms) => ms.iter().all(|m| self.binds_nothing(m, seen)),
            STy::Mu(id) if seen.contains(id) => true,
            STy::Mu(id) => {
                seen.push(*id);
                self.binds_nothing(&self.mus[*id], seen)
            }
            _ => true,
        }
    }

    /// The type at `t`, its annotations, `mu`s and unions seen through
    /// to what is under them (for overlap and fit).
    fn unfold<'a>(&'a self, t: &'a Rc<STy>) -> &'a Rc<STy> {
        match &**t {
            STy::Import(b, _) | STy::Export(b, _) | STy::Many(b) | STy::Typed(b, _) => self.unfold(b),
            STy::Mu(id) => self.unfold(&self.mus[*id]),
            _ => t,
        }
    }

    /// Whether some source syntax could be of both `a` and `b` (Herman's
    /// shapes, §5.2.3): `expr` may be anything but a form's name; looked
    /// at to `depth` pairs, past which they are taken to overlap.
    fn overlap(&self, a: &Rc<STy>, b: &Rc<STy>, depth: usize) -> bool {
        use STy::*;
        let (a, b) = (self.unfold(a), self.unfold(b));
        match (&**a, &**b) {
            (Union(ms), _) => ms.iter().any(|m| self.overlap(m, b, depth)),
            (_, Union(ms)) => ms.iter().any(|m| self.overlap(a, m, depth)),
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
    fn fits(&self, t: &Rc<STy>, s: &Syntax, mode: Mode, interner: &Interner, pvars: &HashMap<Sym, PInfo>) -> bool {
        self.fits_within(t, s, mode, interner, pvars, FITS_DEPTH)
    }

    /// `fits`, looking no deeper than `depth` lists: a `union`'s members
    /// differ within `OVERLAP_DEPTH` (`sty`), so that is enough to choose
    /// one, and what is chosen is aligned whole; and a long list is not
    /// looked through at each of its parts.
    fn fits_within(&self, t: &Rc<STy>, s: &Syntax, mode: Mode, interner: &Interner, pvars: &HashMap<Sym, PInfo>, depth: usize) -> bool {
        use STy::*;
        // `(p ...)`, where a list of elements `p` fits may be.
        if matches!(mode, Mode::Pattern | Mode::Template) && let Some(x) = ellipsis(s, interner) {
            return self.seq_of(self.peel(t)).is_some_and(|(e, _)| self.fits_within(&e, &x, mode, interner, pvars, depth));
        }
        if let Some(n) = s.as_symbol() {
            let lit = matches!(&**self.unfold(t), Literal(_));
            // A pattern variable placed fits anything but, if it is a name,
            // a list's shape, which a name never has.
            let name = pvars.get(&n).is_some_and(|p| matches!(&*p.core, Bvar | Dvar | Id | Label));
            let list = matches!(&**self.unfold(t), Pair(..) | Nil | Lambda);
            if (mode == Mode::Pattern && !lit && interner.name(n) != "_") || (mode == Mode::Template && pvars.contains_key(&n) && !(name && list)) {
                return true;
            }
        }
        match &**self.unfold(t) {
            Union(ms) => ms.iter().any(|m| self.fits_within(m, s, mode, interner, pvars, depth)),
            Pair(a, d) => match &s.datum {
                // No parts: what its tail is.
                Datum::List { items, tail } if items.is_empty() => tail.as_deref().is_some_and(|x| self.fits_within(t, x, mode, interner, pvars, depth)),
                Datum::List { items, tail } => depth == 0 || (self.fits_within(a, &items[0], mode, interner, pvars, depth - 1) && self.fits_rest(d, items, 1, tail.as_deref(), s.span, mode, interner, pvars, depth - 1)),
                _ => false,
            },
            Nil => matches!(s.datum, Datum::Nil),
            Literal(n) => s.as_symbol() == Some(*n),
            Bvar | Dvar => s.as_symbol().is_some_and(|n| mode == Mode::Program || !reserved(interner.name(n))),
            Id => s.as_symbol().is_some(),
            Label => matches!(s.datum, Datum::Keyword(_)) || (matches!(mode, Mode::Use | Mode::Program) && s.as_symbol().is_some()) || (mode == Mode::Program && matches!(s.datum, Datum::Number(_))),
            Expr => (mode == Mode::Program || !s.as_symbol().is_some_and(|n| reserved(interner.name(n)))) && !matches!(s.datum, Datum::Nil),
            Lambda => lambda_shaped(s, interner),
            Defn => matches!(s.datum, Datum::List { .. }),
            Data | Type | Kind | Item => true,
            Import(..) | Export(..) | Mu(_) | Many(_) | Typed(..) => unreachable!("unfolded"),
        }
    }

    /// `fits_within` of the rest of a list, `items` from `k` on and then
    /// `tail`, looked at where it is: a long list's rest is not made again
    /// at each of its parts.
    #[allow(clippy::too_many_arguments)]
    fn fits_rest(&self, t: &Rc<STy>, items: &[Syntax], k: usize, tail: Option<&Syntax>, span: Span, mode: Mode, interner: &Interner, pvars: &HashMap<Sym, PInfo>, depth: usize) -> bool {
        use STy::*;
        if k == items.len() {
            return match tail {
                Some(t1) => self.fits_within(t, t1, mode, interner, pvars, depth),
                None => self.fits_within(t, &Syntax::new(span, Datum::Nil), mode, interner, pvars, depth),
            };
        }
        // What a pattern or template writes by ellipsis, or a lambda's
        // shape, is read from the rest made whole (a template is small).
        let whole = || Syntax::new(span, Datum::List { items: items[k..].to_vec(), tail: tail.map(|t| Box::new(t.clone())) });
        if matches!(mode, Mode::Pattern | Mode::Template) {
            return self.fits_within(t, &whole(), mode, interner, pvars, depth);
        }
        match &**self.unfold(t) {
            Union(ms) => ms.iter().any(|m| self.fits_rest(m, items, k, tail, span, mode, interner, pvars, depth)),
            Pair(a, d) => depth == 0 || (self.fits_within(a, &items[k], mode, interner, pvars, depth - 1) && self.fits_rest(d, items, k + 1, tail, span, mode, interner, pvars, depth - 1)),
            Nil | Literal(_) | Bvar | Dvar | Id | Label => false,
            Lambda => lambda_shaped(&whole(), interner),
            Expr | Defn | Data | Type | Kind | Item => true,
            Import(..) | Export(..) | Mu(_) | Many(_) | Typed(..) => unreachable!("unfolded"),
        }
    }

    /// `(define-syntax name [σ] (syntax-rules (literal …) ((_ . pattern)
    /// template) …))`, its signature written or inferred; or a
    /// `define-syntax-rec` of them: checked, and defined; their names. A template's free name is the top level's
    /// where the macro is used (`Action::Toplevel`).
    pub fn define(&mut self, form: &Syntax, interner: &mut Interner) -> R<Vec<Sym>> {
        let names = self.define_in(form, interner, None)?;
        for n in &names {
            self.defined_at.insert(*n, form.span);
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
    pub fn template_checks(&mut self, name: Sym, interner: &mut Interner) -> R<Vec<Syntax>> {
        let m = self.defined[&name].clone();
        let mut out = Vec::new();
        for c in &m.clauses {
            if c.pvars.iter().all(|(_, p)| p.hole.is_none()) {
                continue;
            }
            out.push(self.template_check(name, &m, c, interner)?);
        }
        Ok(out)
    }

    fn template_check(&mut self, name: Sym, m: &Macro, c: &Clause, interner: &mut Interner) -> R<Syntax> {
        let at = c.template.span;
        let shown = |n: Sym, i: &Interner| i.name(n).to_string();
        let place = |n: Sym| find_symbol(&c.pattern, n).map_or(c.pattern.span, |s| s.span);
        let sym = |s: &str, i: &mut Interner| Syntax::symbol(at, i.intern(s));
        let mut binders = m.poly.clone();
        let mut binds: HashMap<Sym, Syntax> = HashMap::new();
        // Each binder, a fresh name for the holes in its scope to be given.
        for (n, p) in &c.pvars {
            match &*p.core {
                STy::Expr | STy::Lambda => {}
                STy::Bvar => {
                    self.fresh += 1;
                    let f = format!("%{}:{}", shown(*n, interner), self.fresh);
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
                    let ty = c.pvars.iter().find(|(x, _)| x == b).and_then(|(_, q)| q.hole.as_ref()?.ty.clone());
                    let Some(ty) = ty else {
                        return Err(FxError::at(place(*b), format!("`{}` binds a variable `{}` is in the scope of: its type is written, `(bvar #:type T)`, where a macro's parts are typed", shown(*b, interner), shown(*n, interner))));
                    };
                    scope.push((*b, ty));
                }
            }
            // A part left out, a binder of the procedure's, named for the
            // hole (`%type-of-e`), what a message about it says.
            let mut part = |given: &Option<Syntax>, kind: &str, i: &mut Interner| match given {
                Some(s) => s.clone(),
                None => {
                    let v = Syntax::symbol(at, i.intern(&format!("%{kind}-of-{}", shown(*n, i))));
                    binders.push(Syntax::list(at, vec![v.clone(), Syntax::symbol(at, i.intern(kind))]));
                    v
                }
            };
            // A lambda's stand-in is a lambda: its procedure, given, called
            // with the lambda's arguments, of the types its type says; so
            // its type is written, `(subr E (A …) R)`, and making it does
            // nothing.
            let lambda_ty = if lambda {
                let written = h.ty.as_ref().and_then(|t| match t.as_proper_list() {
                    Some([s, _, args, _]) if s.as_symbol().is_some_and(|s| interner.name(s) == "subr") && (args.as_proper_list().is_some() || matches!(args.datum, Datum::Nil)) => Some(t.clone()),
                    _ => None,
                });
                let Some(written) = written else {
                    return Err(FxError::at(place(*n), format!("`{}` is a `lambda` part: its type is written, `(lambda #:type (subr E (A …) R))`, which its stand-in in the check is made of", shown(*n, interner))));
                };
                Some(written)
            } else {
                None
            };
            let ty = part(&h.ty, "type", interner);
            let effect = if lambda { sym("pure", interner) } else { part(&h.effect, "effect", interner) };
            self.fresh += 1;
            let hole = sym(&format!("%h:{}:{}", shown(*n, interner), self.fresh), interner);
            let args: Vec<Syntax> = scope.iter().map(|(_, t)| t.clone()).collect();
            let subr = Syntax::list(at, vec![sym("subr", interner), effect, list_of(at, args, None), ty]);
            params.push(Syntax::list(at, vec![hole.clone(), subr]));
            let call = Syntax::list(at, std::iter::once(hole).chain(scope.iter().map(|(b, _)| binds[b].clone())).collect());
            let stand_in = match lambda_ty {
                None => call,
                Some(written) => {
                    let items = written.as_proper_list().expect("a `subr`");
                    let arg_types = items[2].as_proper_list().map(|l| l.to_vec()).unwrap_or_default();
                    let mut params = Vec::new();
                    let mut names = vec![call];
                    for a in arg_types {
                        self.fresh += 1;
                        let v = sym(&format!("%a:{}", self.fresh), interner);
                        params.push(Syntax::list(at, vec![v.clone(), a]));
                        names.push(v);
                    }
                    Syntax::list(at, vec![sym("lambda", interner), list_of(at, params, None), Syntax::list(at, names)])
                }
            };
            binds.insert(*n, stand_in);
        }
        self.checking = true;
        self.withs.def_envs.insert(0, c.def_env.clone());
        let body = self.transcribe(c, &c.template, &mut Vec::new(), &binds, &mut Made::default(), &mut Vec::new(), 0, interner)?;
        self.checking = false;
        let lambda = Syntax::list(at, vec![sym("lambda", interner), list_of(at, params, None), body]);
        let made = if binders.is_empty() { lambda } else { Syntax::list(at, vec![sym("plambda", interner), Syntax::list(at, binders), lambda]) };
        self.fresh += 1;
        let hidden = sym(&format!("%template:{}:{}", shown(name, interner), self.fresh), interner);
        Ok(Syntax::list(at, vec![sym("define", interner), hidden, made]))
    }

    /// `f` run with a module file's own macros in place of these: none but
    /// the file's, which it defines as it goes, where its items are
    /// (`hygiene::DefEnv::Within`), read from `text`; these put back after.
    /// A file sees the standard environment alone, no macro of the
    /// program's.
    pub(crate) fn in_file_scope<T>(&mut self, text: &str, f: impl FnOnce(&mut Macros) -> T) -> T {
        let defined = std::mem::take(&mut self.defined);
        let defined_at = std::mem::take(&mut self.defined_at);
        let def_env = std::mem::replace(&mut self.withs.def_env, hygiene::DefEnv::Within);
        let reading = self.reading.replace(std::sync::Arc::from(text));
        let r = f(self);
        self.defined = defined;
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
            Some(f) => hygiene::DefEnv::File { shared: f.shared, values: Rc::new(f.values.clone()) },
        }
    }

    /// A file's macros, `forms` its `define-syntax`es (each with whether it
    /// is hidden), defined as the file means them (`FileScope`), each by
    /// the name the importer has it by, `scope.internal`'s, and each not
    /// hidden that `taken` takes by its own name too: what `(import-with-syntax
    /// lib)` brings (`(only name …)`, `(except name …)`).
    /// `at`: the `import-with-syntax`.
    pub fn define_file(&mut self, forms: &[(Syntax, bool)], scope: &FileScope, taken: &dyn Fn(Sym) -> bool, at: Span, interner: &mut Interner) -> R<()> {
        self.ensure_kernel(interner)?;
        // The file's macros defined among themselves, by their names in it,
        // as its templates name them.
        // Its recursive syntax types go on from the program's, which take
        // them back: the signatures refer to them by place.
        let mut own = Macros { mus: std::mem::take(&mut self.mus), k: self.k.clone(), defined: HashMap::new(), fresh: self.fresh, reading: self.reading.clone(), defined_at: HashMap::new(), checking: false, withs: Box::default() };
        let mut made = Vec::new();
        let mut defined = Ok(());
        for (form, hidden) in forms {
            match own.define_in(form, interner, Some(scope)) {
                Ok(ns) => made.extend(ns.into_iter().map(|n| (n, *hidden))),
                Err(e) => {
                    defined = Err(e);
                    break;
                }
            }
        }
        self.mus = std::mem::take(&mut own.mus);
        self.fresh = own.fresh;
        defined?;
        for (name, hidden) in made {
            let m = own.defined[&name].clone();
            if !hidden && taken(name) {
                if self.defined.contains_key(&name) {
                    let shown = interner.name(name);
                    return Err(FxError::at(forms[0].0.span, format!("`{shown}` is a macro defined already: a file's may not be defined again")));
                }
                self.defined.insert(name, m.clone());
                self.defined_at.insert(name, at);
            }
            self.defined.insert(scope.internal[&name], m);
        }
        Ok(())
    }

    /// `define`, in a file's scope if `file` is given: the macros' names.
    fn define_in(&mut self, form: &Syntax, interner: &mut Interner, file: Option<&FileScope>) -> R<Vec<Sym>> {
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

    fn define_written(&mut self, ws: &[Written], interner: &mut Interner, file: Option<&FileScope>) -> R<Vec<Sym>> {
        if let [w @ Written { procedural: Some((style, code)), .. }] = ws {
            let def_env = self.def_env_of(file);
            return self.define_procedural(w.name, *style, code, def_env, interner);
        }
        if let Some(w) = ws.iter().find(|w| w.procedural.is_some()) {
            return Err(FxError::at(w.span, "a procedural macro is defined alone, by `define-syntax`"));
        }
        let mut sigs = Vec::new();
        for w in ws {
            let s = match &w.sig {
                Some(sig) => {
                    let s = self.signature(sig, interner)?;
                    self.defined.insert(w.name, Rc::new(Macro { sig: s.1.clone(), defn: s.2, desc: s.3, poly: s.0.clone(), clauses: Vec::new(), text: None, procedural: None }));
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
                let shown = infer::sig_text(&sig, interner);
                let name = interner.name(w.name).to_string();
                let said = |e: FxError| FxError::at(e.span, format!("{}; `{name}`'s signature, inferred, is `{shown}`: write one if it means another", e.message));
                let parsed = self.signature(&sig, interner).map_err(said)?;
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
            let mut checked = Vec::new();
            for c in &w.clauses {
                let r = self.clause(c, &sig, defn, desc, &poly, &w.lits, interner, file);
                match (r, inferred.iter().find(|(n, _)| *n == w.name)) {
                    (Ok(c), _) => checked.push(c),
                    (Err(e), None) => return Err(e),
                    (Err(e), Some((_, shown))) => {
                        return Err(FxError::at(e.span, format!("{}; `{}`'s signature, inferred, is `{shown}`: write one if it means another", e.message, interner.name(w.name))));
                    }
                }
            }
            out.push((w.name, Macro { sig, defn, desc, poly, clauses: checked, text: self.reading.clone(), procedural: None }));
        }
        Ok(out
            .into_iter()
            .map(|(n, m)| {
                self.defined.insert(n, Rc::new(m));
                n
            })
            .collect())
    }

    /// Procedural macro `name`, its transformer `code` checked at its
    /// style's type in the transformers' session (`procedural::run`).
    fn define_procedural(&mut self, name: Sym, style: procedural::Style, code: &Syntax, def_env: hygiene::DefEnv, interner: &mut Interner) -> R<Vec<Sym>> {
        let text = fixpt_read::write_syntax(code, interner);
        procedural::run(&procedural::checked(style, &text)).map_err(|e| FxError::at(code.span, format!("`{}`'s transformer: {e}", interner.name(name))))?;
        let p = procedural::Procedural { style, code: text, def_env };
        let m = Macro { sig: Rc::new(STy::Expr), defn: false, desc: false, poly: Vec::new(), clauses: Vec::new(), text: None, procedural: Some(Rc::new(p)) };
        self.defined.insert(name, Rc::new(m));
        Ok(vec![name])
    }

    /// A signature as written: the binders of its `(poly (binder …) σ)`, the
    /// syntax type, and whether it makes definitions or a description.
    fn signature(&mut self, sig: &Syntax, interner: &mut Interner) -> R<(Vec<Syntax>, Rc<STy>, bool, bool)> {
        // `(poly (binder …) σ)`: the binders its typed holes may name.
        let (poly, sig) = match sig.as_proper_list() {
            Some([h, bs, body]) if h.as_symbol().is_some_and(|h| interner.name(h) == "poly") => {
                let bs = bs.as_proper_list().ok_or_else(|| FxError::at(bs.span, "a signature's `(poly ((name kind) …) σ)`"))?;
                (bs.to_vec(), body)
            }
            _ => (Vec::new(), sig),
        };
        // `(-> σ defn)`: of what it makes, definitions; `(-> σ type)`, a
        // description; `(-> σ expr)`, as `σ`.
        let (sig, defn, desc) = match sig.as_proper_list() {
            Some([h, body, made]) if h.as_symbol().is_some_and(|h| interner.name(h) == "->") => match made.as_symbol().map(|m| interner.name(m)) {
                Some("defn") => (body, true, false),
                Some("type") => (body, false, true),
                Some("expr") => (body, false, false),
                _ => return Err(FxError::at(made.span, "a signature `(-> σ made)` makes `expr`, `defn` or `type`")),
            },
            _ => (sig, false, false),
        };
        let sig = self.sty(sig, interner, &HashMap::new(), &mut Vec::new())?;
        Ok((poly, sig, defn, desc))
    }

    /// A clause checked against signature `sig` (Herman's rules): its
    /// pattern fits the signature, each of the pattern's variables is
    /// placed in the template where the signature says what is in scope
    /// there, and a reference to a pattern's binder is where no other
    /// pattern binder may shadow it.
    #[allow(clippy::too_many_arguments)]
    fn clause(&self, c: &Syntax, sig: &Rc<STy>, defn: bool, desc: bool, poly: &[Syntax], lits: &[Sym], interner: &mut Interner, file: Option<&FileScope>) -> R<Clause> {
        let usage = "a clause is `((_ . pattern) template)`";
        let [pattern, template] = c.as_proper_list().ok_or_else(|| FxError::at(c.span, usage))? else {
            return Err(FxError::at(c.span, usage));
        };
        let Some((_, pattern)) = split(pattern) else {
            return Err(FxError::at(pattern.span, usage));
        };
        // The pattern, aligned with the signature: each variable's type and
        // declared environment.
        let none = HashMap::new();
        let mut p = Aligner { m: self, interner, mode: Mode::Pattern, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new() };
        let root = p.align(sig, &pattern, None, Vec::new())?;
        // A `syntax-rules`' literals, each a name the signature has written
        // as it is, `(literal name)`, where the pattern has it; and no other.
        {
            for node in &p.nodes {
                let Some(n) = node.syn.as_symbol() else { continue };
                let lit = matches!(&*node.core, STy::Literal(_));
                if lit && !lits.contains(&n) && !reserved(interner.name(n)) {
                    return Err(FxError::at(node.syn.span, format!("`{}` is written as it is in the signature, `(literal {0})`, and is not among the `syntax-rules` literals", interner.name(n))));
                }
                if !lit && matches!(node.kids, Kids::PVar(_)) && lits.contains(&n) {
                    return Err(FxError::at(node.syn.span, format!("`{}` is among the `syntax-rules` literals, and the signature has a part here, not `(literal {0})`", interner.name(n))));
                }
            }
        }
        let mut found = Vec::new();
        p.walk(root, &Env::default(), false, 0, &mut found, &mut Vec::new())?;
        // What a use of a macro that makes definitions says it defines, if
        // its signature says (`(-> (export σ β) defn)`): what a template
        // using it sees, and what its own template is held to.
        let declared = match (defn, &p.nodes[root].export) {
            (true, Some((b, r))) => Some(exports(&p.eval(b, *r, pattern.span)?)),
            _ => None,
        };
        let mut pvars: HashMap<Sym, PInfo> = HashMap::new();
        let mut order = Vec::new();
        for (at, env, many, depth) in found {
            let Kids::PVar(n) = p.nodes[at].kids else { continue };
            order.push(n);
            if depth > 0 && p.nodes[at].hole.is_some() {
                return Err(FxError::at(p.nodes[at].syn.span, "a typed part under an ellipsis: not yet"));
            }
            if pvars.insert(n, PInfo { core: p.nodes[at].core.clone(), declared: env.to_vec(), many, hole: p.nodes[at].hole.clone(), depth }).is_some() {
                return Err(FxError::at(p.nodes[at].syn.span, format!("`{}` is a pattern variable twice", interner.name(n))));
            }
            // Its uses' definitions are checked where each is (the first
            // tier): a template of definitions is not checked once, yet.
            if defn && p.nodes[at].hole.is_some() {
                return Err(FxError::at(p.nodes[at].syn.span, "a macro that makes definitions has no typed parts, not yet: what each use defines is checked where it is"));
            }
            if desc && p.nodes[at].hole.is_some() {
                return Err(FxError::at(p.nodes[at].syn.span, "a macro that makes a description has no typed parts"));
            }
        }
        // The template, an expression or definitions, aligned with the
        // kernel's forms' signatures and the macros'.
        let mut t = Aligner { m: self, interner, mode: Mode::Template, pvars: &pvars, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new() };
        let made = if defn { STy::Defn } else if desc { STy::Type } else { STy::Expr };
        let root = t.align(&Rc::new(made), template, None, Vec::new())?;
        let (mut found, mut seqs) = (Vec::new(), Vec::new());
        t.walk(root, &Env::default(), false, 0, &mut found, &mut seqs)?;
        // How many ellipses each of the template's binders is under: a
        // binder repeated is made fresh in each repetition.
        let binder_depth: HashMap<usize, usize> = found.iter().filter(|f| matches!(t.nodes[f.0].kids, Kids::Binder(..))).map(|f| (f.0, f.3)).collect();
        // The names the template binds in its uses of macros that make
        // definitions: what their signatures do not say they define, it
        // does not see.
        let mut nested = Vec::new();
        for node in &t.nodes {
            if let Kids::Form(x) = node.kids
                && let Some(h) = node.syn.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol())
                && !pvars.contains_key(&h)
                && self.defined.get(&h).is_some_and(|m| m.defn)
            {
                t.binders_under(x, h, &mut nested);
            }
        }
        let mut actions = HashMap::new();
        let mut uses: HashMap<Sym, usize> = HashMap::new();
        for (at, env, many, depth) in found {
            let node = &t.nodes[at];
            let span = node.syn.span;
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
                        return Err(FxError::at(span, format!("`{n}` is bound in a use of `{m}`, whose signature does not say its uses define it: say so (`(-> (export σ β) defn)`), or write `(with #%toplevel {n})` for the top level's")));
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
                        (None, Free::Bound, _) => {
                            return Err(FxError::at(span, format!("`{}`, the module a template's `(with module name)` takes from, is bound by the template or given by a use: a top level's, not yet", interner.name(*n))));
                        }
                        (None, Free::Qualified, None) => Action::Alias,
                        // A file's macro's description is read through the
                        // file's module whole (below).
                        (None, Free::Qualified, Some(_)) => continue,
                        (None, Free::Toplevel, None) => Action::Alias,
                        (None, Free::Toplevel, Some(f)) if f.values.contains(n) || (f.is_standard)(*n) => Action::Alias,
                        (None, Free::Toplevel, Some(_)) => {
                            return Err(FxError::at(
                                span,
                                format!("`{}` is neither a value the file's module shows nor a standard binding: a file's macro names only those, as they are where it is imported", interner.name(*n)),
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
                return Err(FxError::at(t.nodes[r].syn.span, "`...` follows a part with no pattern variable in it under as many ellipses in the pattern, nor a binder repeated as deep, to say how many times"));
            }
        }
        // What the template defines of what its uses give, what its
        // signature says.
        if let Some(declared) = declared {
            let made = exports(&t.levels_of(root, template.span)?);
            if made != declared {
                return Err(FxError::at(template.span, format!("this template defines {}, and its signature says its uses define {}", shown_exports(&made, interner), shown_exports(&declared, interner))));
            }
        }
        // A file's macro's descriptions, each read whole through the file's
        // module or the standard environment: of those the template writes
        // alone, with no binder of its own or part of a use's in them, for
        // now.
        for (i, node) in t.nodes.iter().enumerate() {
            if let (Some(f), true) = (file, node.desc) {
                let open = t.under(i).into_iter().find(|k| match t.nodes[*k].kids {
                    Kids::PVar(_) | Kids::Binder(..) => true,
                    _ => matches!(actions.get(&t.nodes[*k].path), Some(Action::Rename(..))),
                });
                if let Some(k) = open {
                    return Err(FxError::at(t.nodes[k].syn.span, "a file's macro's description with a binder of its own or a part a use gives in it: not yet"));
                }
                let action = match node.syn.as_symbol() {
                    Some(n) if !f.types.contains(&n) => Action::StandardType,
                    _ => Action::ModuleType(f.shared),
                };
                actions.insert(node.path.clone(), action);
            }
            // A use of another of the file's macros: that macro, by the
            // name the importer has it by.
            if let (Some(f), Kids::Form(_)) = (file, &node.kids)
                && let Some(h) = node.syn.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol())
                && let Some(i) = f.internal.get(&h)
            {
                actions.insert(node.path.clone(), Action::MacroHead(*i));
            }
        }
        // Each typed hole's contract, its type read as a use reads the
        // template's types; none where it names the macro's own binders.
        let binders: Vec<Sym> = poly.iter().filter_map(|b| b.as_proper_list()?.first()?.as_symbol()).collect();
        let mut contracts = HashMap::new();
        for (n, info) in &pvars {
            let Some(ty) = info.hole.as_ref().and_then(|h| h.ty.clone()) else { continue };
            if !matches!(&*info.core, STy::Expr) || names_one_of(&ty, &binders) {
                continue;
            }
            let module = match file {
                None => interner.intern("#%toplevel"),
                Some(f) => match ty.as_symbol() {
                    Some(n) if !f.types.contains(&n) => interner.intern("#%fx"),
                    _ => f.shared,
                },
            };
            let select = interner.intern("select");
            contracts.insert(*n, Syntax::list(ty.span, vec![Syntax::symbol(ty.span, select), Syntax::symbol(ty.span, module), ty]));
        }
        let pvars: Vec<(Sym, PInfo)> = order.into_iter().map(|n| (n, pvars[&n].clone())).collect();
        let names = pvars.iter().filter(|(_, p)| matches!(&*p.core, STy::Bvar | STy::Dvar | STy::Id)).map(|(n, _)| *n).collect();
        let def_env = self.def_env_of(file);
        // A typed hole's contract is its type as the top level or the
        // file's module reads it, by a qualifier: none names a file's own
        // items, which a binder at the use could capture.
        if matches!(def_env, hygiene::DefEnv::Within) && let Some(n) = contracts.keys().next() {
            return Err(FxError::at(c.span, format!("`{}`: a typed hole in a macro a file uses itself, not yet", interner.name(*n))));
        }
        Ok(Clause { pattern, names, template: template.clone(), actions, pvars, contracts, def_env })
    }

    /// `form` with each use of a macro in it expanded, as each expands,
    /// until none is left; quoted data left as it is.
    pub fn expand(&mut self, form: &Syntax, interner: &mut Interner) -> R<Syntax> {
        if self.defined.is_empty() {
            return Ok(form.clone());
        }
        let mut budget = 10_000;
        let mut out = self.expand_in(form, interner, &mut budget, &mut Vec::new())?;
        // A form of the program's is the text written for it, what a use
        // made of it or not: the REPL takes the entry's text by it.
        out.span = form.span;
        Ok(out)
    }

    /// Top-level form `form` expanded: a use of a macro that makes
    /// definitions, the definitions it makes, in order, a `begin` of them
    /// spliced (as R7RS's at the top level); each at `form`'s place, as
    /// `expand`'s, as a top-level `include`'s forms are. Else `expand`'s.
    pub fn expand_top(&mut self, form: &Syntax, interner: &mut Interner) -> R<Vec<Syntax>> {
        // A procedural macro may make definitions too, which no signature
        // says ahead.
        let makes = form.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol()).is_some_and(|h| self.defined.get(&h).is_some_and(|m| m.defn || m.procedural.is_some()));
        if !makes {
            return Ok(vec![self.expand(form, interner)?]);
        }
        let mut out = Vec::new();
        self.expand_defn(form, interner, &mut 10_000, &mut out)?;
        for f in &mut out {
            f.span = form.span;
        }
        Ok(out)
    }

    /// `s`, where a definition is: a use of a macro that makes definitions,
    /// what it makes; a `begin`, each of its; a definition, as `expand_in`
    /// expands it. Each definition pushed on `out`.
    fn expand_defn(&mut self, s: &Syntax, interner: &mut Interner, budget: &mut usize, out: &mut Vec<Syntax>) -> R<()> {
        let items = s.as_proper_list().unwrap_or(&[]);
        let head = items.first().and_then(|h| h.as_symbol());
        if let Some(h) = head
            && let Some(m) = self.defined.get(&h).cloned()
        {
            if *budget == 0 {
                return Err(FxError::at(s.span, "this macro's expansion does not end"));
            }
            *budget -= 1;
            let made = self.expand_use(h, &m, s, interner)?;
            return self.expand_defn(&made, interner, budget, out);
        }
        if head.is_some_and(|h| interner.name(h) == "begin") {
            for d in &items[1..] {
                self.expand_defn(d, interner, budget, out)?;
            }
            return Ok(());
        }
        out.push(self.expand_in(s, interner, budget, &mut Vec::new())?);
        Ok(())
    }

    /// `withs`: the places of the `with` forms whose bodies `s` is in.
    fn expand_in(&mut self, s: &Syntax, interner: &mut Interner, budget: &mut usize, withs: &mut Vec<Span>) -> R<Syntax> {
        let Datum::List { items, tail } = &s.datum else { return Ok(s.clone()) };
        let head = items[0].as_symbol();
        if head.is_some_and(|h| interner.name(h) == "quote") {
            return Ok(s.clone());
        }
        if let Some(h) = head
            && let Some(m) = self.defined.get(&h).cloned()
        {
            if m.defn {
                return Err(FxError::at(s.span, format!("`{}` makes definitions, which are made at the top level, not where an expression is", interner.name(h))));
            }
            if *budget == 0 {
                return Err(FxError::at(s.span, "this macro's expansion does not end"));
            }
            *budget -= 1;
            // A name the program wrote (a template's is the macro, by
            // hygiene), in a `with`'s body.
            if items[0].span.expansion == 0 {
                for w in withs.iter() {
                    self.withs.with_uses.entry(*w).or_default().push((h, items[0].span));
                }
            }
            let out = self.expand_use(h, &m, s, interner)?;
            return self.expand_in(&out, interner, budget, withs);
        }
        // A template's `(with m name)`: `m`'s `name`, or refused.
        if let (Some(h), None, [_, m, n]) = (head, tail, &items[..])
            && interner.name(h) == "with"
            && items[0].span.expansion != 0
            && let (Some(m), Some(x)) = (m.as_symbol(), n.as_symbol())
            && !matches!(interner.name(m), "#%fx" | "#%toplevel")
        {
            self.withs.projections.insert(s.span, (x, n.span));
        }
        // A definition of a macro's name: refused, as a form's is.
        if let (Some(h), Some(n)) = (head, items.get(1).and_then(|n| n.as_symbol()))
            && matches!(interner.name(h), "define" | "define*")
            && self.defined.contains_key(&n)
        {
            return Err(FxError::at(items[1].span, format!("`{}` is a macro's name, which is not defined again", interner.name(n))));
        }
        // `(with m body …)`: its body in it.
        let with = head.is_some_and(|h| interner.name(h) == "with");
        let mut out = Vec::new();
        for (k, i) in items.iter().enumerate() {
            let inside = with && k >= 2;
            if inside {
                withs.push(s.span);
            }
            let r = self.expand_in(i, interner, budget, withs);
            if inside {
                withs.pop();
            }
            out.push(r?);
        }
        let items = out;
        let tail = match tail {
            Some(t) => Some(Box::new(self.expand_in(t, interner, budget, withs)?)),
            None => None,
        };
        Ok(Syntax::new(s.span, Datum::List { items, tail }))
    }

    /// Form `form`, a program's after expansion, each local value binder
    /// renamed, and each reference to it, as a program's walk finds their
    /// scopes (`binding-shapes.md`, step 1): the same program, if the
    /// kernel's binding structure is the checkers'. A definition's name is
    /// kept, and so is every binder of a name a reference reaches only past
    /// what a `with` or `include` binds, which the walk does not know yet.
    pub fn alpha_renamed(&mut self, form: &Syntax, interner: &mut Interner) -> R<Syntax> {
        self.ensure_kernel(interner)?;
        let none = HashMap::new();
        let mut renamed: HashMap<Vec<bool>, String> = HashMap::new();
        {
            let mut a = Aligner { m: self, interner, mode: Mode::Program, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new() };
            let root = a.align(&Rc::new(STy::Item), form, None, Vec::new())?;
            let mut found = Vec::new();
            a.walk(root, &Env::default(), false, 0, &mut found, &mut Vec::new())?;
            // The names definitions give, which other forms see.
            let mut defined = HashSet::new();
            for node in &a.nodes {
                if let (STy::Item | STy::Defn, Kids::Form(x)) = (&*node.core, &node.kids)
                    && let Some((b, r)) = &a.nodes[*x].export
                {
                    for level in a.eval(b, *r, node.syn.span)? {
                        if let Level::Rib(atoms) = level {
                            defined.extend(atoms.iter().filter_map(|x| if let Atom::Lit(t, _) = x { Some(*t) } else { None }));
                        }
                    }
                }
            }
            // Each reference's binder, innermost first; a name looked for
            // past a module's names, kept.
            let mut target: HashMap<usize, usize> = HashMap::new();
            let mut kept: HashSet<Sym> = HashSet::new();
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
            binders.sort_by(|x, y| a.nodes[*x].path.iter().map(|s| !s).cmp(a.nodes[*y].path.iter().map(|s| !s)));
            binders.dedup_by(|x, y| a.nodes[*x].path == a.nodes[*y].path);
            for (k, t) in binders.into_iter().enumerate() {
                let Kids::Binder(n, _) = a.nodes[t].kids else { unreachable!("a binder") };
                renamed.insert(a.nodes[t].path.clone(), format!("{}%{}", a.name(n), k + 1));
            }
            for (at, b) in &target {
                if let Some(name) = renamed.get(&a.nodes[*b].path).cloned() {
                    renamed.insert(a.nodes[*at].path.clone(), name);
                }
            }
        }
        Ok(rename_paths(form, &mut Vec::new(), &renamed, interner))
    }

    /// A use of macro `name`, parsed by its signature, then the first clause
    /// whose pattern matches it transcribed.
    fn expand_use(&mut self, name: Sym, m: &Macro, s: &Syntax, interner: &mut Interner) -> R<Syntax> {
        if let Some(p) = &m.procedural {
            return self.expand_procedural(name, p, s, interner);
        }
        let (_, operands) = split(s).expect("a list");
        let none = HashMap::new();
        let mut u = Aligner { m: self, interner, mode: Mode::Use, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new() };
        u.align(&m.sig, &operands, None, Vec::new()).map_err(|e| FxError::at(e.span, format!("a use of `{}`: {}", interner.name(name), e.message)))?;
        for c in &m.clauses {
            let mut binds = HashMap::new();
            if !matches(&c.pattern, &operands, &c.names, &mut binds, interner) {
                continue;
            }
            let made = fixpt_read::record_expansion(interner.name(name), s.span, m.text.clone());
            self.withs.def_envs.insert(made, c.def_env.clone());
            return self
                .transcribe(c, &c.template, &mut Vec::new(), &binds, &mut Made::default(), &mut Vec::new(), made, interner)
                .map_err(|e| FxError::at(s.span, format!("a use of `{}`: {}", interner.name(name), e.message)));
        }
        Err(FxError::at(s.span, format!("a use of `{}` that no clause of it matches", interner.name(name))))
    }

    /// A use of procedural macro `name`, `s`: its transformer run on it
    /// (`procedural::run`), what it gave read back at the use's place, a
    /// syntactic closure's opened (`procedural::closed`).
    fn expand_procedural(&mut self, name: Sym, p: &procedural::Procedural, s: &Syntax, interner: &mut Interner) -> R<Syntax> {
        let made = fixpt_read::record_expansion(interner.name(name), s.span, None);
        self.withs.def_envs.insert(made, p.def_env.clone());
        let form = fixpt_read::write_syntax(s, interner);
        let said = |e: String| FxError::at(s.span, format!("a use of `{}`: its transformer: {e}", interner.name(name)));
        let out = procedural::run(&procedural::applied(p.style, &p.code, &form, made)).map_err(said)?;
        let read = fixpt_read::Reader::new(&out, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX26, interner).read_all();
        let read = read.map_err(|e| FxError::at(s.span, format!("a use of `{}`: what its transformer gave, `{out}`, is not read: {}", interner.name(name), e.message)))?;
        let [one] = &read[..] else {
            return Err(FxError::at(s.span, format!("a use of `{}`: its transformer gave `{out}`, not one form", interner.name(name))));
        };
        let at = procedural::placed(one, s.span, made);
        let opened = match p.style {
            procedural::Style::Er => at,
            procedural::Style::Sc => procedural::closed(&at, true, made, interner)?,
            procedural::Style::Rsc => procedural::closed(&at, false, made, interner)?,
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
    fn transcribe(&mut self, c: &Clause, t: &Syntax, path: &mut Vec<bool>, binds: &HashMap<Sym, Syntax>, fresh: &mut Made, iters: &mut Vec<usize>, made: u32, interner: &mut Interner) -> R<Syntax> {
        let at = t.span.in_expansion(made);
        let typed = match c.actions.get(&*path) {
            Some(Action::StandardType) => Some(interner.intern("#%fx")),
            Some(Action::ModuleType(m)) => Some(*m),
            _ => None,
        };
        if let Some(m) = typed {
            return Ok(selected(m, t, made, interner));
        }
        match &t.datum {
            Datum::Symbol(n) => {
                if let Some(b) = binds.get(n) {
                    // A typed hole's expression, held to its type; in a
                    // template's check, its call, where the template has it.
                    if self.checking {
                        return Ok(respanned(b, at));
                    }
                    return Ok(match c.contracts.get(n) {
                        Some(ty) => Syntax::list(b.span, vec![Syntax::symbol(b.span, interner.intern("the")), in_expansion(ty, made), b.clone()]),
                        None => b.clone(),
                    });
                }
                Ok(match c.actions.get(&*path) {
                    Some(Action::Rename(binder, depth)) => {
                        let key = (binder.clone(), iters[..(*depth).min(iters.len())].to_vec());
                        let name = match fresh.fresh.get(&key) {
                            Some(f) => *f,
                            None => {
                                self.fresh += 1;
                                let f = interner.intern(&format!("%{}:{}", interner.name(*n), self.fresh));
                                fresh.fresh.insert(key, f);
                                f
                            }
                        };
                        Syntax::symbol(at, name)
                    }
                    Some(Action::Alias) => {
                        let a = interner.intern(&procedural::alias(interner.name(*n), made));
                        Syntax::symbol(at, a)
                    }
                    _ => Syntax::new(at, t.datum.clone()),
                })
            }
            Datum::List { items, tail } => {
                let head = match c.actions.get(&*path) {
                    Some(Action::MacroHead(h)) => Some(*h),
                    _ => None,
                };
                let depth = path.len();
                let mut out = Vec::new();
                let mut i = 0;
                while i < items.len() {
                    path.push(true);
                    // `p ...`: `p` once for each element of what the use gave
                    // of the pattern variables in it under more ellipses than
                    // this, together.
                    if items.get(i + 1).is_some_and(|x| is_ellipsis(x, interner)) {
                        let drivers: Vec<Sym> = c.pvars.iter().filter(|(n, p)| p.depth > iters.len() && find_symbol(&items[i], *n).is_some()).map(|(n, _)| *n).collect();
                        let lists: Vec<Vec<Syntax>> = drivers.iter().map(|n| elements(&binds[n])).collect();
                        if let Some((k, _)) = lists.iter().enumerate().find(|(_, l)| l.len() != lists[0].len()) {
                            let (a, b) = (interner.name(drivers[0]), interner.name(drivers[k]));
                            return Err(FxError::at(items[i].span, format!("`{a}` and `{b}`, repeated together, are given {} and {} times", lists[0].len(), lists[k].len())));
                        }
                        // The binders of the template's repeated in it,
                        // and those it refers to that were repeated before.
                        let under: Vec<(&Vec<bool>, &Vec<bool>)> = c
                            .actions
                            .iter()
                            .filter_map(|(at, a)| match a {
                                Action::Rename(b, d) if *d > iters.len() && at.starts_with(path) => Some((at, b)),
                                _ => None,
                            })
                            .collect();
                        // Every count it is repeated by agrees: the pattern
                        // variables', and the repeated binders' it refers to.
                        let mut known: Vec<usize> = under.iter().filter_map(|(_, b)| fresh.counts.get(&((*b).clone(), iters.clone())).copied()).collect();
                        known.extend(lists.first().map(|l| l.len()));
                        let Some(&times) = known.first() else {
                            return Err(FxError::at(items[i].span, "this part is repeated before the repetition that binds what it refers to"));
                        };
                        if known.iter().any(|k| *k != times) {
                            return Err(FxError::at(items[i].span, "this part repeats binders and parts that were repeated, or given, different numbers of times"));
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
                            let x = self.transcribe(c, &items[i], path, &each, fresh, iters, made, interner);
                            iters.pop();
                            out.push(x?);
                        }
                        path.pop();
                        path.push(false);
                        path.push(false);
                        i += 2;
                        continue;
                    }
                    out.push(self.transcribe(c, &items[i], path, binds, fresh, iters, made, interner)?);
                    path.pop();
                    path.push(false);
                    i += 1;
                }
                if let Some(h) = head {
                    out[0] = Syntax::symbol(out[0].span, h);
                }
                let tail = match tail {
                    Some(x) => Some(self.transcribe(c, x, path, binds, fresh, iters, made, interner)?),
                    None => None,
                };
                path.truncate(depth);
                Ok(list_of(at, out, tail))
            }
            _ => Ok(Syntax::new(at, t.datum.clone())),
        }
    }
}

impl Aligner<'_> {
    fn name(&self, n: Sym) -> &str {
        self.interner.name(n)
    }

    /// `s`, at `path`, aligned with type `t`; `root`, the node its
    /// addresses are from, if not itself.
    fn align(&mut self, t: &Rc<STy>, s: &Syntax, root: Option<usize>, path: Vec<bool>) -> R<usize> {
        let at = self.node_new(t, s, path);
        self.fill(at, t, s, root.unwrap_or(at))?;
        Ok(at)
    }

    /// A node for `s`, at `path`, of type `t`, to be filled.
    fn node_new(&mut self, t: &Rc<STy>, s: &Syntax, path: Vec<bool>) -> usize {
        let at = self.nodes.len();
        // A program's node keeps its syntax three lists deep, all that is
        // read of it (`shapes.rs`: a `moduleof`'s members' names), not a
        // copy of all it holds at every node it holds.
        let syn = if self.mode == Mode::Program { shallow(s, 3) } else { s.clone() };
        self.nodes.push(Node { syn, path, core: t.clone(), imports: Vec::new(), export: None, many: false, hole: None, desc: false, repeated: false, kids: Kids::Other });
        at
    }

    fn fill(&mut self, at: usize, t: &Rc<STy>, s: &Syntax, root: usize) -> R<()> {
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
    fn fill_step(&mut self, at: usize, t: Rc<STy>, s_owned: Syntax, root: usize) -> R<Option<Step>> {
        let s = &s_owned;
        let t = &t;
        let span = s.span;
        let fail = |why: String| FxError::at(span, why);
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
        // A pattern's variable, or one placed in a template: at any type.
        if let Some(n) = s.as_symbol() {
            let lit = matches!(&**self.m.unfold(t), STy::Literal(_));
            let pvar = match self.mode {
                Mode::Pattern => !lit && self.name(n) != "_" && self.name(n) != "...",
                Mode::Template => self.pvars.contains_key(&n),
                Mode::Use | Mode::Program => false,
            };
            if pvar {
                // A pattern's variable where a name or a list may be: the
                // name's shape, if one member is a name's.
                if self.mode == Mode::Pattern
                    && let STy::Union(ms) = &**self.m.unfold(t)
                {
                    let names: Vec<&Rc<STy>> = ms.iter().filter(|m| matches!(&**self.m.unfold(m), STy::Bvar | STy::Dvar | STy::Id | STy::Label)).collect();
                    if let [one] = &names[..] {
                        let one = (*one).clone();
                        return Ok(Some((at, one, s_owned, root)));
                    }
                }
                self.nodes[at].kids = Kids::PVar(n);
                return Ok(None);
            }
        }
        // `(p ...)`, a pattern's or a template's: `p` aligned with the list's
        // element type, repeated; the list exports what each element does.
        if matches!(self.mode, Mode::Pattern | Mode::Template) && let Some(x) = ellipsis(s, self.interner) {
            let Some((elem, cage)) = self.m.seq_of(t) else {
                return Err(fail(format!("`{}` repeats a part by `...` where the form takes no list of them", self.show(s))));
            };
            let mut p = self.nodes[at].path.clone();
            p.push(true);
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
        if matches!(self.mode, Mode::Pattern | Mode::Template) && s.as_symbol().is_some_and(|n| self.name(n) == "...") {
            return Err(fail("`...` follows the part it repeats, last in a list".into()));
        }
        match &**t {
            STy::Mu(id) => {
                let body = self.m.mus[*id].clone();
                Ok(Some((at, body, s_owned, at)))
            }
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
                if !matches!(s.datum, Datum::List { .. }) {
                    return Err(fail(format!("`{}` is not a list as this part must be", self.show(s))));
                }
                // Taken apart, not copied: a long list's rest is not made
                // again at each of its parts.
                let (x, y) = split_owned(s_owned).expect("a list");
                let path = self.nodes[at].path.clone();
                let mut ap = path.clone();
                ap.push(true);
                let mut dp = path;
                dp.push(false);
                let x_at = self.node_new(a, &x, ap);
                // The rest, its node made here and filled after the first
                // part; a program's keeps only its place (what a rest is,
                // its parts say).
                let rest = self.nodes.len();
                let syn = if self.mode == Mode::Program { Syntax::new(y.span, Datum::Nil) } else { y.clone() };
                self.nodes.push(Node { syn, path: dp, core: d.clone(), imports: Vec::new(), export: None, many: false, hole: None, desc: false, repeated: false, kids: Kids::Other });
                self.nodes[at].kids = Kids::Pair(x_at, rest);
                self.work.push((rest, d.clone(), y, root));
                Ok(Some((x_at, a.clone(), x, root)))
            }
            STy::Nil => match &s.datum {
                Datum::Nil => {
                    self.nodes[at].kids = Kids::Nil;
                    Ok(None)
                }
                _ => Err(fail(format!("`{}` is more than this part may have", self.show(s)))),
            },
            STy::Literal(n) => match s.as_symbol() {
                Some(m) if m == *n => Ok(None),
                _ => Err(fail(format!("`{}` where `{}` is written", self.show(s), self.name(*n)))),
            },
            // A program's binder: any name the checkers let it bind, which
            // they decide.
            STy::Bvar | STy::Dvar if self.mode == Mode::Program && s.as_symbol().is_some() => {
                let n = s.as_symbol().expect("a name");
                let ns = if matches!(&**t, STy::Dvar) { Ns::Desc } else { Ns::Value };
                self.nodes[at].kids = Kids::Binder(n, ns);
                Ok(None)
            }
            STy::Bvar | STy::Dvar => match s.as_symbol() {
                Some(n) if self.m.defined.contains_key(&n) => Err(fail(format!("`{}` is a macro's name, which is not bound", self.name(n)))),
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
            STy::Id => match s.as_symbol() {
                Some(n) => {
                    if self.writes() {
                        self.nodes[at].kids = Kids::Ref(n, Ns::Value, Free::Toplevel);
                    }
                    Ok(None)
                }
                None => Err(fail(format!("`{}` is not a variable", self.show(s)))),
            },
            STy::Label => match &s.datum {
                Datum::Keyword(_) => Ok(None),
                Datum::Symbol(_) if matches!(self.mode, Mode::Use | Mode::Program) => Ok(None),
                // A product's field by its position, a program's.
                Datum::Number(_) if self.mode == Mode::Program => Ok(None),
                Datum::Symbol(n) => Err(fail(format!("a tag or label in a template is a keyword: `#:{}`, not `{0}`", self.name(*n)))),
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
            STy::Lambda => match (&s.datum, self.mode) {
                (Datum::List { .. }, Mode::Template) if s.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol()).is_some_and(|h| self.name(h) == "lambda") => self.form_owned(at, s_owned, false),
                _ if self.mode != Mode::Template && lambda_shaped(s, self.interner) => Ok(None),
                _ => Err(fail(format!("`{}` is not a lambda, as this part must be", self.show(s)))),
            },
            STy::Expr => match (&s.datum, self.mode) {
                (Datum::Symbol(n), Mode::Program) if !matches!(self.name(*n), "#t" | "#f" | "#u") => {
                    self.nodes[at].kids = Kids::Ref(*n, Ns::Value, Free::Toplevel);
                    Ok(None)
                }
                (Datum::Symbol(n), _) if reserved(self.name(*n)) => Err(fail(format!("`{}` is a form's name, not an expression", self.name(*n)))),
                // `#u`, unit: a literal, which the parsers read as a name.
                (Datum::Symbol(n), _) if self.name(*n) == "#u" => Ok(None),
                (Datum::Symbol(n), Mode::Template | Mode::Program) => {
                    self.nodes[at].kids = Kids::Ref(*n, Ns::Value, Free::Toplevel);
                    Ok(None)
                }
                (Datum::List { .. }, Mode::Template | Mode::Program) => self.form_owned(at, s_owned, false),
                (Datum::Nil, _) => Err(fail("`()` is not an expression".into())),
                _ => Ok(None),
            },
            STy::Defn => match (&s.datum, self.mode) {
                (Datum::List { .. }, Mode::Template | Mode::Program) => self.form_owned(at, s_owned, true),
                _ => Err(fail(format!("`{}` is not a definition", self.show(s)))),
            },
            // A module's item: a definition by its head, a string, or an
            // expression.
            STy::Item => {
                if self.defines(s) {
                    return self.form_owned(at, s_owned, true);
                }
                if matches!(s.datum, Datum::Str(_)) {
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
    fn unquoted(&mut self, s: &Syntax, path: Vec<bool>, depth: u32, kids: &mut Vec<usize>) -> R<()> {
        match &s.datum {
            Datum::List { items, tail } => {
                let head = items[0].as_symbol().map(|h| self.name(h).to_string());
                if items.len() == 2 && tail.is_none() {
                    let mut inner = path.clone();
                    inner.extend([false, true]);
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
                    let mut ip = p.clone();
                    ip.push(true);
                    self.unquoted(i, ip, depth, kids)?;
                    p.push(false);
                }
                match tail {
                    Some(t) => self.unquoted(t, p, depth, kids),
                    None => Ok(()),
                }
            }
            Datum::Vector(items) if items.iter().any(|i| self.unquotes(i)) => {
                items.iter().for_each(|i| self.symbols_into(i));
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Whether `s` is a definition, by its head: a `begin` one if all it
    /// holds are.
    fn defines(&self, s: &Syntax) -> bool {
        let Some([h, rest @ ..]) = s.as_proper_list() else { return false };
        match h.as_symbol().map(|h| self.name(h)) {
            Some("begin") => !rest.is_empty() && rest.iter().all(|r| self.defines(r)),
            Some(h) => self.m.k.definitions.contains_key(h) || self.m.k.scope_definitions.contains_key(h),
            None => false,
        }
    }

    /// Each name in `s`, unplaced.
    fn symbols_into(&mut self, s: &Syntax) {
        match &s.datum {
            Datum::Symbol(n) => self.unplaced.push(*n),
            Datum::List { items, tail } => items.iter().chain(tail.as_deref()).for_each(|i| self.symbols_into(i)),
            Datum::Vector(items) => items.iter().for_each(|i| self.symbols_into(i)),
            _ => {}
        }
    }

    /// Whether `s` has an `unquote` or `unquote-splicing` in it.
    fn unquotes(&self, s: &Syntax) -> bool {
        match &s.datum {
            Datum::Symbol(n) => matches!(self.name(*n), "unquote" | "unquote-splicing"),
            Datum::List { items, tail } => items.iter().chain(tail.as_deref()).any(|i| self.unquotes(i)),
            Datum::Vector(items) => items.iter().any(|i| self.unquotes(i)),
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
    fn form(&mut self, at: usize, s: &Syntax, defn: bool) -> R<Option<(Rc<STy>, Vec<bool>, bool)>> {
        let Datum::List { items, tail } = &s.datum else { unreachable!("a list") };
        let head = items[0].as_symbol().filter(|h| !self.pvars.contains_key(h));
        let not_one = |what: &str| FxError::at(s.span, format!("`{}` is not a definition: a macro that makes definitions makes {what}", self.show(s)));
        let sig = match head.map(|h| (h, self.name(h))) {
            Some((h, _)) if self.m.defined.get(&h).is_some_and(|m| m.procedural.is_some()) => {
                return Err(FxError::at(s.span, format!("`{}` is a procedural macro, whose binding structure no signature says: not in a template", self.name(h))));
            }
            // A program's `(module-parameters ((name T) … (name kind) …))`:
            // a module's values or descriptions by what each is given, which
            // only the kind's word tells (`parse::binder_is_kind`).
            Some((_, "module-parameters")) if defn && self.mode == Mode::Program && items.len() == 2 => Some(self.parameters_sig(&items[1])),
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
                return Err(FxError::at(s.span, format!("`{}` makes definitions, which are made at the top level, not where an expression is", self.name(h))));
            }
            Some((h, _)) if self.m.defined.get(&h).is_some_and(|m| m.desc) => {
                return Err(FxError::at(s.span, format!("`{}` makes a description, not an expression", self.name(h))));
            }
            Some((_, n)) if self.m.k.definitions.contains_key(n) && !self.m.k.forms.contains_key(n) => {
                return Err(FxError::at(s.span, format!("`{n}` makes a definition, made at the top level by a macro that makes definitions, not where an expression is")));
            }
            Some((_, "quasiquote")) if self.mode == Mode::Program => {
                let [_, x] = &items[..] else { return Err(FxError::at(s.span, "`(quasiquote datum)`")) };
                let mut p = self.nodes[at].path.clone();
                p.extend([false, true]);
                let mut kids = Vec::new();
                self.unquoted(x, p, 1, &mut kids)?;
                self.nodes[at].kids = Kids::Desc(kids);
                return Ok(None);
            }
            Some((_, "with")) if self.mode == Mode::Program && {
                let named = |m: &str| m == "#%fx" || m == "#%toplevel";
                tail.is_none() && matches!(&items[..], [_, m, n] if m.as_symbol().is_some_and(|m| named(self.name(m))) && n.as_symbol().is_some())
            } => return Ok(None),
            Some((_, "with")) if self.mode == Mode::Template => {
                let named = |m: &str| m == "#%fx" || m == "#%toplevel";
                let standard = tail.is_none() && matches!(&items[..], [_, m, n] if m.as_symbol().is_some_and(|m| named(self.name(m))) && n.as_symbol().is_some());
                if standard {
                    return Ok(None);
                }
                // `(with m name)`: the value `name` of module `m`, a
                // template's binder or a use's, the name as written; `m`'s
                // or refused, where it is checked (`Macros::projections`).
                if let (None, [_, m, n]) = (tail, &items[..])
                    && m.as_symbol().is_some()
                    && n.as_symbol().is_some()
                {
                    let sig = Rc::new(STy::Pair(Rc::new(STy::Id), Rc::new(STy::Pair(Rc::new(STy::Data), Rc::new(STy::Nil)))));
                    let (_, operands) = split(s).expect("a list");
                    let mut p = self.nodes[at].path.clone();
                    p.push(false);
                    let x = self.align(&sig, &operands, None, p)?;
                    if let Kids::Pair(m, _) = self.nodes[x].kids
                        && let Kids::Ref(n, ns, _) = self.nodes[m].kids
                    {
                        self.nodes[m].kids = Kids::Ref(n, ns, Free::Bound);
                    }
                    self.nodes[at].kids = Kids::Form(x);
                    return Ok(None);
                }
                return Err(FxError::at(s.span, "a template's `with` is `(with module name)`, the value `name` of the module, or `(with #%fx name)` or `(with #%toplevel name)` (one opening a module over a body waits for scopes of a module's names)"));
            }
            Some((h, _)) if self.m.defined.contains_key(&h) => Some(self.m.defined[&h].sig.clone()),
            // A form the kernel has not, but `scope-forms`: in a program's
            // walk; in a template too, if it binds nothing (`bloblet-ref`,
            // `TODO.md` §247).
            Some((_, n))
                if self.m.k.scope_forms.get(n).is_some_and(|t| self.mode == Mode::Program || self.m.binds_nothing(t, &mut Vec::new())) =>
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
                return Err(FxError::at(s.span, format!("the prototype does not know `{n}`'s binding structure: not yet in a template")));
            }
            _ => None,
        };
        let path = self.nodes[at].path.clone();
        // A keyword at a list's head constructs, a tag written or placed.
        let construct = matches!(items[0].datum, Datum::Keyword(_)) || items[0].as_symbol().and_then(|h| self.pvars.get(&h)).is_some_and(|p| matches!(&*p.core, STy::Label));
        // Aligned next, by `run`, not here: a form nested in a form takes
        // no stack.
        Ok(Some(match sig {
            _ if construct && !defn => (self.m.k.forms["%construct"].clone(), path, false),
            Some(sig) => {
                let mut p = path;
                p.push(false);
                (sig, p, true)
            }
            None => (self.m.k.forms["%app"].clone(), path, false),
        }))
    }

    /// `form` of `s`, which is taken: what it aligns next, its operands
    /// moved out of it, not copied, at every form a program nests.
    fn form_owned(&mut self, at: usize, s: Syntax, defn: bool) -> R<Option<Step>> {
        let Some((t, path, operands)) = self.form(at, &s, defn)? else { return Ok(None) };
        let s = if operands { split_owned(s).expect("a list").1 } else { s };
        let x = self.node_new(&t, &s, path);
        self.nodes[at].kids = Kids::Form(x);
        Ok(Some((x, t, s, x)))
    }

    /// The binding structure of a program's `module-parameters`' list
    /// `bs`: each a value's binder, its type in the scope of those before
    /// it, or a description's.
    fn parameters_sig(&self, bs: &Syntax) -> Rc<STy> {
        let entry = |d| Bind::Rib(vec![(vec![true], d)]);
        let ps = bs.as_proper_list().unwrap_or(&[]);
        let mut list = Rc::new(STy::Nil);
        for p in ps.iter().rev() {
            let one = if crate::parse::binder_is_kind(p, self.interner) {
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
        let included = ps.iter().enumerate().filter(|(_, p)| !crate::parse::binder_is_kind(p, self.interner) && p.as_proper_list().is_some_and(|l| l.len() == 2));
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
    fn desc(&mut self, at: usize, s: &Syntax) -> R<()> {
        let fail = |why: String| FxError::at(s.span, why);
        let items = match &s.datum {
            Datum::Symbol(n) => {
                self.nodes[at].kids = if self.pvars.contains_key(n) {
                    Kids::PVar(*n)
                } else if self.word(*n, false) {
                    Kids::Other
                } else {
                    Kids::Ref(*n, Ns::Desc, Free::Qualified)
                };
                return Ok(());
            }
            Datum::List { items, tail: None } => items.clone(),
            Datum::List { .. } => return Err(fail("a description is a list, not a dotted one".into())),
            _ => return Ok(()),
        };
        // A macro's use: its operands aligned with its signature, if it
        // makes a description.
        if let Some(h) = items[0].as_symbol().filter(|h| !self.pvars.contains_key(h))
            && let Some(m) = self.m.defined.get(&h)
        {
            if !m.desc {
                let what = if m.defn { "definitions" } else { "an expression" };
                return Err(fail(format!("`{}` makes {what}, not a description", self.name(h))));
            }
            let (sig, (_, operands)) = (m.sig.clone(), split(s).expect("a list"));
            let mut p = self.nodes[at].path.clone();
            p.push(false);
            let x = self.align(&sig, &operands, None, p)?;
            self.nodes[at].kids = Kids::Form(x);
            return Ok(());
        }
        let head = items[0].as_symbol().filter(|h| !self.pvars.contains_key(h)).map(|h| self.name(h).to_string());
        let kids = self.desc_kids(at, &items);
        let not_yet = |what: &str| Err(fail(format!("{what} in a template's description: not yet")));
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
                let entries = bs.as_proper_list().map(|l| l.to_vec()).unwrap_or_default();
                let ek = self.desc_kids(kids[1], &entries);
                let (mut atoms, mut parts) = (Vec::new(), Vec::new());
                for (k, e) in ek.iter().zip(&entries) {
                    let Some([n, d]) = e.as_proper_list() else {
                        return Err(FxError::at(e.span, "`(name description)`"));
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
                    let Some([label, ty]) = f.as_proper_list() else {
                        // A program's flat sum's tag type, `(sumof u8 …)`.
                        if self.mode == Mode::Program {
                            self.desc(*k, f)?;
                            continue;
                        }
                        return Err(FxError::at(f.span, "`(label type)`"));
                    };
                    let p = self.desc_kids(*k, &[label.clone(), ty.clone()]);
                    // A label a use gives, placed.
                    if let Some(n) = label.as_symbol().filter(|n| self.pvars.contains_key(n)) {
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
                    let Some(n) = syn.as_symbol() else {
                        return Err(FxError::at(syn.span, "a name"));
                    };
                    self.nodes[k].core = Rc::new(STy::Id);
                    self.nodes[k].kids = if self.pvars.contains_key(&n) { Kids::PVar(n) } else { Kids::Ref(n, Ns::Value, free) };
                }
                Ok(())
            }
            // A program's: each member's type in the scope of the abstract
            // and transparent types before it, a value's name a label.
            Some("moduleof") if self.mode == Mode::Program => {
                let mut atoms = Vec::new();
                for (k, m) in kids[1..].iter().zip(&items[1..]) {
                    let parts = m.as_proper_list().map(|l| l.to_vec()).unwrap_or_default();
                    let word = parts.first().and_then(|h| h.as_symbol()).map(|h| self.name(h).to_string());
                    if parts.len() < 2 {
                        self.desc(*k, m)?;
                        continue;
                    }
                    let p = self.desc_kids(*k, &parts);
                    for (q, x) in p[2..].iter().zip(&parts[2..]) {
                        self.desc_scoped(*q, x, atoms.clone())?;
                    }
                    if matches!(word.as_deref(), Some("abs" | "desc")) && parts[1].as_symbol().is_some() {
                        atoms.push(self.desc_binder(p[1], &parts[1])?);
                    }
                }
                Ok(())
            }
            Some("moduleof") => not_yet("a `moduleof`"),
            Some("subr" | "->" | "->*") => self.desc_subr(s, &items, &kids),
            Some(_) if self.word(items[0].as_symbol().expect("a name"), true) => {
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
    fn desc_subr(&mut self, s: &Syntax, items: &[Syntax], kids: &[usize]) -> R<()> {
        let clause = |c: &Self, x: &Syntax| x.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol()).is_some_and(|h| matches!(c.name(h), "requires" | "ensures"));
        let plain = items.len() - items.iter().rev().take_while(|c| clause(self, c)).count();
        if plain < 3 || kids.len() != items.len() {
            return Err(FxError::at(s.span, "`(subr effect (param …) result)` or `(-> (param …) result)`, then a specification's clauses"));
        }
        let (pi, ri) = (plain - 2, plain - 1);
        for i in 1..pi {
            self.desc(kids[i], &items[i])?;
        }
        let mut atoms = Vec::new();
        if !matches!(items[pi].datum, Datum::Nil) {
            let Some(ps) = items[pi].as_proper_list().map(|l| l.to_vec()) else {
                return Err(FxError::at(items[pi].span, "a procedure type's parameters are a list"));
            };
            let pk = self.desc_kids(kids[pi], &ps);
            for (k, p) in pk.iter().zip(&ps) {
                let named = p.as_proper_list().filter(|q| q.len() == 3 && q[1].as_symbol().is_some_and(|c| self.name(c) == ":")).map(|q| q.to_vec());
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
        if result.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol()).is_some_and(|h| self.name(h) == "bool" && !self.pvars.contains_key(&h)) {
            if let Some(n) = self.pvar_in(result) {
                return Err(FxError::at(result.span, format!("pattern variable `{}` in a `(bool …)` result's propositions: not yet", self.name(n))));
            }
        } else {
            self.desc_scoped(kids[ri], result, atoms.clone())?;
        }
        for (k, c) in kids[plain..].iter().zip(&items[plain..]) {
            let parts = c.as_proper_list().expect("a clause").to_vec();
            let q = self.desc_kids(*k, &parts);
            match (self.name(parts[0].as_symbol().expect("a clause")), &q[..]) {
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
                _ => return Err(FxError::at(c.span, "a specification is `(requires proposition)`, then `(ensures name proposition)`")),
            }
        }
        Ok(())
    }

    /// A value's binder `n` a description writes (a procedure type's
    /// parameter named, its result's name), at node `at`: a pattern variable
    /// (a `bvar` the use gives), or a name the template binds; what it binds.
    fn value_binder(&mut self, at: usize, n: &Syntax) -> R<Atom> {
        self.nodes[at].core = Rc::new(STy::Bvar);
        match n.as_symbol() {
            Some(m) if self.pvars.contains_key(&m) => {
                self.nodes[at].kids = Kids::PVar(m);
                Ok(Atom::Var(m, Ns::Value, 0))
            }
            Some(m) if !reserved(self.name(m)) && !self.word(m, false) => {
                self.nodes[at].kids = Kids::Binder(m, Ns::Value);
                Ok(Atom::Lit(at, Ns::Value))
            }
            _ => Err(FxError::at(n.span, format!("`{}` is not a name that may be bound", self.show(n)))),
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
    fn spec(&mut self, at: usize, s: &Syntax) -> R<()> {
        let name = |c: &mut Self, at: usize, n: Sym, free: Free| {
            c.nodes[at].core = Rc::new(STy::Id);
            c.nodes[at].kids = if c.pvars.contains_key(&n) { Kids::PVar(n) } else { Kids::Ref(n, Ns::Value, free) };
        };
        match &s.datum {
            Datum::Symbol(n) => name(self, at, *n, Free::Qualified),
            Datum::List { items, tail: None } => {
                let kids = self.desc_kids(at, items);
                match items[0].as_symbol() {
                    Some(h) if !self.pvars.contains_key(&h) && matches!(self.name(h), "<" | "<=" | "=" | ">" | ">=" | "not" | "and" | "or" | "implies" | "+" | "-" | "*") => {}
                    Some(h) => name(self, kids[0], h, Free::Plain),
                    None => return Err(FxError::at(s.span, "a specification's proposition or integer")),
                }
                for (k, i) in kids[1..].iter().zip(&items[1..]) {
                    self.spec(*k, i)?;
                }
            }
            Datum::List { .. } => return Err(FxError::at(s.span, "a specification's proposition is a list, not a dotted one")),
            _ => {}
        }
        Ok(())
    }

    /// A node for each of `items`, the parts of the list at node `at`, at
    /// their paths in it: `at`'s kids.
    fn desc_kids(&mut self, at: usize, items: &[Syntax]) -> Vec<usize> {
        let mut path = self.nodes[at].path.clone();
        let mut kids = Vec::new();
        // `p ...` last: `p` repeated, the `...` no part of its own.
        let repeated = items.len() >= 2 && is_ellipsis(&items[items.len() - 1], self.interner);
        let items = if repeated { &items[..items.len() - 1] } else { items };
        for i in items {
            let mut p = path.clone();
            p.push(true);
            kids.push(self.nodes.len());
            self.nodes.push(Node { syn: i.clone(), path: p, core: Rc::new(STy::Type), imports: Vec::new(), export: None, many: false, hole: None, desc: false, repeated: false, kids: Kids::Other });
            path.push(false);
        }
        if repeated && let Some(&k) = kids.last() {
            self.nodes[k].repeated = true;
        }
        self.nodes[at].kids = Kids::Desc(kids.clone());
        kids
    }

    /// Description `s` at node `at`, in the scope of `atoms`.
    fn desc_scoped(&mut self, at: usize, s: &Syntax, atoms: Vec<Atom>) -> R<()> {
        self.nodes[at].imports.push((Bind::Direct(atoms), at));
        self.desc(at, s)
    }

    /// A description's binder `n`, at node `at`: a pattern variable (a
    /// `dvar` the use gives), or a name the template binds; what it binds.
    fn desc_binder(&mut self, at: usize, n: &Syntax) -> R<Atom> {
        self.nodes[at].core = Rc::new(STy::Dvar);
        match n.as_symbol() {
            Some(m) if self.pvars.contains_key(&m) => {
                self.nodes[at].kids = Kids::PVar(m);
                Ok(Atom::Var(m, Ns::Desc, 0))
            }
            Some(m) if self.mode == Mode::Program || (!reserved(self.name(m)) && !self.word(m, false)) => {
                self.nodes[at].kids = Kids::Binder(m, Ns::Desc);
                Ok(Atom::Lit(at, Ns::Desc))
            }
            _ => Err(FxError::at(n.span, format!("`{}` is not a name that may be bound", self.show(n)))),
        }
    }

    /// `((name kind) …)` at node `at`, a binder's place or `distinct` third
    /// if any, each in the scope of those before it: what they bind.
    fn desc_binders(&mut self, at: usize, bs: &Syntax) -> R<Vec<Atom>> {
        let entries = bs.as_proper_list().map(|l| l.to_vec()).unwrap_or_default();
        let ek = self.desc_kids(at, &entries);
        let mut atoms = Vec::new();
        for (k, e) in ek.iter().zip(&entries) {
            let parts = e.as_proper_list().map(|l| l.to_vec()).unwrap_or_default();
            let ([n, _] | [n, _, _]) = &parts[..] else {
                return Err(FxError::at(e.span, "a binder is `(name kind)`"));
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
            let is_poly = self.nodes[at].syn.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol()).is_some_and(|h| self.name(h) == "poly" && !self.pvars.contains_key(&h));
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

    /// A pattern variable written somewhere inside `s`.
    fn pvar_in(&self, s: &Syntax) -> Option<Sym> {
        match &s.datum {
            Datum::Symbol(n) if self.pvars.contains_key(n) => Some(*n),
            Datum::List { items, tail } => items.iter().chain(tail.as_deref()).find_map(|x| self.pvar_in(x)),
            _ => None,
        }
    }

    fn show(&self, s: &Syntax) -> String {
        fixpt_read::write_syntax(s, self.interner)
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
                env = env.within(self.eval(b, *root, node.syn.span)?);
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
                    for l in self.levels_of(*x, node.syn.span)? {
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
    fn eval(&self, b: &Bind, root: usize, span: Span) -> R<Vec<Level>> {
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
    fn rib(&self, entries: &[(Addr, Delta)], root: usize, span: Span) -> R<Vec<Atom>> {
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
                (Delta::Var, Kids::PVar(n)) if value => out.push(Atom::Var(*n, Ns::Value, 0)),
                (Delta::Var, Kids::Binder(_, Ns::Value)) => out.push(Atom::Lit(t, Ns::Value)),
                (Delta::Var, _) => return Err(FxError::at(node.syn.span, "the signature says a value's binder is here")),
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
                (Delta::Dvar | Delta::Place, _) => return Err(FxError::at(node.syn.span, "the signature says a description's binder is here")),
                // A use's description: what its own `poly`s bind is the
                // use's, which nothing the template writes can name.
                (Delta::Rib, Kids::PVar(_)) if matches!(&*node.core, STy::Type) => {}
                (Delta::Rib, Kids::PVar(n)) => out.push(Atom::RibOf(*n)),
                (Delta::Rib, Kids::Seq(..)) => match &self.exported(t).export {
                    Some((Bind::Rib(es), r)) => out.extend(self.gathered(t, self.rib(es, *r, span)?)),
                    Some((Bind::Direct(atoms), _)) => out.extend(atoms.iter().cloned()),
                    _ => return Err(FxError::at(node.syn.span, "the signature says what is here exports a rib, and it exports none")),
                },
                (Delta::Rib, _) => match &self.exported(t).export {
                    Some((Bind::Rib(es), r)) => work.push((es, *r)),
                    Some((Bind::Direct(atoms), _)) => out.extend(atoms.iter().cloned()),
                    // A use of a macro that makes definitions: none the
                    // template sees.
                    None if matches!(node.kids, Kids::Form(_)) => {}
                    _ => return Err(FxError::at(node.syn.span, "the signature says what is here exports a rib, and it exports none")),
                },
                (Delta::Env, _) => return Err(FxError::at(node.syn.span, "a ribcage (`env`) in a rib: write it `(at ℓ)` in a `cage`")),
            }
        }
        Ok(out)
    }

    fn levels_of(&self, t: usize, span: Span) -> R<Vec<Level>> {
        let node = &self.nodes[t];
        match (&node.kids, &self.exported(t).export) {
            (Kids::PVar(n), _) => Ok(vec![Level::Cage(*n)]),
            (_, Some((b, r))) => Ok(self.gathered_levels(t, self.eval(b, *r, span)?)),
            // A ribcage's list by ellipsis: what each element exports.
            (Kids::Seq(e, true), None) => Ok(self.gathered_levels(t, self.levels_of(*e, span)?)),
            (Kids::Form(_), None) => Ok(Vec::new()),
            _ => Err(FxError::at(node.syn.span, "the signature says what is here exports a ribcage, and it exports none")),
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

    fn nav(&self, root: usize, addr: &Addr, span: Span) -> R<usize> {
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
    fn placed(&self, n: Sym, info: &PInfo, want: &Rc<STy>, env: &[Level], span: Span) -> R<()> {
        use STy::*;
        let name = self.name(n);
        let have = &info.core;
        let want_u = self.m.unfold(want);
        let fits = match (&**have, &**want_u) {
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
            (Expr | Id | Data | Type | Label | Bvar | Dvar | Kind | Lambda | Defn, _) | (_, Expr | Id | Data | Type | Label | Bvar | Dvar | Kind | Lambda | Defn) => false,
            _ => self.m.sub(have, want, &mut HashSet::new()),
        };
        if !fits {
            return Err(FxError::at(span, format!("`{name}` is placed where its syntax type is not one the form takes there")));
        }
        if normal(env) != normal(&info.declared) {
            return Err(FxError::at(span, format!("`{name}` is placed in the scope of other bindings than its signature says it is")));
        }
        Ok(())
    }
}

impl Aligner<'_> {
    /// Pattern binder `n`, of namespace `ns`, referred to in `env`: in its
    /// scope, and where no other of the pattern's binders of that namespace
    /// may shadow it (Herman's shadow restriction). A value's binder never
    /// shadows a description's; every description's shares one namespace.
    fn in_scope(&self, n: Sym, ns: Ns, env: &[Level], span: Span) -> R<()> {
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
    /// alike: coinductive, as FX-26's recursive types are.
    fn sub(&self, a: &Rc<STy>, b: &Rc<STy>, assumed: &mut HashSet<(usize, usize)>) -> bool {
        use STy::*;
        let key = (Rc::as_ptr(a) as usize, Rc::as_ptr(b) as usize);
        if Rc::ptr_eq(a, b) || assumed.contains(&key) {
            return true;
        }
        assumed.insert(key);
        match (&**a, &**b) {
            (Import(x, p), Import(y, q)) | (Export(x, p), Export(y, q)) => p == q && self.sub(x, y, assumed),
            (Many(x), _) | (Typed(x, _), _) => self.sub(x, b, assumed),
            (_, Many(y)) | (_, Typed(y, _)) => self.sub(a, y, assumed),
            (Mu(i), _) => self.sub(&self.mus[*i], b, assumed),
            (_, Mu(j)) => self.sub(a, &self.mus[*j], assumed),
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
    sig: Option<Syntax>,
    lits: Vec<Sym>,
    clauses: Vec<Syntax>,
    span: Span,
    /// A procedural macro's transformer: its style, and the procedure.
    procedural: Option<(procedural::Style, Syntax)>,
}

/// The macros `form` defines: a `define-syntax`'s one, or each of a
/// `define-syntax-rec`'s, `(define-syntax-rec (name [σ] (syntax-rules …)) …)`,
/// all defined together, so that each template may use any of them.
fn written(form: &Syntax, interner: &Interner) -> R<Vec<Written>> {
    let usage = "`(define-syntax name [signature] (syntax-rules (literal …) ((_ . pattern) template) …))`";
    let rec = "`(define-syntax-rec (name [signature] (syntax-rules (literal …) clause …)) …)`";
    let items = form.as_proper_list().ok_or_else(|| FxError::at(form.span, usage))?;
    if items.first().and_then(|h| h.as_symbol()).is_some_and(|h| interner.name(h) == "define-syntax-rec") {
        if items.len() < 2 {
            return Err(FxError::at(form.span, rec));
        }
        let mut out: Vec<Written> = Vec::new();
        for m in &items[1..] {
            let Some([name, rest @ ..]) = m.as_proper_list() else {
                return Err(FxError::at(m.span, rec));
            };
            let w = written_one(name, rest, m.span, rec, interner)?;
            if out.iter().any(|o| o.name == w.name) {
                return Err(FxError::at(name.span, format!("`{}` is defined twice in this `define-syntax-rec`", interner.name(w.name))));
            }
            out.push(w);
        }
        return Ok(out);
    }
    let [_, name, rest @ ..] = items else {
        return Err(FxError::at(form.span, usage));
    };
    Ok(vec![written_one(name, rest, form.span, usage, interner)?])
}

fn written_one(name: &Syntax, rest: &[Syntax], at: Span, usage: &str, interner: &Interner) -> R<Written> {
    let name = name.as_symbol().filter(|n| !reserved(interner.name(*n))).ok_or_else(|| FxError::at(name.span, format!("{usage}: a macro's name, not a form's")))?;
    let rules = |s: &Syntax| s.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol()).is_some_and(|h| interner.name(h) == "syntax-rules");
    // A procedural macro: `(er-macro-transformer proc)`, `(sc-macro-
    // transformer proc)` or `(rsc-macro-transformer proc)`, no signature.
    if let [t] = rest
        && let Some(items) = t.as_proper_list()
        && let Some(style) = items.first().and_then(|h| h.as_symbol()).and_then(|h| procedural::Style::named(interner.name(h)))
    {
        let [_, code] = items else {
            return Err(FxError::at(t.span, format!("`({} procedure)`", interner.name(items[0].as_symbol().expect("a head")))));
        };
        return Ok(Written { name, sig: None, lits: Vec::new(), clauses: Vec::new(), span: at, procedural: Some((style, code.clone())) });
    }
    let (sig, rules) = match rest {
        [r] if rules(r) => (None, r),
        [sig, r] if rules(r) => (Some(sig.clone()), r),
        // The clauses are a transformer's, which says how to read them.
        [_, c, ..] if c.as_proper_list().is_some_and(|l| l.len() == 2) => {
            return Err(FxError::at(c.span, "a macro's clauses are a transformer's: `(syntax-rules (literal …) ((_ . pattern) template) …)`, after its signature if it is written"));
        }
        _ => return Err(FxError::at(at, usage.to_string())),
    };
    let parts = rules.as_proper_list().expect("a list");
    let Some((lits, clauses)) = parts[1..].split_first() else {
        return Err(FxError::at(rules.span, "`(syntax-rules (literal …) ((_ . pattern) template) …)`"));
    };
    let lits = match &lits.datum {
        Datum::Nil => Vec::new(),
        _ => lits.as_proper_list().and_then(|l| l.iter().map(|x| x.as_symbol()).collect::<Option<Vec<_>>>()).ok_or_else(|| FxError::at(lits.span, "a `syntax-rules`' literals are a list of names"))?,
    };
    Ok(Written { name, sig, lits, clauses: clauses.to_vec(), span: at, procedural: None })
}

fn bind(b: &Syntax, interner: &Interner) -> R<Bind> {
    let usage = "a binding is `(rho (address δ) …)` or `(cage (rho …) (at address) …)`";
    let items = b.as_proper_list().ok_or_else(|| FxError::at(b.span, usage))?;
    let head = items.first().and_then(|h| h.as_symbol()).map(|h| interner.name(h));
    let rib = |entries: &[Syntax]| -> R<Vec<(Addr, Delta)>> {
        entries
            .iter()
            .map(|e| match e.as_proper_list() {
                Some([a, d]) => {
                    let d = match d.as_symbol().map(|d| interner.name(d)) {
                        Some("none") => Delta::None,
                        Some("var") => Delta::Var,
                        Some("dvar") => Delta::Dvar,
                        Some("place") => Delta::Place,
                        Some("rib") => Delta::Rib,
                        Some("env") => Delta::Env,
                        _ => return Err(FxError::at(d.span, "δ is `none`, `var`, `dvar`, `place`, `rib` or `env`")),
                    };
                    Ok((addr(a, interner)?, d))
                }
                _ => Err(FxError::at(e.span, usage)),
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
                    let parts = r.as_proper_list().ok_or_else(|| FxError::at(r.span, usage))?;
                    match parts.first().and_then(|h| h.as_symbol()).map(|h| interner.name(h)) {
                        Some("rho") => Ok(Ring::Rib(rib(&parts[1..])?)),
                        Some("at") if parts.len() == 2 => Ok(Ring::At(addr(&parts[1], interner)?)),
                        _ => Err(FxError::at(r.span, usage)),
                    }
                })
                .collect::<R<Vec<_>>>()?;
            Ok(Bind::Cage(rings))
        }
        _ => Err(FxError::at(b.span, usage)),
    }
}

/// A typed hole's keywords and what each says, `#:type T` and, of an
/// `expr`, `#:effect E`, each once.
fn hole(parts: &[Syntax], kind: &str, s: &Syntax, interner: &Interner) -> R<Hole> {
    let expr = kind == "expr";
    let usage = if expr { "`(expr #:type T #:effect E)`, either left out".to_string() } else { format!("`({kind} #:type T)`") };
    let mut h = Hole { ty: None, effect: None };
    let mut rest = parts;
    while let [k, v, more @ ..] = rest {
        let slot = match &k.datum {
            Datum::Keyword(w) if interner.name(*w) == "type" => &mut h.ty,
            Datum::Keyword(w) if expr && interner.name(*w) == "effect" => &mut h.effect,
            _ => return Err(FxError::at(k.span, format!("a syntax type: {usage}"))),
        };
        if slot.replace(v.clone()).is_some() {
            return Err(FxError::at(k.span, format!("a syntax type: {usage}, each once")));
        }
        rest = more;
    }
    if !rest.is_empty() {
        return Err(FxError::at(s.span, format!("a syntax type: {usage}")));
    }
    Ok(h)
}

/// An address, `A`s and `D`s read right to left, or `()`, none: its steps,
/// first first.
fn addr(a: &Syntax, interner: &Interner) -> R<Addr> {
    if matches!(a.datum, Datum::Nil) {
        return Ok(Vec::new());
    }
    let name = a.as_symbol().map(|a| interner.name(a)).filter(|n| !n.is_empty() && n.chars().all(|c| c == 'A' || c == 'D'));
    let Some(name) = name else {
        return Err(FxError::at(a.span, "an address is a word of `A` (car) and `D` (cdr), read right to left"));
    };
    Ok(name.chars().rev().map(|c| c == 'A').collect())
}

/// `s`, at `path`, each symbol at a path of `renamed` renamed so.
fn rename_paths(s: &Syntax, path: &mut Vec<bool>, renamed: &HashMap<Vec<bool>, String>, interner: &mut Interner) -> Syntax {
    if let Some(n) = renamed.get(path) {
        return Syntax::symbol(s.span, interner.intern(n));
    }
    match &s.datum {
        Datum::List { items, tail } => {
            let depth = path.len();
            let mut out = Vec::new();
            for i in items {
                path.push(true);
                out.push(rename_paths(i, path, renamed, interner));
                path.pop();
                path.push(false);
            }
            let tail = tail.as_ref().map(|t| Box::new(rename_paths(t, path, renamed, interner)));
            path.truncate(depth);
            Syntax::new(s.span, Datum::List { items: out, tail })
        }
        _ => s.clone(),
    }
}

/// Whether `t` uses `mu` `id`'s variable only under a pair.
fn guarded(t: &STy, id: usize) -> bool {
    match t {
        STy::Mu(j) => *j != id,
        STy::Import(b, _) | STy::Export(b, _) | STy::Many(b) | STy::Typed(b, _) => guarded(b, id),
        STy::Union(ms) => ms.iter().all(|m| guarded(m, id)),
        _ => true,
    }
}

/// A form's name, `#%fx` or `#%toplevel`: never bound, so never a binder or
/// a variable.
fn reserved(name: &str) -> bool {
    crate::top::KEYWORDS.contains(&name) || name == "#%fx" || name == "#%toplevel" || name == "define-syntax" || name == "define-syntax-rec"
}

/// A list's car and cdr, the cdr a list of the rest (or the tail).
/// `s`, `depth` lists deep: a list deeper, `()` at its place.
fn shallow(s: &Syntax, depth: usize) -> Syntax {
    match &s.datum {
        Datum::List { .. } if depth == 0 => Syntax::new(s.span, Datum::Nil),
        Datum::List { items, tail } => Syntax::new(
            s.span,
            Datum::List { items: items.iter().map(|i| shallow(i, depth - 1)).collect(), tail: tail.as_ref().map(|t| Box::new(shallow(t, depth - 1))) },
        ),
        _ => s.clone(),
    }
}

/// `split` of `s`, which is taken: its parts moved, not copied.
fn split_owned(s: Syntax) -> Option<(Syntax, Syntax)> {
    let Datum::List { mut items, tail } = s.datum else { return None };
    if items.is_empty() {
        return split_owned(*tail?);
    }
    if items.len() > 1 {
        let first = items.remove(0);
        return Some((first, Syntax::new(s.span, Datum::List { items, tail })));
    }
    let first = items.pop()?;
    Some((first, tail.map(|t| *t).unwrap_or_else(|| Syntax::new(s.span, Datum::Nil))))
}

fn split(s: &Syntax) -> Option<(Syntax, Syntax)> {
    let Datum::List { items, tail } = &s.datum else { return None };
    if items.is_empty() {
        return split(tail.as_deref()?);
    }
    let rest = if items.len() > 1 {
        Syntax::new(s.span, Datum::List { items: items[1..].to_vec(), tail: tail.clone() })
    } else {
        tail.as_deref().cloned().unwrap_or_else(|| Syntax::new(s.span, Datum::Nil))
    };
    Some((items[0].clone(), rest))
}

/// `items` and `tail` as one list: a tail that is a list joined to it, an
/// empty one dropped.
fn list_of(at: Span, mut items: Vec<Syntax>, tail: Option<Syntax>) -> Syntax {
    let tail = match tail.map(|t| t.datum) {
        None | Some(Datum::Nil) => None,
        Some(Datum::List { items: more, tail }) => {
            items.extend(more);
            tail
        }
        Some(other) => Some(Box::new(Syntax::new(at, other))),
    };
    if items.is_empty() {
        return Syntax::new(at, Datum::Nil);
    }
    Syntax::new(at, Datum::List { items, tail })
}

/// Whether `s` matches pattern `p`, binding its variables in `binds`: a
/// name the pattern variable (`_` anything), a form's name or a keyword
/// itself.
fn matches(p: &Syntax, s: &Syntax, names: &HashSet<Sym>, binds: &mut HashMap<Sym, Syntax>, interner: &Interner) -> bool {
    // `(x ...)`: each element of a list by `x`, each of its pattern
    // variables then the list of what it matched.
    if let Some(x) = ellipsis(p, interner) {
        let Some(elems) = (match &s.datum {
            Datum::Nil => Some(Vec::new()),
            _ => s.as_proper_list().map(|l| l.to_vec()),
        }) else {
            return false;
        };
        let mut each = Vec::new();
        for e in &elems {
            let mut b = HashMap::new();
            if !matches(&x, e, names, &mut b, interner) {
                return false;
            }
            each.push(b);
        }
        for n in pattern_names(&x, interner) {
            let items: Vec<Syntax> = each.iter().map(|b| b[&n].clone()).collect();
            binds.insert(n, list_of(s.span, items, None));
        }
        return true;
    }
    match &p.datum {
        Datum::Symbol(n) if interner.name(*n) == "_" => true,
        Datum::Symbol(n) if reserved(interner.name(*n)) => s.as_symbol() == Some(*n),
        // A name's pattern variable matches a name alone.
        Datum::Symbol(n) if names.contains(n) && s.as_symbol().is_none() => false,
        Datum::Symbol(n) => {
            binds.insert(*n, s.clone());
            true
        }
        Datum::Nil => matches!(s.datum, Datum::Nil),
        Datum::List { .. } => match (split(p), split(s)) {
            (Some((pa, pd)), Some((sa, sd))) => matches(&pa, &sa, names, binds, interner) && matches(&pd, &sd, names, binds, interner),
            _ => false,
        },
        other => &s.datum == other,
    }
}

/// Whether `s` is the name `...`.
fn is_ellipsis(s: &Syntax, interner: &Interner) -> bool {
    s.as_symbol().is_some_and(|n| interner.name(n) == "...")
}

/// `x` of `(x ...)`, a part repeated, if `s` is one.
fn ellipsis(s: &Syntax, interner: &Interner) -> Option<Syntax> {
    match s.as_proper_list() {
        Some([x, dots]) if is_ellipsis(dots, interner) => Some(x.clone()),
        _ => None,
    }
}

/// What a pattern variable repeated was given: the list's elements.
fn elements(s: &Syntax) -> Vec<Syntax> {
    match &s.datum {
        Datum::Nil => Vec::new(),
        _ => s.as_proper_list().map(|l| l.to_vec()).unwrap_or_default(),
    }
}

/// The pattern variables in pattern `p`: its names but `_`, `...` and the
/// forms' (which match themselves).
fn pattern_names(p: &Syntax, interner: &Interner) -> Vec<Sym> {
    match &p.datum {
        Datum::Symbol(n) if !matches!(interner.name(*n), "_" | "...") && !reserved(interner.name(*n)) => vec![*n],
        Datum::List { items, tail } => items.iter().chain(tail.as_deref()).flat_map(|x| pattern_names(x, interner)).collect(),
        _ => Vec::new(),
    }
}

/// Whether `name` is a macro's template's check (`template_checks`), which
/// no program names, so that nothing shows it.
pub fn template_check(name: &str) -> bool {
    name.starts_with("%template:")
}

/// Name `n` where `s` writes it, the first.
fn find_symbol(s: &Syntax, n: Sym) -> Option<&Syntax> {
    match &s.datum {
        Datum::Symbol(m) if *m == n => Some(s),
        Datum::List { items, tail } => items.iter().chain(tail.as_deref()).find_map(|x| find_symbol(x, n)),
        _ => None,
    }
}

/// Whether `s` is a lambda as the checkers take one (`Checker::is_lambda`):
/// a `lambda`, `rlambda` or `vlambda`, in `plambda`s and `the`s.
fn lambda_shaped(s: &Syntax, interner: &Interner) -> bool {
    let Some(items) = s.as_proper_list() else { return false };
    match items.first().and_then(|h| h.as_symbol()).map(|h| interner.name(h)) {
        Some("lambda" | "rlambda" | "vlambda") => true,
        Some("plambda") if items.len() == 3 => lambda_shaped(&items[2], interner),
        Some("the") if items.len() == 3 => lambda_shaped(&items[2], interner),
        _ => false,
    }
}

/// Whether syntax `s` names one of `names`.
fn names_one_of(s: &Syntax, names: &[Sym]) -> bool {
    match &s.datum {
        Datum::Symbol(n) => names.contains(n),
        Datum::List { items, tail } => items.iter().chain(tail.as_deref()).any(|x| names_one_of(x, names)),
        _ => false,
    }
}

/// `s` at `at`, the place its parts were made for (a hole's call, where the
/// template has the hole).
fn respanned(s: &Syntax, at: Span) -> Syntax {
    match &s.datum {
        Datum::List { items, tail } => Syntax::new(at, Datum::List { items: items.iter().map(|x| respanned(x, at)).collect(), tail: tail.as_ref().map(|x| Box::new(respanned(x, at))) }),
        d => Syntax::new(at, d.clone()),
    }
}

/// Type `t`, which a template writes, read in module `m` (`#%toplevel`,
/// `#%fx` or a file's), at its place in expansion `made`: `(select m t)`;
/// of a definition's `(->* (param …) result)`, which is no type, each of
/// its types so.
fn selected(m: Sym, t: &Syntax, made: u32, interner: &mut Interner) -> Syntax {
    let at = t.span.in_expansion(made);
    if let Some([h, params, result]) = t.as_proper_list()
        && h.as_symbol().is_some_and(|h| interner.name(h) == "->*")
        && let Some(ps) = params.as_proper_list()
    {
        let ps: Vec<Syntax> = ps.iter().map(|p| selected(m, p, made, interner)).collect();
        let ps = list_of(params.span.in_expansion(made), ps, None);
        return Syntax::list(at, vec![in_expansion(h, made), ps, selected(m, result, made, interner)]);
    }
    let select = interner.intern("select");
    Syntax::list(at, vec![Syntax::symbol(at, select), Syntax::symbol(at, m), in_expansion(t, made)])
}

/// `s`, each part of it at its place in expansion `made` (`transcribe`'s,
/// for a part nothing in is renamed or placed).
fn in_expansion(s: &Syntax, made: u32) -> Syntax {
    let at = s.span.in_expansion(made);
    match &s.datum {
        Datum::List { items, tail } => list_of(at, items.iter().map(|x| in_expansion(x, made)).collect(), tail.as_ref().map(|x| in_expansion(x, made))),
        Datum::Vector(items) => Syntax::new(at, Datum::Vector(items.iter().map(|x| in_expansion(x, made)).collect())),
        d => Syntax::new(at, d.clone()),
    }
}

#[cfg(test)]
mod tests {
    /// The kernel file's reserved words, which the expander written in
    /// FX-26 reads, are the Rust front end's keywords.
    #[test]
    fn the_kernels_reserved_words_are_the_keywords() {
        let mut interner = fixpt_read::Interner::default();
        let forms = fixpt_read::Reader::new(super::KERNEL, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX26, &mut interner).read_all().expect("reads");
        let words: Vec<String> = super::kernel_list(&forms, &interner, "reserved-words").iter().map(|w| interner.name(w.as_symbol().expect("a name")).to_string()).collect();
        assert_eq!(words, crate::top::KEYWORDS);
    }

    /// The kernel's type forms are the checkers' (`parse.rs`'s `TYPE_FORMS`).
    #[test]
    fn the_kernels_type_forms_are_the_checkers() {
        let mut interner = fixpt_read::Interner::default();
        let forms = fixpt_read::Reader::new(super::KERNEL, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX26, &mut interner).read_all().expect("reads");
        let words: Vec<String> = super::kernel_list(&forms, &interner, "type-forms").iter().map(|w| interner.name(w.as_symbol().expect("a name")).to_string()).collect();
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
        let mut interner = fixpt_read::Interner::default();
        let forms = fixpt_read::Reader::new(super::KERNEL, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX26, &mut interner).read_all().expect("reads");
        let heads: Vec<String> = super::kernel_list(&forms, &interner, "description-heads").iter().map(|w| interner.name(w.as_symbol().expect("a name")).to_string()).collect();
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
        let body = src.split("pub fn parse_exp(").nth(1).expect("parse_exp");
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
