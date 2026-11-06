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
//! σ ::= expr | bvar | id | data | type | label | ()
//!     | (σ . σ) | (σ …)                    a pair; a list, of pairs
//!     | (import σ β) | (export σ β)        Herman's σ↓β and σ↑β
//!     | (mu v σ) | v | (union σ …)         recursion, alternatives
//!     | (literal name)                     a name written as it is (`else`)
//!     | (many σ)                           placed any number of times
//! β ::= (rho (ℓ δ) …)                      a rib, {ℓ : δ, …}
//!     | (cage ρ-or-(at ℓ) …)               ribs in order, innermost first; ℓ@γ
//! δ ::= none | var | rib | env
//! ```
//!
//! An address `ℓ` is a word of `A` (car) and `D` (cdr), read right to left
//! as `cadr` is, from the innermost `mu`, `union` member or signature
//! around it. `id`, `type` and `label` are FX-26's: a variable referred to
//! (as `set!`'s target would be), a description, a tag or field's name.
//! So is `many`: a pattern variable with an expression in it is placed at
//! most once in a template, affine, unless its part of the signature is
//! `(many σ)`; placed where another macro's signature says `many`, it is
//! taken as placed more than once, so the opt-out is said all the way up
//! a chain of macros (`docs/research/typed-macros.md`).

use crate::error::{FxError, R};
use fixpt_read::{Datum, Interner, Span, Sym, Syntax};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// A syntax type (Herman's `σ`).
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum STy {
    Expr,
    Bvar,
    Id,
    Data,
    Type,
    Label,
    Nil,
    Literal(Sym),
    Pair(Rc<STy>, Rc<STy>),
    Import(Rc<STy>, Bind),
    Export(Rc<STy>, Bind),
    /// A `mu`, by its number in `Macros::mus`; and its variable, the same.
    Mu(usize),
    /// What may be placed any number of times.
    Many(Rc<STy>),
    Union(Vec<Rc<STy>>),
}

/// What an annotation binds (Herman's `β`): a rib, or a ribcage.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Bind {
    Rib(Vec<(Addr, Delta)>),
    Cage(Vec<Ring>),
}

/// One of a ribcage's: a rib, or the ribcage exported at an address.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Ring {
    Rib(Vec<(Addr, Delta)>),
    At(Addr),
}

/// An address's steps from its root, first first: `true` the car.
type Addr = Vec<bool>;

/// What a part at an address binds (Herman's `δ`).
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Delta {
    None,
    Var,
    Rib,
    Env,
}

/// A macro defined: its signature and clauses.
#[derive(Debug)]
struct Macro {
    sig: Rc<STy>,
    clauses: Vec<Clause>,
    /// The text it was read from, its templates' places in it.
    text: Option<std::sync::Arc<str>>,
}

/// A clause: its pattern (of the operands), its template, and what is done
/// to the template's names where it is transcribed, by their paths in it.
#[derive(Debug)]
struct Clause {
    pattern: Syntax,
    template: Syntax,
    actions: HashMap<Vec<bool>, Action>,
}

/// What becomes of one of a template's names: made fresh, one name for
/// the binder found at a path and for each reference to it; or the
/// standard binding, `(with #%fx name)`.
#[derive(Clone, Debug)]
enum Action {
    Rename(Vec<bool>),
    Standard,
}

/// The macros defined, and the syntax types of the kernel's forms, for
/// checking templates. Cloned to be put back (`Checker::macros_kept`).
#[derive(Clone, Default)]
pub struct Macros {
    mus: Vec<Rc<STy>>,
    kernel: HashMap<String, Rc<STy>>,
    defined: HashMap<Sym, Rc<Macro>>,
    fresh: usize,
    /// The text being read, if it is known (`Checker::read_in`): a macro
    /// defined in it has its templates' places in it.
    pub(crate) reading: Option<std::sync::Arc<str>>,
}

/// The kernel's forms a template may use, with their binding structure
/// (each signature of a form's operands). A form not here is refused in a
/// template; what has no binders is an application, of expressions.
const KERNEL: &str = include_str!("macros-kernel.sx");

/// Where a syntax type is aligned with syntax: a macro's pattern, a
/// template, or a use.
#[derive(Clone, Copy, PartialEq)]
enum Mode {
    Pattern,
    Template,
    Use,
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
    kids: Kids,
}

enum Kids {
    Pair(usize, usize),
    Nil,
    /// A pattern variable (in a pattern, or placed in a template).
    PVar(Sym),
    /// A template's binder, a name it writes in a binding position.
    Binder(Sym),
    /// A name in a template referred to.
    Ref(Sym),
    /// A form in a template, its operands (or, an application's, itself).
    Form(usize),
    Other,
}

/// What an environment is made of: a pattern variable bound (`bvar`), the
/// rib or ribcage a pattern variable exports, a template's own binder.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Atom {
    Var(Sym),
    RibOf(Sym),
    Lit(usize),
}

/// Each pattern variable, template binder and name referred to, by node,
/// with its environment and whether it is in a `many` part (`walk`).
type Found = Vec<(usize, Vec<Level>, bool)>;

/// One level of an environment: a rib, or a pattern variable's ribcage.
#[derive(Clone, Debug, PartialEq)]
enum Level {
    Rib(Vec<Atom>),
    Cage(Sym),
}

/// A pattern variable: its type, its kind (the type's annotations off), and
/// its environment as the signature declares it.
struct PInfo {
    core: Rc<STy>,
    declared: Vec<Level>,
    /// Whether it may be placed any number of times (`(many …)`).
    many: bool,
}

/// Syntax aligned with syntax types, as a tree of `Node`s.
struct Aligner<'m> {
    m: &'m Macros,
    interner: &'m Interner,
    mode: Mode,
    pvars: &'m HashMap<Sym, PInfo>,
    nodes: Vec<Node>,
}

impl Macros {
    fn ensure_kernel(&mut self, interner: &mut Interner) -> R<()> {
        if !self.kernel.is_empty() {
            return Ok(());
        }
        let forms = fixpt_read::Reader::new(KERNEL, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX26, interner)
            .read_all()
            .map_err(|e| FxError::at(e.span, format!("the kernel's syntax types: {}", e.message)))?;
        let mut named: HashMap<Sym, Rc<STy>> = HashMap::new();
        for f in &forms {
            let items = f.as_proper_list().expect("a kernel entry");
            let what = interner.name(items[0].as_symbol().expect("a head")).to_string();
            let name = items[1].as_symbol().expect("a name");
            let t = self.sty(&items[2], interner, &named, &mut Vec::new())?;
            if what == "define" {
                named.insert(name, t);
            } else {
                self.kernel.insert(interner.name(name).to_string(), t);
            }
        }
        Ok(())
    }

    /// Whether `name` is a macro defined.
    pub fn is_macro(&self, name: Sym) -> bool {
        self.defined.contains_key(&name)
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
                        "bvar" => STy::Bvar,
                        "id" => STy::Id,
                        "data" => STy::Data,
                        "type" => STy::Type,
                        "label" => STy::Label,
                        other => return Err(bad(&format!("`{other}` is none (`expr`, `bvar`, `id`, `data`, `type`, `label`, or a `mu`'s variable)"))),
                    }
                }
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
                                if self.overlap(a, b, 6) {
                                    return Err(bad("a `union`'s members must be told apart by their shapes in the source (an `expr` may be anything)"));
                                }
                            }
                        }
                        STy::Union(ms)
                    }
                    (Some("many"), [_, body], None) => STy::Many(self.sty(body, interner, named, mus)?),
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

    /// The type at `t`, its annotations, `mu`s and unions seen through
    /// to what is under them (for overlap and fit).
    fn unfold<'a>(&'a self, t: &'a Rc<STy>) -> &'a Rc<STy> {
        match &**t {
            STy::Import(b, _) | STy::Export(b, _) | STy::Many(b) => self.unfold(b),
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
            (Literal(_), Expr | Bvar) | (Expr | Bvar, Literal(_)) => false,
            (Literal(x), Literal(y)) => x == y,
            (Literal(_), Id) | (Id, Literal(_)) => true,
            (Expr | Data | Type, _) | (_, Expr | Data | Type) => true,
            (Pair(a1, d1), Pair(a2, d2)) => depth == 0 || (self.overlap(a1, a2, depth - 1) && self.overlap(d1, d2, depth - 1)),
            (Nil, Nil) => true,
            (Label, Label) => true,
            (Label, _) | (_, Label) => false,
            (Bvar | Id, Bvar | Id) => true,
            _ => false,
        }
    }

    /// Whether `s` has the shape of `t`, in `mode`: a pattern variable in a
    /// template, or any name in a pattern, fits anything.
    fn fits(&self, t: &Rc<STy>, s: &Syntax, mode: Mode, interner: &Interner, pvars: &HashMap<Sym, PInfo>) -> bool {
        use STy::*;
        if let Some(n) = s.as_symbol() {
            let lit = matches!(&**self.unfold(t), Literal(_));
            if (mode == Mode::Pattern && !lit && interner.name(n) != "_") || (mode == Mode::Template && pvars.contains_key(&n)) {
                return true;
            }
        }
        match &**self.unfold(t) {
            Union(ms) => ms.iter().any(|m| self.fits(m, s, mode, interner, pvars)),
            Pair(a, d) => split(s).is_some_and(|(x, y)| self.fits(a, &x, mode, interner, pvars) && self.fits(d, &y, mode, interner, pvars)),
            Nil => matches!(s.datum, Datum::Nil),
            Literal(n) => s.as_symbol() == Some(*n),
            Bvar => s.as_symbol().is_some_and(|n| !reserved(interner.name(n))),
            Id => s.as_symbol().is_some(),
            Label => matches!(s.datum, Datum::Keyword(_)) || (mode == Mode::Use && s.as_symbol().is_some()),
            Expr => !s.as_symbol().is_some_and(|n| reserved(interner.name(n))) && !matches!(s.datum, Datum::Nil),
            Data | Type => true,
            Import(..) | Export(..) | Mu(_) | Many(_) => unreachable!("unfolded"),
        }
    }

    /// `(define-syntax name σ ((_ . pattern) template) …)`: checked, and
    /// defined. `is_standard` says whether a name is a standard binding,
    /// which a template's free name must be.
    pub fn define(&mut self, form: &Syntax, interner: &mut Interner, is_standard: &dyn Fn(Sym) -> bool) -> R<()> {
        self.ensure_kernel(interner)?;
        let usage = "`(define-syntax name signature ((_ . pattern) template) …)`";
        let items = form.as_proper_list().ok_or_else(|| FxError::at(form.span, usage))?;
        let [_, name, sig, clauses @ ..] = items else {
            return Err(FxError::at(form.span, usage));
        };
        let name = name.as_symbol().filter(|n| !reserved(interner.name(*n))).ok_or_else(|| FxError::at(name.span, format!("{usage}: a macro's name, not a form's")))?;
        if clauses.is_empty() {
            return Err(FxError::at(form.span, format!("{usage}: at least one clause")));
        }
        let sig = self.sty(sig, interner, &HashMap::new(), &mut Vec::new())?;
        // Defined first, so that a template may use the macro itself.
        let before = self.defined.insert(name, Rc::new(Macro { sig: sig.clone(), clauses: Vec::new(), text: None }));
        let mut checked = Vec::new();
        for c in clauses {
            match self.clause(c, &sig, interner, is_standard) {
                Ok(c) => checked.push(c),
                Err(e) => {
                    match before {
                        Some(b) => self.defined.insert(name, b),
                        None => self.defined.remove(&name),
                    };
                    return Err(e);
                }
            }
        }
        let text = self.reading.clone();
        self.defined.insert(name, Rc::new(Macro { sig, clauses: checked, text }));
        Ok(())
    }

    /// A clause checked against signature `sig` (Herman's rules): its
    /// pattern fits the signature, each of the pattern's variables is
    /// placed in the template where the signature says what is in scope
    /// there, and a reference to a pattern's binder is where no other
    /// pattern binder may shadow it.
    fn clause(&self, c: &Syntax, sig: &Rc<STy>, interner: &Interner, is_standard: &dyn Fn(Sym) -> bool) -> R<Clause> {
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
        let mut p = Aligner { m: self, interner, mode: Mode::Pattern, pvars: &none, nodes: Vec::new() };
        let root = p.align(sig, &pattern, None, Vec::new())?;
        let mut found = Vec::new();
        p.walk(root, &Vec::new(), false, &mut found)?;
        let mut pvars: HashMap<Sym, PInfo> = HashMap::new();
        for (at, env, many) in found {
            let Kids::PVar(n) = p.nodes[at].kids else { continue };
            if pvars.insert(n, PInfo { core: p.nodes[at].core.clone(), declared: env, many }).is_some() {
                return Err(FxError::at(p.nodes[at].syn.span, format!("`{}` is a pattern variable twice", interner.name(n))));
            }
        }
        // The template, an expression, aligned with the kernel's forms'
        // signatures and the macros'.
        let mut t = Aligner { m: self, interner, mode: Mode::Template, pvars: &pvars, nodes: Vec::new() };
        let root = t.align(&Rc::new(STy::Expr), template, None, Vec::new())?;
        let mut found = Vec::new();
        t.walk(root, &Vec::new(), false, &mut found)?;
        let mut actions = HashMap::new();
        let mut uses: HashMap<Sym, usize> = HashMap::new();
        for (at, env, many) in found {
            let node = &t.nodes[at];
            let span = node.syn.span;
            match &node.kids {
                Kids::PVar(n) => {
                    let info = &pvars[n];
                    let name = interner.name(*n);
                    t.placed(*n, info, &node.core, &env, span)?;
                    // Anything with an expression in it, placed twice, runs
                    // twice: placed once, unless its signature says `many`.
                    // Where another macro's says `many`, it may be placed
                    // more than once there.
                    let affine = !info.many && !matches!(&*info.core, STy::Bvar | STy::Id | STy::Label | STy::Data | STy::Type);
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
                Kids::Binder(_) => {
                    actions.insert(node.path.clone(), Action::Rename(node.path.clone()));
                }
                Kids::Ref(n) => {
                    let bound = env.iter().find_map(|l| match l {
                        Level::Rib(atoms) => atoms.iter().find_map(|a| match a {
                            Atom::Lit(b) if matches!(t.nodes[*b].kids, Kids::Binder(m) if m == *n) => Some(*b),
                            _ => None,
                        }),
                        Level::Cage(_) => None,
                    });
                    match bound {
                        Some(b) => {
                            actions.insert(node.path.clone(), Action::Rename(t.nodes[b].path.clone()));
                        }
                        None if is_standard(*n) => {
                            actions.insert(node.path.clone(), Action::Standard);
                        }
                        None => {
                            return Err(FxError::at(
                                span,
                                format!(
                                    "`{}` is not bound in the template, nor a standard binding: a template may name the program's own globals only once there is a reference to them nothing shadows (typed-macros.md, item 5)",
                                    interner.name(*n)
                                ),
                            ))
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(Clause { pattern, template: template.clone(), actions })
    }

    /// `form` with each use of a macro in it expanded, as each expands,
    /// until none is left; quoted data left as it is.
    pub fn expand(&mut self, form: &Syntax, interner: &mut Interner) -> R<Syntax> {
        if self.defined.is_empty() {
            return Ok(form.clone());
        }
        let mut budget = 10_000;
        let mut out = self.expand_in(form, interner, &mut budget)?;
        // A form of the program's is the text written for it, what a use
        // made of it or not: the REPL takes the entry's text by it.
        out.span = form.span;
        Ok(out)
    }

    fn expand_in(&mut self, s: &Syntax, interner: &mut Interner, budget: &mut usize) -> R<Syntax> {
        let Datum::List { items, tail } = &s.datum else { return Ok(s.clone()) };
        let head = items[0].as_symbol();
        if head.is_some_and(|h| interner.name(h) == "quote") {
            return Ok(s.clone());
        }
        if let Some(h) = head
            && let Some(m) = self.defined.get(&h).cloned()
        {
            if *budget == 0 {
                return Err(FxError::at(s.span, "this macro's expansion does not end"));
            }
            *budget -= 1;
            let out = self.expand_use(h, &m, s, interner)?;
            return self.expand_in(&out, interner, budget);
        }
        // A definition of a macro's name: refused, as a form's is.
        if let (Some(h), Some(n)) = (head, items.get(1).and_then(|n| n.as_symbol()))
            && matches!(interner.name(h), "define" | "define*")
            && self.defined.contains_key(&n)
        {
            return Err(FxError::at(items[1].span, format!("`{}` is a macro's name, which is not defined again", interner.name(n))));
        }
        let items = items.iter().map(|i| self.expand_in(i, interner, budget)).collect::<R<Vec<_>>>()?;
        let tail = match tail {
            Some(t) => Some(Box::new(self.expand_in(t, interner, budget)?)),
            None => None,
        };
        Ok(Syntax::new(s.span, Datum::List { items, tail }))
    }

    /// A use of macro `name`, parsed by its signature, then the first clause
    /// whose pattern matches it transcribed.
    fn expand_use(&mut self, name: Sym, m: &Macro, s: &Syntax, interner: &mut Interner) -> R<Syntax> {
        let (_, operands) = split(s).expect("a list");
        let none = HashMap::new();
        let mut u = Aligner { m: self, interner, mode: Mode::Use, pvars: &none, nodes: Vec::new() };
        u.align(&m.sig, &operands, None, Vec::new()).map_err(|e| FxError::at(e.span, format!("a use of `{}`: {}", interner.name(name), e.message)))?;
        for c in &m.clauses {
            let mut binds = HashMap::new();
            if !matches(&c.pattern, &operands, &mut binds, interner) {
                continue;
            }
            let mut fresh: HashMap<Vec<bool>, Sym> = HashMap::new();
            let made = fixpt_read::record_expansion(interner.name(name), s.span, m.text.clone());
            return Ok(self.transcribe(c, &c.template, &mut Vec::new(), &binds, &mut fresh, made, interner));
        }
        Err(FxError::at(s.span, format!("a use of `{}` that no clause of it matches", interner.name(name))))
    }

    /// Template `t`, at `path` in it, transcribed by expansion `made`: each
    /// part the template makes at its own place in the `define-syntax`, of
    /// that expansion (provenance, not identity:
    /// `docs/research/loads-and-places.md`, "Decided: identity by
    /// position"), each pattern variable's what the use gave.
    #[allow(clippy::too_many_arguments)]
    fn transcribe(&mut self, c: &Clause, t: &Syntax, path: &mut Vec<bool>, binds: &HashMap<Sym, Syntax>, fresh: &mut HashMap<Vec<bool>, Sym>, made: u32, interner: &mut Interner) -> Syntax {
        let at = t.span.in_expansion(made);
        match &t.datum {
            Datum::Symbol(n) => {
                if let Some(b) = binds.get(n) {
                    return b.clone();
                }
                match c.actions.get(&*path) {
                    Some(Action::Rename(binder)) => {
                        let name = match fresh.get(binder) {
                            Some(f) => *f,
                            None => {
                                self.fresh += 1;
                                let f = interner.intern(&format!("%{}:{}", interner.name(*n), self.fresh));
                                fresh.insert(binder.clone(), f);
                                f
                            }
                        };
                        Syntax::symbol(at, name)
                    }
                    Some(Action::Standard) => {
                        let (with, fx) = (interner.intern("with"), interner.intern("#%fx"));
                        Syntax::list(at, vec![Syntax::symbol(at, with), Syntax::symbol(at, fx), Syntax::symbol(at, *n)])
                    }
                    None => Syntax::new(at, t.datum.clone()),
                }
            }
            Datum::List { items, tail } => {
                let depth = path.len();
                let mut out = Vec::new();
                for item in items {
                    path.push(true);
                    out.push(self.transcribe(c, item, path, binds, fresh, made, interner));
                    path.pop();
                    path.push(false);
                }
                let tail = tail.as_ref().map(|x| self.transcribe(c, x, path, binds, fresh, made, interner));
                path.truncate(depth);
                list_of(at, out, tail)
            }
            _ => Syntax::new(at, t.datum.clone()),
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
        let at = self.nodes.len();
        self.nodes.push(Node { syn: s.clone(), path, core: t.clone(), imports: Vec::new(), export: None, many: false, kids: Kids::Other });
        self.fill(at, t, s, root.unwrap_or(at))?;
        Ok(at)
    }

    fn fill(&mut self, at: usize, t: &Rc<STy>, s: &Syntax, root: usize) -> R<()> {
        let fail = |why: String| FxError::at(s.span, why);
        match &**t {
            STy::Import(body, b) => {
                self.nodes[at].imports.push((b.clone(), root));
                return self.fill(at, body, s, root);
            }
            STy::Many(body) => {
                self.nodes[at].many = true;
                return self.fill(at, body, s, root);
            }
            STy::Export(body, b) => {
                if self.nodes[at].export.is_some() {
                    return Err(fail("two exports at one part".into()));
                }
                self.nodes[at].export = Some((b.clone(), root));
                return self.fill(at, body, s, root);
            }
            _ => {}
        }
        self.nodes[at].core = t.clone();
        // A pattern's variable, or one placed in a template: at any type.
        if let Some(n) = s.as_symbol() {
            let lit = matches!(&**self.m.unfold(t), STy::Literal(_));
            let pvar = match self.mode {
                Mode::Pattern => !lit && self.name(n) != "_",
                Mode::Template => self.pvars.contains_key(&n),
                Mode::Use => false,
            };
            if pvar {
                self.nodes[at].kids = Kids::PVar(n);
                return Ok(());
            }
        }
        match &**t {
            STy::Mu(id) => {
                let body = self.m.mus[*id].clone();
                self.fill(at, &body, s, at)
            }
            STy::Union(ms) => {
                let fit: Vec<&Rc<STy>> = ms.iter().filter(|m| self.m.fits(m, s, self.mode, self.interner, self.pvars)).collect();
                match &fit[..] {
                    [one] => {
                        let one = (*one).clone();
                        self.fill(at, &one, s, at)
                    }
                    [] => Err(fail(format!("`{}` is of none of the shapes this part may have", self.show(s)))),
                    _ => Err(fail(format!("`{}` could be of more than one of this part's shapes", self.show(s)))),
                }
            }
            STy::Pair(a, d) => {
                let Some((x, y)) = split(s) else {
                    return Err(fail(format!("`{}` is not a list as this part must be", self.show(s))));
                };
                let path = self.nodes[at].path.clone();
                let mut ap = path.clone();
                ap.push(true);
                let mut dp = path;
                dp.push(false);
                let x = self.align(a, &x, Some(root), ap)?;
                let y = self.align(d, &y, Some(root), dp)?;
                self.nodes[at].kids = Kids::Pair(x, y);
                Ok(())
            }
            STy::Nil => match &s.datum {
                Datum::Nil => {
                    self.nodes[at].kids = Kids::Nil;
                    Ok(())
                }
                _ => Err(fail(format!("`{}` is more than this part may have", self.show(s)))),
            },
            STy::Literal(n) => match s.as_symbol() {
                Some(m) if m == *n => Ok(()),
                _ => Err(fail(format!("`{}` where `{}` is written", self.show(s), self.name(*n)))),
            },
            STy::Bvar => match s.as_symbol() {
                Some(n) if self.m.defined.contains_key(&n) => Err(fail(format!("`{}` is a macro's name, which is not bound", self.name(n)))),
                Some(n) if !reserved(self.name(n)) => {
                    if self.mode == Mode::Template {
                        self.nodes[at].kids = Kids::Binder(n);
                    }
                    Ok(())
                }
                _ => Err(fail(format!("`{}` is not a name that may be bound", self.show(s)))),
            },
            STy::Id => match s.as_symbol() {
                Some(n) => {
                    if self.mode == Mode::Template {
                        self.nodes[at].kids = Kids::Ref(n);
                    }
                    Ok(())
                }
                None => Err(fail(format!("`{}` is not a variable", self.show(s)))),
            },
            STy::Label => match &s.datum {
                Datum::Keyword(_) => Ok(()),
                Datum::Symbol(_) if self.mode == Mode::Use => Ok(()),
                Datum::Symbol(n) => Err(fail(format!("a tag or label in a template is a keyword: `#:{}`, not `{0}`", self.name(*n)))),
                _ => Err(fail(format!("`{}` is not a tag or label", self.show(s)))),
            },
            STy::Data | STy::Type => {
                if self.mode == Mode::Template && let Some(n) = self.pvar_in(s) {
                    return Err(fail(format!("pattern variable `{}` inside a quoted datum or a type: only a whole one is placed", self.name(n))));
                }
                Ok(())
            }
            STy::Expr => match (&s.datum, self.mode) {
                (Datum::Symbol(n), _) if reserved(self.name(*n)) => Err(fail(format!("`{}` is a form's name, not an expression", self.name(*n)))),
                (Datum::Symbol(n), Mode::Template) => {
                    self.nodes[at].kids = Kids::Ref(*n);
                    Ok(())
                }
                (Datum::List { .. }, Mode::Template) => self.form(at, s),
                (Datum::Nil, _) => Err(fail("`()` is not an expression".into())),
                _ => Ok(()),
            },
            STy::Import(..) | STy::Export(..) | STy::Many(_) => unreachable!("taken off"),
        }
    }

    /// A form in a template, at node `at`: a kernel form, a macro's use, or
    /// an application, aligned with its signature.
    fn form(&mut self, at: usize, s: &Syntax) -> R<()> {
        let Datum::List { items, tail } = &s.datum else { unreachable!("a list") };
        let head = items[0].as_symbol().filter(|h| !self.pvars.contains_key(h));
        let sig = match head.map(|h| (h, self.name(h))) {
            Some((_, "with")) => {
                let standard = tail.is_none() && matches!(&items[..], [_, m, n] if m.as_symbol().is_some_and(|m| self.name(m) == "#%fx") && n.as_symbol().is_some());
                if standard {
                    return Ok(());
                }
                return Err(FxError::at(s.span, "a template's `with` is `(with #%fx name)` (one opening a module waits for scopes of a module's names)"));
            }
            Some((h, _)) if self.m.defined.contains_key(&h) => Some(self.m.defined[&h].sig.clone()),
            Some((_, n)) if self.m.kernel.contains_key(n) && n != "%app" => Some(self.m.kernel[n].clone()),
            Some((_, n)) if reserved(n) => {
                return Err(FxError::at(s.span, format!("the prototype does not know `{n}`'s binding structure: not yet in a template")));
            }
            _ => None,
        };
        let path = self.nodes[at].path.clone();
        let x = match sig {
            Some(sig) => {
                let (_, operands) = split(s).expect("a list");
                let mut p = path;
                p.push(false);
                self.align(&sig, &operands, None, p)?
            }
            None => {
                let app = self.m.kernel["%app"].clone();
                self.align(&app, s, None, path)?
            }
        };
        self.nodes[at].kids = Kids::Form(x);
        Ok(())
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
    fn walk(&self, at: usize, env: &Vec<Level>, many: bool, found: &mut Found) -> R<()> {
        let node = &self.nodes[at];
        let many = many || node.many;
        let mut env = env.clone();
        for (b, root) in &node.imports {
            let mut levels = self.eval(b, *root, node.syn.span)?;
            levels.extend(env);
            env = levels;
        }
        match &node.kids {
            Kids::Pair(x, y) => {
                self.walk(*x, &env, many, found)?;
                self.walk(*y, &env, many, found)
            }
            Kids::Form(x) => self.walk(*x, &env, many, found),
            Kids::PVar(_) | Kids::Binder(_) | Kids::Ref(_) => {
                found.push((at, env, many));
                Ok(())
            }
            Kids::Nil | Kids::Other => Ok(()),
        }
    }

    /// What `b` binds, its addresses from `root`: levels, innermost first.
    fn eval(&self, b: &Bind, root: usize, span: Span) -> R<Vec<Level>> {
        match b {
            Bind::Rib(entries) => Ok(vec![Level::Rib(self.rib(entries, root, span)?)]),
            Bind::Cage(rings) => {
                let mut out = Vec::new();
                for r in rings {
                    match r {
                        Ring::Rib(entries) => out.push(Level::Rib(self.rib(entries, root, span)?)),
                        Ring::At(addr) => {
                            let t = self.nav(root, addr, span)?;
                            out.extend(self.levels_of(t, span)?);
                        }
                    }
                }
                Ok(out)
            }
        }
    }

    fn rib(&self, entries: &[(Addr, Delta)], root: usize, span: Span) -> R<Vec<Atom>> {
        let mut out = Vec::new();
        for (addr, delta) in entries {
            let t = self.nav(root, addr, span)?;
            let node = &self.nodes[t];
            match (delta, &node.kids) {
                (Delta::None, _) => {}
                (Delta::Var, Kids::PVar(n)) => out.push(Atom::Var(*n)),
                (Delta::Var, Kids::Binder(_)) => out.push(Atom::Lit(t)),
                (Delta::Var, _) => return Err(FxError::at(node.syn.span, "the signature says a binder is here")),
                (Delta::Rib, Kids::PVar(n)) => out.push(Atom::RibOf(*n)),
                (Delta::Rib, _) => match &node.export {
                    Some((Bind::Rib(es), r)) => out.extend(self.rib(es, *r, span)?),
                    _ => return Err(FxError::at(node.syn.span, "the signature says what is here exports a rib, and it exports none")),
                },
                (Delta::Env, _) => return Err(FxError::at(node.syn.span, "a ribcage (`env`) in a rib: write it `(at ℓ)` in a `cage`")),
            }
        }
        Ok(out)
    }

    fn levels_of(&self, t: usize, span: Span) -> R<Vec<Level>> {
        let node = &self.nodes[t];
        match (&node.kids, &node.export) {
            (Kids::PVar(n), _) => Ok(vec![Level::Cage(*n)]),
            (_, Some((b, r))) => self.eval(b, *r, span),
            _ => Err(FxError::at(node.syn.span, "the signature says what is here exports a ribcage, and it exports none")),
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
            (Bvar, Bvar) => return Ok(()),
            // A pattern's binder referred to: in its scope, and where no other
            // of the pattern's binders may shadow it (the shadow restriction).
            (Bvar, Expr | Id) => {
                let Some(i) = env.iter().position(|l| matches!(l, Level::Rib(atoms) if atoms.contains(&Atom::Var(n)))) else {
                    return Err(FxError::at(span, format!("`{name}` is referred to where the template does not bind it")));
                };
                let pattern_atom = |a: &Atom| !matches!(a, Atom::Lit(_));
                if env[..i].iter().any(|l| matches!(l, Level::Cage(_)) || matches!(l, Level::Rib(atoms) if atoms.iter().any(pattern_atom))) {
                    return Err(FxError::at(span, format!("`{name}` is referred to where another of the pattern's binders may shadow it (Herman's shadow restriction): a use giving both one name would change what it refers to")));
                }
                return Ok(());
            }
            (Expr, Expr) | (Id, Expr | Id) => true,
            (Data, Data) | (Type, Type) | (Label, Label) => return Ok(()),
            (Expr | Id | Data | Type | Label | Bvar, _) | (_, Expr | Id | Data | Type | Label | Bvar) => false,
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
            (Many(x), _) => self.sub(x, b, assumed),
            (_, Many(y)) => self.sub(a, y, assumed),
            (Mu(i), _) => self.sub(&self.mus[*i], b, assumed),
            (_, Mu(j)) => self.sub(a, &self.mus[*j], assumed),
            (Union(ms), _) => ms.iter().all(|m| self.sub(m, b, assumed)),
            (_, Union(ms)) => ms.iter().any(|m| self.sub(a, m, assumed)),
            (Import(..) | Export(..), _) | (_, Import(..) | Export(..)) => false,
            (Pair(a1, d1), Pair(a2, d2)) => self.sub(a1, a2, assumed) && self.sub(d1, d2, assumed),
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
                let mut a: Vec<Atom> = atoms.iter().filter(|a| !matches!(a, Atom::Lit(_))).cloned().collect();
                a.sort();
                (!a.is_empty()).then_some(Level::Rib(a))
            }
            Level::Cage(n) => Some(Level::Cage(*n)),
        })
        .collect()
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
                        Some("rib") => Delta::Rib,
                        Some("env") => Delta::Env,
                        _ => return Err(FxError::at(d.span, "δ is `none`, `var`, `rib` or `env`")),
                    };
                    Ok((addr(a, interner)?, d))
                }
                _ => Err(FxError::at(e.span, usage)),
            })
            .collect()
    };
    match head {
        Some("rho") => Ok(Bind::Rib(rib(&items[1..])?)),
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

/// An address, `A`s and `D`s read right to left: its steps, first first.
fn addr(a: &Syntax, interner: &Interner) -> R<Addr> {
    let name = a.as_symbol().map(|a| interner.name(a)).filter(|n| !n.is_empty() && n.chars().all(|c| c == 'A' || c == 'D'));
    let Some(name) = name else {
        return Err(FxError::at(a.span, "an address is a word of `A` (car) and `D` (cdr), read right to left"));
    };
    Ok(name.chars().rev().map(|c| c == 'A').collect())
}

/// Whether `t` uses `mu` `id`'s variable only under a pair.
fn guarded(t: &STy, id: usize) -> bool {
    match t {
        STy::Mu(j) => *j != id,
        STy::Import(b, _) | STy::Export(b, _) | STy::Many(b) => guarded(b, id),
        STy::Union(ms) => ms.iter().all(|m| guarded(m, id)),
        _ => true,
    }
}

/// A form's name, or `#%fx`: never bound, so never a binder or a variable.
fn reserved(name: &str) -> bool {
    crate::top::KEYWORDS.contains(&name) || name == "#%fx" || name == "define-syntax"
}

/// A list's car and cdr, the cdr a list of the rest (or the tail).
fn split(s: &Syntax) -> Option<(Syntax, Syntax)> {
    let Datum::List { items, tail } = &s.datum else { return None };
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
fn matches(p: &Syntax, s: &Syntax, binds: &mut HashMap<Sym, Syntax>, interner: &Interner) -> bool {
    match &p.datum {
        Datum::Symbol(n) if interner.name(*n) == "_" => true,
        Datum::Symbol(n) if reserved(interner.name(*n)) => s.as_symbol() == Some(*n),
        Datum::Symbol(n) => {
            binds.insert(*n, s.clone());
            true
        }
        Datum::Nil => matches!(s.datum, Datum::Nil),
        Datum::List { .. } => match (split(p), split(s)) {
            (Some((pa, pd)), Some((sa, sd))) => matches(&pa, &sa, binds, interner) && matches(&pd, &sd, binds, interner),
            _ => false,
        },
        other => &s.datum == other,
    }
}
