//! Binding shapes (`docs/research/binding-shapes.md`, step 2): what a
//! module gives, by namespace, read from a program's syntax after its
//! expansion and before its types are known, so that what `with`,
//! `extend` and `include` bind is known where they are. Each such form has
//! its module's shape written into it, `(with m #:relied ((x …) (t …)) body
//! …)`, which the checkers hold to the module's type there: a shape is a
//! promise the checkers keep, never a guess the expander makes alone.
//!
//! Where a module's shape comes from (the design note's table): a
//! variable's, from what binds it (a `define` or `let` of a module
//! expression, or a binder whose type is written); a `module`'s, its items'
//! names; a file's, its items' (a function's that makes them, if it takes
//! module parameters); a `the`'s, its type's; a `moduleof`'s, its members';
//! a function's result's, its body's or its type's.

use super::{Aligner, Atom, Kids, Level, Macros, Mode, Ns, STy};
use crate::error::{FxError, R};
use fixpt_read::{Datum, Interner, Span, Sym, Syntax};
use std::collections::HashMap;
use std::rc::Rc;

/// What a module gives, as expansion needs it: its values' names, each
/// with its own shape if it is known and is a module's (or a function's
/// that makes one); its descriptions' names (types, effects, functions of
/// descriptions, which share one scope). Or a function's that makes a
/// module of a shape: a functor, a file of module parameters.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Shape {
    Module { vals: Vec<(Sym, Option<Rc<Shape>>)>, descs: Vec<(Sym, Option<Rc<Shape>>)> },
    /// A function's: the shapes of its parameters and of its result, each
    /// where it is known, so that a shape in any position a value reaches
    /// a binder from is (a callback's parameter, `(-> ((-> (S) X)) Y)`).
    Fun { params: Vec<Option<Rc<Shape>>>, result: Option<Rc<Shape>> },
}

impl Shape {
    /// Its names, by namespace, as a set.
    fn name_set(&self) -> std::collections::HashSet<(Sym, Ns)> {
        match self {
            Shape::Module { vals, descs } => vals.iter().map(|(n, _)| (*n, Ns::Value)).chain(descs.iter().map(|(n, _)| (*n, Ns::Desc))).collect(),
            Shape::Fun { .. } => Default::default(),
        }
    }

    /// A function's shape, if anything of it is known.
    fn fun(params: Vec<Option<Rc<Shape>>>, result: Option<Rc<Shape>>) -> Option<Rc<Shape>> {
        (result.is_some() || params.iter().any(Option::is_some)).then(|| Rc::new(Shape::Fun { params, result }))
    }

    /// What a function of this shape makes, applied.
    fn result(&self) -> Option<Rc<Shape>> {
        match self {
            Shape::Fun { result, .. } => result.clone(),
            Shape::Module { .. } => None,
        }
    }

    /// Its `k`th parameter's shape, if it is a function's.
    fn param(&self, k: usize) -> Option<Rc<Shape>> {
        match self {
            Shape::Fun { params, .. } => params.get(k).cloned().flatten(),
            Shape::Module { .. } => None,
        }
    }

    /// Name `n`'s own shape, in namespace `ns`, if it gives one: a value
    /// that is a module, a type that is a module's.
    fn member(&self, n: Sym, ns: Ns) -> Option<Rc<Shape>> {
        let Shape::Module { vals, descs } = self else { return None };
        let list = if ns == Ns::Value { vals } else { descs };
        list.iter().find(|(v, _)| *v == n).and_then(|(_, s)| s.clone())
    }
}

/// What a file gives, read before the program that loads it is expanded:
/// the shape of what `load-module` of it makes, and of the module
/// `load-moduleof` of it describes (the same, but for a file of module
/// parameters, whose value is a function of them).
#[derive(Clone, Debug, Default)]
pub(crate) struct FileShape {
    pub(crate) value: Option<Rc<Shape>>,
    pub(crate) module: Option<Rc<Shape>>,
    /// What to write into its forms, by path (`with_written`).
    written: Option<Rc<Written>>,
}

/// The shapes to write into a form, by the path of each form that opens a
/// module: `None` where the module's shape is not known.
type Written = HashMap<Vec<bool>, Option<Syntax>>;

/// What a walk finds (`Macros::walked`).
#[derive(Default)]
struct Walked {
    written: Written,
    shape: Option<Rc<Shape>>,
    defined: Vec<(Sym, Ns, Option<Rc<Shape>>)>,
}

/// A file's forms as one form to walk: its one expression, `input`; or a
/// `module` of them.
fn file_form(forms: &[Syntax], input: bool, interner: &mut Interner) -> Option<Syntax> {
    match forms {
        [one] if input => Some(one.clone()),
        _ if input => None,
        [] => None,
        [first, ..] => {
            let span = first.span;
            Some(Syntax::list(span, std::iter::once(Syntax::symbol(span, interner.intern("module"))).chain(forms.iter().cloned()).collect()))
        }
    }
}

/// The shapes the top level's names have, each as its definition gives it
/// (`None`, a name whose shape is not known), kept from form to form.
#[derive(Clone, Debug, Default)]
pub(crate) struct TopShapes {
    vals: HashMap<Sym, Option<Rc<Shape>>>,
    descs: HashMap<Sym, Option<Rc<Shape>>>,
    /// The form of each description whose shape was not known where it was
    /// defined, to read it again where it is used: types are declared ahead
    /// of the values they may name (`Checker::declare_ahead`).
    desc_forms: HashMap<Sym, Syntax>,
    /// How deep such forms are being read again, so that one that names
    /// itself ends.
    again: std::cell::Cell<usize>,
}

/// The shapes known from form to form: the top level's names', each file's
/// by its key (`load_key`), and the directory a file being read loads from.
#[derive(Clone, Debug, Default)]
pub(crate) struct Known {
    top: TopShapes,
    files: HashMap<String, FileShape>,
    dir: Option<std::path::PathBuf>,
    /// Each file's forms as they were read for its shape, by its path, for
    /// the parser to take rather than read the file again.
    read: HashMap<String, (String, Vec<Syntax>)>,
    /// Each top-level form before and after its shapes were written, if
    /// they are kept (`Checker::keep_shapes_seen`).
    seen: Option<Vec<(String, String)>>,
    /// Each alias an expansion defined at the top level (`(define %~N:x
    /// …)`), a description's if marked: a name of its own wherever later
    /// forms name it (`Macros::aliases_resolved`).
    pub(crate) aliases_defined: std::collections::HashSet<(Sym, bool)>,
    /// The shapes named by `define-syntax` (`(define-syntax s (modnames …))`,
    /// `binding-shapes.md`), each its `modnames` form, by its name.
    named: HashMap<Sym, Syntax>,
}

/// Where a binder's value comes from, for its shape: the expression it is
/// bound to, the type it is declared to have, or (a description's binder)
/// the description it is defined as.
enum Source {
    Value(usize),
    Typed(usize),
    /// A name an `import` takes from the module at a node.
    Member(usize, Sym),
    /// The `k`th parameter of the procedure type of a name, which the
    /// checker knows and no form the walk reads defines.
    Param(Sym, usize),
    /// Parameter `i` of the function given as argument `k` to the operator
    /// at a node.
    ArgParam(usize, usize, usize),
}

/// A module's names as they are gathered, a later one of a name in its
/// place.
#[derive(Default)]
struct Members {
    vals: Vec<(Sym, Option<Rc<Shape>>)>,
    descs: Vec<(Sym, Option<Rc<Shape>>)>,
}

impl Members {
    fn add(&mut self, n: Sym, ns: Ns, s: Option<Rc<Shape>>) {
        let list = if ns == Ns::Value { &mut self.vals } else { &mut self.descs };
        list.retain(|(m, _)| *m != n);
        list.push((n, s));
    }
}

/// The shape a top-level value's type says it has, where the checker has
/// checked it: for a value whose definition the walk did not read.
///
/// Asked of a name in a namespace: a value's; a type's; or, given `k`, the
/// `k`th parameter's of the procedure type of that name.
pub(crate) type Global<'a> = Option<&'a dyn Fn(Sym, Ns, Option<usize>) -> Option<Rc<Shape>>>;

/// What a module was asked, by name and namespace, and its answers: what
/// the form that opens it relies on. `unknown` if its shape was not known
/// where a reference asked.
#[derive(Clone, Debug, Default)]
struct Asked {
    vals: Vec<(Sym, bool)>,
    descs: Vec<(Sym, bool)>,
    unknown: bool,
}

impl Asked {
    fn note(&mut self, n: Sym, ns: Ns, given: bool) {
        let list = if ns == Ns::Value { &mut self.vals } else { &mut self.descs };
        if !list.iter().any(|(m, _)| *m == n) {
            list.push((n, given));
        }
    }

    /// As written into a form (`#:relied`, `ast::Relied`): `((value …)
    /// (description …))`, the names asked of the module that it gives.
    /// What it was asked and does not give, the checkers find for
    /// themselves (each reference whose name the module's type gives, held
    /// to this list).
    fn written(&self, span: Span) -> Syntax {
        let given = |l: &[(Sym, bool)]| Syntax::list(span, l.iter().filter(|(_, g)| *g).map(|(n, _)| Syntax::symbol(span, *n)).collect());
        Syntax::list(span, vec![given(&self.vals), given(&self.descs)])
    }
}

/// A table made with a cheap hash, of the walk's own keys.
type Fast<K, V> = HashMap<K, V, std::hash::BuildHasherDefault<crate::ast::IdHasher>>;

/// A run of an environment's levels, as a reference is looked up: ribs,
/// one table of their binders by name and namespace; or a module's names
/// (`Level::Shape`), with whether it is an `include`'s.
enum Segment {
    Ribs(Fast<(Sym, Ns), usize>),
    Shape(usize, bool),
}

/// What a name referred to is bound by: a binder, the module a `with` (or
/// `extend` or `include`) opens around it, or nothing here.
enum Res {
    Binder(usize),
    Member(usize, Sym, Ns),
    Free(Sym, Ns),
    /// Past a module whose shape is not known: what it is cannot be said.
    Unknown,
}

/// The key a load of `path` is known by, read from directory `dir`: the
/// path resolved, as the checkers' `parse_load` makes it, `input:` before
/// it for a `load-input` file.
pub(crate) fn load_key(dir: Option<&std::path::Path>, path: &str, input: bool) -> (std::path::PathBuf, String) {
    let at = match dir {
        Some(d) if std::path::Path::new(path).is_relative() && crate::built_in_module(path).is_none() => d.join(path),
        _ => std::path::PathBuf::from(path),
    };
    let key = format!("{}{}", if input { "input:" } else { "" }, at.display());
    (at, key)
}

/// The paths each `load-module`, `load-input`, `load-moduleof` and
/// `load-input-moduleof` in `s` names, with whether it is an input's.
pub(crate) fn loads_in(s: &Syntax, interner: &Interner, out: &mut Vec<(String, bool)>) {
    let mut work = vec![s];
    while let Some(s) = work.pop() {
        let Datum::List { items, tail } = &s.datum else { continue };
        if let [h, p, ..] = &items[..]
            && let (Some(h), Datum::Str(p)) = (h.as_symbol(), &p.datum)
            && let Some(input) = match interner.name(h) {
                "load-module" | "load-moduleof" => Some(false),
                "load-input" | "load-input-moduleof" => Some(true),
                _ => None,
            }
        {
            out.push((p.clone(), input));
        }
        work.extend(items.iter().chain(tail.as_deref()));
    }
}

/// `s` without the shapes written into it (`#:relied …`), as it was
/// expanded: what a program's walk reads.
pub(crate) fn unshaped(s: &Syntax, interner: &Interner) -> Syntax {
    let Datum::List { items, tail } = &s.datum else { return s.clone() };
    let mut out = Vec::with_capacity(items.len());
    let mut k = 0;
    while k < items.len() {
        if matches!(&items[k].datum, Datum::Keyword(w) if interner.name(*w) == "relied") && k == 2 {
            k += 2;
            continue;
        }
        out.push(unshaped(&items[k], interner));
        k += 1;
    }
    Syntax::new(s.span, Datum::List { items: out, tail: tail.as_ref().map(|t| Box::new(unshaped(t, interner))) })
}

/// The forms that bind what the module at their first operand gives.
fn opens(head: &str) -> bool {
    matches!(head, "with" | "extend" | "include" | "import-with-syntax")
}

/// One walk's shapes: its aligned nodes, the environments the walk found
/// each name in, and what is known already (the top level's, files').
struct Shaper<'a, 'm> {
    a: &'a Aligner<'m>,
    top: &'a TopShapes,
    files: &'a HashMap<String, FileShape>,
    dir: Option<&'a std::path::Path>,
    /// A top-level value's shape as its checked type says (`Global`).
    global: Global<'a>,
    /// Each node's parent: the node of the list or form it is a part of.
    parent: Vec<Option<usize>>,
    envs: HashMap<usize, &'a super::Env>,
    /// What each module, by the node of its expression, was asked by the
    /// references that reached it (`resolve`): what is written into the
    /// form that opens it, and all it is held to.
    asked: HashMap<usize, Asked>,
    /// Each part of an environment as segments (`Segment`), made once a
    /// reference is looked up in it.
    segments: Fast<*const Vec<Level>, Rc<Vec<Segment>>>,
    /// Whether each node is in the module an `include` includes, which is
    /// not in the scope of what any `include` gives.
    in_included: Vec<bool>,
    /// Each shape's names by namespace, made once a shape is asked.
    names: HashMap<*const Shape, std::collections::HashSet<(Sym, Ns)>>,
    /// Each node's shape as an expression (`false`) and as a type (`true`),
    /// once found; `None` while it is being found, so that a cycle finds
    /// none.
    memo: HashMap<(usize, bool), Option<Rc<Shape>>>,
}

impl<'a, 'm> Shaper<'a, 'm> {
    fn new(a: &'a Aligner<'m>, found: &'a super::Found, top: &'a TopShapes, files: &'a HashMap<String, FileShape>, dir: Option<&'a std::path::Path>, global: Global<'a>) -> Self {
        let mut parent = vec![None; a.nodes.len()];
        for (k, n) in a.nodes.iter().enumerate() {
            match &n.kids {
                Kids::Pair(x, y) => (parent[*x], parent[*y]) = (Some(k), Some(k)),
                Kids::Form(x) | Kids::Seq(x, _) => parent[*x] = Some(k),
                Kids::Desc(xs) => xs.iter().for_each(|x| parent[*x] = Some(k)),
                _ => {}
            }
        }
        let envs = found.iter().map(|(at, env, _, _)| (*at, env)).collect();
        let mut c = Shaper { a, top, files, dir, global, parent, envs, asked: HashMap::new(), segments: Fast::default(), in_included: Vec::new(), names: HashMap::new(), memo: HashMap::new() };
        c.in_included = c.included_nodes();
        c
    }

    fn name(&self, n: Sym) -> &'m str {
        let i: &'m Interner = self.a.interner;
        i.name(n)
    }

    fn head(&self, s: &Syntax) -> Option<&'m str> {
        s.as_proper_list()?.first()?.as_symbol().map(|h| self.name(h))
    }

    /// What the checker's types say of `n` (`Global`), without its own
    /// names.
    fn global_of(&self, n: Sym, ns: Ns, k: Option<usize>) -> Option<Rc<Shape>> {
        self.global.and_then(|g| g(n, ns, k)).map(|s| self.own(&s))
    }

    /// Shape `s` without the checkers' own names (`%…`), which no program
    /// reads, as a type has them.
    fn own(&self, s: &Rc<Shape>) -> Rc<Shape> {
        match &**s {
            Shape::Fun { params, result } => Rc::new(Shape::Fun {
                params: params.iter().map(|p| p.as_ref().map(|p| self.own(p))).collect(),
                result: result.as_ref().map(|r| self.own(r)),
            }),
            Shape::Module { vals, descs } => {
                let mine = |n: &Sym| !self.name(*n).starts_with('%');
                Rc::new(Shape::Module {
                    vals: vals.iter().filter(|(n, _)| mine(n)).map(|(n, x)| (*n, x.as_ref().map(|x| self.own(x)))).collect(),
                    descs: descs.iter().filter(|(n, _)| mine(n)).cloned().collect(),
                })
            }
        }
    }

    /// The `k`th element of node `at`'s list.
    fn elem(&self, at: usize, k: usize) -> Option<usize> {
        self.elems(at).get(k).copied().flatten()
    }

    /// The nodes of node `at`'s list's elements, by position (`None` where
    /// no node is, as for a form's head).
    fn elems(&self, at: usize) -> Vec<Option<usize>> {
        let nodes = &self.a.nodes;
        let cars = |mut x: usize| {
            let mut out = Vec::new();
            while let Kids::Pair(a, d) = nodes[x].kids {
                out.push(Some(a));
                x = d;
            }
            out
        };
        match &nodes[at].kids {
            // An application's list is its own; a form's, its operands'.
            Kids::Form(x) if nodes[*x].path.len() == nodes[at].path.len() => cars(*x),
            Kids::Form(x) => std::iter::once(None).chain(cars(*x)).collect(),
            Kids::Pair(..) => cars(at),
            Kids::Desc(xs) => xs.iter().map(|x| Some(*x)).collect(),
            _ => Vec::new(),
        }
    }

    /// The list node `b` is an element of, and its place there.
    fn position(&self, b: usize) -> Option<(usize, usize)> {
        let nodes = &self.a.nodes;
        let p = self.parent[b]?;
        match &nodes[p].kids {
            Kids::Pair(a, _) if *a == b => {}
            Kids::Desc(xs) => return Some((p, xs.iter().position(|x| *x == b)?)),
            _ => return None,
        }
        let (mut top, mut i) = (p, 0);
        while let Some(q) = self.parent[top]
            && matches!(nodes[q].kids, Kids::Pair(_, d) if d == top)
        {
            (top, i) = (q, i + 1);
        }
        match self.parent[top] {
            Some(f) if matches!(nodes[f].kids, Kids::Form(x) if x == top) => Some((f, if nodes[top].path.len() == nodes[f].path.len() { i } else { i + 1 })),
            _ => Some((top, i)),
        }
    }

    /// What reference `at`, of `n` in namespace `ns`, is bound by.
    fn resolve(&mut self, at: usize, n: Sym, ns: Ns) -> Res {
        let Some(env) = self.envs.get(&at).copied() else { return Res::Free(n, ns) };
        for chunk in env.0.iter().rev() {
            let segments = self.segments_of(chunk);
            for seg in segments.iter() {
                match seg {
                    Segment::Ribs(index) => {
                        if let Some(b) = index.get(&(n, ns)) {
                            return Res::Binder(*b);
                        }
                    }
                    // A module's own expression is not in the scope of what
                    // it gives; nor is an `include`'s of what any includes,
                    // as the checkers make the modules included before the
                    // items.
                    Segment::Shape(m, _) if self.a.nodes[at].path.starts_with(&self.a.nodes[*m].path) => {}
                    Segment::Shape(_, true) if self.in_included[at] => {}
                    // What the module gives: asked, and the answer kept, as
                    // what the form that opens it relies on.
                    Segment::Shape(m, _) => match self.exp(*m) {
                        Some(s) => {
                            let given = self.names.entry(Rc::as_ptr(&s)).or_insert_with(|| s.name_set()).contains(&(n, ns));
                            self.asked.entry(*m).or_default().note(n, ns, given);
                            if given {
                                return Res::Member(*m, n, ns);
                            }
                        }
                        None => {
                            self.asked.entry(*m).or_default().unknown = true;
                            return Res::Unknown;
                        }
                    },
                }
            }
        }
        Res::Free(n, ns)
    }

    /// Part `chunk` of an environment as segments, innermost first: each
    /// run of ribs one table, the innermost binder of a name its entry (a
    /// module's items bind a rib each); each module's names on its own.
    fn segments_of(&mut self, chunk: &Rc<Vec<Level>>) -> Rc<Vec<Segment>> {
        if let Some(s) = self.segments.get(&Rc::as_ptr(chunk)) {
            return s.clone();
        }
        // A part's own binders before the modules it opens: a module's
        // items before what its `include`s give, as the checkers read them.
        let nodes = &self.a.nodes;
        let mut ribs: Fast<(Sym, Ns), usize> = Fast::default();
        let mut shapes = Vec::new();
        for level in chunk.iter() {
            match level {
                Level::Rib(atoms) | Level::Earlier(atoms) => {
                    for x in atoms.iter() {
                        if let Atom::Lit(b, m) = x
                            && let Kids::Binder(k, _) = nodes[*b].kids
                        {
                            ribs.entry((k, *m)).or_insert(*b);
                        }
                    }
                }
                Level::Shape(m) => shapes.push(Segment::Shape(*m, self.included(*m))),
                Level::Cage(_) => {}
            }
        }
        let mut out = vec![Segment::Ribs(ribs)];
        out.extend(shapes);
        let out = Rc::new(out);
        self.segments.insert(Rc::as_ptr(chunk), out.clone());
        out
    }

    /// Each node, whether it is in a module an `include` includes.
    fn included_nodes(&self) -> Vec<bool> {
        let nodes = &self.a.nodes;
        let mut marked = vec![false; nodes.len()];
        let mut work = Vec::new();
        for (k, node) in nodes.iter().enumerate() {
            if matches!(node.kids, Kids::Form(_)) && self.head(&node.syn) == Some("include")
                && let Some(m) = self.elem(k, 1)
            {
                work.push(m);
            }
        }
        while let Some(x) = work.pop() {
            if std::mem::replace(&mut marked[x], true) {
                continue;
            }
            match &nodes[x].kids {
                Kids::Pair(a, d) => work.extend([*a, *d]),
                Kids::Form(y) | Kids::Seq(y, _) => work.push(*y),
                Kids::Desc(ys) => work.extend(ys.iter().copied()),
                _ => {}
            }
        }
        marked
    }

    /// Whether node `m` is the module an `include` includes.
    fn included(&self, m: usize) -> bool {
        self.position(m).is_some_and(|(f, i)| i == 1 && self.head(&self.a.nodes[f].syn) == Some("include"))
    }

    /// Top-level description `n`'s shape, its form read again now that
    /// what it names may be known.
    fn desc_again(&self, n: Sym) -> Option<Rc<Shape>> {
        let form = self.top.desc_forms.get(&n)?;
        if self.top.again.get() > 4 {
            return None;
        }
        self.top.again.set(self.top.again.get() + 1);
        let walked = self.a.m.walked(form, true, self.global, self.a.interner);
        self.top.again.set(self.top.again.get() - 1);
        walked.ok()?.defined.into_iter().find(|(m, ns, _)| *m == n && *ns == Ns::Desc).and_then(|(_, _, s)| s)
    }

    /// Where binder `b`'s value comes from: the binding form it is in, by
    /// its place there.
    fn source(&self, b: usize) -> Option<Source> {
        let (q, i) = self.position(b)?;
        // A lambda's parameter of no type of its own: the procedure type
        // the lambda is declared at says it.
        if let Some((f, 1)) = self.position(q)
            && self.head(&self.a.nodes[f].syn) == Some("lambda")
        {
            return self.declared_param(f, i).or_else(|| self.argument_param(f, i));
        }
        // A description function's name, `(define-type (f (a kind) …) T)`:
        // `T`, whatever it is given.
        if let (0, Some((d, 1))) = (i, self.position(q))
            && self.head(&self.a.nodes[d].syn) == Some("define-type")
        {
            return Some(Source::Typed(self.elem(d, 2)?));
        }
        let list = &self.a.nodes[q].syn;
        let items = list.as_proper_list()?;
        match (self.head(list), i, items.len()) {
            (Some("define"), 1, 3) => Some(Source::Value(self.elem(q, 2)?)),
            (Some("define" | "define*"), 1, 4) => Some(Source::Typed(self.elem(q, 2)?)),
            (Some("define-type"), 1, 3) => Some(Source::Typed(self.elem(q, 2)?)),
            (Some("import"), 2.., _) => match self.a.nodes[b].kids {
                Kids::Binder(n, Ns::Value) => Some(Source::Member(self.elem(q, 1)?, n)),
                _ => None,
            },
            // An element of a list of bindings, `(x e)`, `(x T)`, `(x T e)`:
            // which, by the form whose operand the list is.
            (_, 0, 2..=3) => {
                let (r, _) = self.position(q)?;
                let (f, k) = self.position(r)?;
                let form = &self.a.nodes[f].syn;
                let second = self.elem(q, 1)?;
                match (self.head(form), k) {
                    (Some("let" | "let*" | "par"), 1) => Some(Source::Value(second)),
                    (Some("letrec" | "lambda" | "module-parameters"), 1) | (Some("rlambda"), 2) => Some(Source::Typed(second)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The type node of parameter `k` of lambda `f`, as the type the
    /// lambda is declared at writes it: a typed `define`'s or a `the`'s,
    /// through `plambda`s, in a `subr` or `->` under `poly`s.
    /// Parameter `i` of lambda `f` given as an argument of an application:
    /// the parameter's shape the operator's shape says its argument's
    /// function is given (a positive place of the operator's type).
    fn argument_param(&self, f: usize, i: usize) -> Option<Source> {
        let (app, j) = self.position(f)?;
        let op = self.operator(app)?;
        (j >= 1).then_some(Source::ArgParam(op, j - 1, i))
    }

    fn declared_param(&self, f: usize, k: usize) -> Option<Source> {
        let mut at = f;
        let t = loop {
            let (p, i) = self.position(at)?;
            match (self.head(&self.a.nodes[p].syn), i) {
                (Some("plambda"), 2) => at = p,
                (Some("define" | "define*"), 3) => break self.elem(p, 2)?,
                (Some("the"), 2) => break self.elem(p, 1)?,
                _ => return None,
            }
        };
        let mut t = t;
        loop {
            let syn = &self.a.nodes[t].syn;
            // A procedure type by its name: its parameter, as the checker
            // has the type.
            if let Some(n) = syn.as_symbol() {
                return Some(Source::Param(n, k));
            }
            let items = syn.as_proper_list()?;
            let params = match self.head(syn)? {
                // Each member a type of the procedure: its first's says,
                // and the checker holds the others to the shape.
                "allof" => {
                    t = self.elem(t, 1)?;
                    continue;
                }
                "poly" => {
                    t = self.elem(t, items.len() - 1)?;
                    continue;
                }
                "->" => self.elem(t, 1)?,
                "subr" => self.elem(t, if items.get(1).is_some_and(|c| self.head(c) == Some("conv")) { 3 } else { 2 })?,
                _ => return None,
            };
            let p = self.elem(params, k)?;
            // A dependent parameter, `(c : T)`: its type.
            return match self.a.nodes[p].syn.as_proper_list() {
                Some([_, c, _]) if c.as_symbol().is_some_and(|c| self.name(c) == ":") => self.elem(p, 2).map(Source::Typed),
                _ => Some(Source::Typed(p)),
            };
        }
    }

    fn binder(&mut self, b: usize) -> Option<Rc<Shape>> {
        match self.source(b)? {
            Source::Value(e) => self.exp(e),
            Source::Typed(t) => self.ty(t),
            Source::Member(m, n) => self.exp(m)?.member(n, Ns::Value),
            Source::Param(n, k) => self.global_of(n, Ns::Desc, Some(k)),
            Source::ArgParam(op, k, i) => self.exp(op)?.param(k)?.param(i),
        }
    }

    /// The shape of what a reference, at `at`, of `n` refers to.
    fn reference(&mut self, at: usize, n: Sym, ns: Ns) -> Option<Rc<Shape>> {
        match self.resolve(at, n, ns) {
            Res::Binder(b) => self.binder(b),
            Res::Member(m, n, ns) => self.exp(m)?.member(n, ns),
            // A top-level name: as its definition's walk found it, or as
            // the checker found its type, which a definition read from a
            // fasl, or a file's hidden global, has alone.
            Res::Free(n, Ns::Value) => self.top.vals.get(&n).cloned().flatten().or_else(|| self.global_of(n, Ns::Value, None)),
            Res::Free(n, Ns::Desc) => match self.top.descs.get(&n).cloned().flatten() {
                Some(s) => Some(s),
                None => self.desc_again(n).or_else(|| self.global_of(n, Ns::Desc, None)),
            },
            Res::Unknown => None,
        }
    }

    /// The shape of expression node `at`, if it makes a module (or a
    /// function that makes one) whose shape is known.
    fn exp(&mut self, at: usize) -> Option<Rc<Shape>> {
        self.memoized(at, false, |c| c.exp_found(at))
    }

    fn ty(&mut self, at: usize) -> Option<Rc<Shape>> {
        self.memoized(at, true, |c| c.ty_found(at))
    }

    fn memoized(&mut self, at: usize, ty: bool, find: impl FnOnce(&mut Self) -> Option<Rc<Shape>>) -> Option<Rc<Shape>> {
        if let Some(s) = self.memo.get(&(at, ty)) {
            return s.clone();
        }
        self.memo.insert((at, ty), None);
        let s = find(self);
        self.memo.insert((at, ty), s.clone());
        s
    }

    fn exp_found(&mut self, at: usize) -> Option<Rc<Shape>> {
        let a = self.a;
        let node = &a.nodes[at];
        match node.kids {
            Kids::Ref(n, ns, _) => return self.reference(at, n, ns),
            Kids::Binder(..) => return self.binder(at),
            _ => {}
        }
        let syn = &node.syn;
        let items = syn.as_proper_list()?;
        let e = self.elems(at);
        let last = e.last().copied().flatten().filter(|_| items.len() > 1);
        match self.head(syn) {
            Some("module") => self.module(&e[1..]),
            Some(h @ ("load-module" | "load-input")) => {
                let Datum::Str(p) = &items.get(1)?.datum else { return None };
                let (_, key) = load_key(self.dir, p, h == "load-input");
                self.files.get(&key)?.value.clone()
            }
            Some("the") => self.ty(e.get(1).copied().flatten()?),
            Some("extend") => {
                let (Shape::Module { vals: v0, descs: d0 }, Shape::Module { vals: v1, descs: d1 }) =
                    (&*self.exp(e.get(1).copied().flatten()?)?, &*self.exp(e.last().copied().flatten()?)?)
                else {
                    return None;
                };
                let mut vals: Vec<_> = v0.iter().filter(|(n, _)| !v1.iter().any(|(m, _)| m == n)).cloned().collect();
                vals.extend(v1.iter().cloned());
                let mut descs: Vec<_> = d0.iter().filter(|(n, _)| !d1.iter().any(|(m, _)| m == n)).cloned().collect();
                descs.extend(d1.iter().cloned());
                Some(Rc::new(Shape::Module { vals, descs }))
            }
            // `(with #%toplevel name)`: the top level's.
            Some("with") if items.len() == 3 && items[1].as_symbol().is_some_and(|m| self.name(m) == "#%toplevel") => {
                self.top.vals.get(&items[2].as_symbol()?).cloned().flatten()
            }
            Some("with" | "let" | "let*" | "letrec" | "begin" | "letregion" | "letfreeze" | "letrena" | "letreap" | "plambda" | "dlambda") => self.exp(last?),
            Some("proj") => self.exp(e.get(1).copied().flatten()?),
            Some("if") if items.len() == 4 => {
                let (a, b) = (self.exp(e[2]?)?, self.exp(e[3]?)?);
                (a == b).then_some(a)
            }
            Some(h @ ("lambda" | "rlambda")) => {
                let formals = e.get(if h == "lambda" { 1 } else { 2 }).copied().flatten();
                let params = formals.map(|f| self.formals(f)).unwrap_or_default();
                let result = last.and_then(|x| self.exp(x));
                Shape::fun(params, result)
            }
            // An application: its operator's result.
            _ => self.exp(self.operator(at)?)?.result(),
        }
    }

    /// The shapes of a procedure type's parameters, node `ps` their list,
    /// each a type or a dependent `(c : T)`.
    fn param_types(&mut self, ps: usize) -> Vec<Option<Rc<Shape>>> {
        let a = self.a;
        let mut out = Vec::new();
        for p in self.elems(ps) {
            let t = p.and_then(|p| match a.nodes[p].syn.as_proper_list() {
                Some([_, c, _]) if c.as_symbol().is_some_and(|c| self.name(c) == ":") => self.elem(p, 2),
                _ => Some(p),
            });
            out.push(t.and_then(|t| self.ty(t)));
        }
        out
    }

    /// The shapes of a lambda's parameters, node `f` its formals: a typed
    /// one's type's, an untyped one's as its binder has it.
    fn formals(&mut self, f: usize) -> Vec<Option<Rc<Shape>>> {
        let a = self.a;
        let mut out = Vec::new();
        for p in self.elems(f) {
            out.push(p.and_then(|p| match a.nodes[p].kids {
                Kids::Binder(..) => self.binder(p),
                _ => self.elem(p, 1).and_then(|t| self.ty(t)),
            }));
        }
        out
    }

    /// The node of application `at`'s operator.
    fn operator(&self, at: usize) -> Option<usize> {
        let Kids::Form(x) = self.a.nodes[at].kids else { return None };
        match self.a.nodes[x].kids {
            Kids::Pair(f, _) if self.a.nodes[x].path == self.a.nodes[at].path => Some(f),
            _ => None,
        }
    }

    /// The shape of the module whose items are the nodes `items`: the names
    /// each exports, but a `hide`'s and a `module-parameters`'.
    fn module(&mut self, items: &[Option<usize>]) -> Option<Rc<Shape>> {
        let (mut given, mut hidden) = (Members::default(), Members::default());
        let a = self.a;
        for x in items {
            let x = (*x)?;
            let head = self.head(&a.nodes[x].syn);
            if head == Some("module-parameters") {
                continue;
            }
            let Kids::Form(f) = a.nodes[x].kids else { continue };
            let Some((b, r)) = &a.nodes[f].export else { continue };
            let levels = a.eval(b, *r, a.nodes[x].syn.span).ok()?;
            let mut got = Members::default();
            for level in levels {
                match level {
                    Level::Rib(atoms) | Level::Earlier(atoms) => {
                        for atom in atoms.iter().cloned() {
                            let Atom::Lit(b, ns) = atom else { continue };
                            let Kids::Binder(n, _) = a.nodes[b].kids else { continue };
                            let s = self.binder(b);
                            got.add(n, ns, s);
                        }
                    }
                    Level::Shape(m) => {
                        let Shape::Module { vals, descs } = &*self.exp(m)? else { return None };
                        for (n, s) in vals {
                            got.add(*n, Ns::Value, s.clone());
                        }
                        for (n, s) in descs {
                            got.add(*n, Ns::Desc, s.clone());
                        }
                    }
                    Level::Cage(_) => return None,
                }
            }
            // What a `hide` holds is no name the module gives, nor is any
            // name it gives, though the module define it too (as the
            // checkers' `hiding` leaves out each name marked).
            let into = if head == Some("hide") { &mut hidden } else { &mut given };
            for (n, s) in got.vals {
                into.add(n, Ns::Value, s);
            }
            for (n, s) in got.descs {
                into.add(n, Ns::Desc, s);
            }
        }
        given.vals.retain(|(n, _)| !hidden.vals.iter().any(|(m, _)| m == n));
        given.descs.retain(|(n, _)| !hidden.descs.iter().any(|(m, _)| m == n));
        Some(Rc::new(Shape::Module { vals: given.vals, descs: given.descs }))
    }

    /// The shape of `(modnames member …)`, its members `members`: each
    /// value's name (`x`, `(val x)`), a module's with its own shape
    /// (`(modnames m member …)`), each description's (`(abs t)`, `(desc u)`,
    /// `(eff e)`).
    fn modnames_shape(&self, members: &[Syntax]) -> Option<Rc<Shape>> {
        let (mut vals, mut descs) = (Vec::new(), Vec::new());
        for m in members {
            if let Some(n) = m.as_symbol() {
                vals.push((n, None));
                continue;
            }
            let [w, n, rest @ ..] = m.as_proper_list()? else { return None };
            let n = n.as_symbol()?;
            match self.name(w.as_symbol()?) {
                "val" => vals.push((n, None)),
                "modnames" => vals.push((n, self.modnames_shape(rest))),
                "abs" | "desc" | "eff" => descs.push((n, None)),
                _ => return None,
            }
        }
        Some(Rc::new(Shape::Module { vals, descs }))
    }

    fn ty_found(&mut self, at: usize) -> Option<Rc<Shape>> {
        let a = self.a;
        let node = &a.nodes[at];
        if let Kids::Ref(n, Ns::Desc, _) = node.kids {
            return self.reference(at, n, Ns::Desc);
        }
        // A template's free description name, the top level's, qualified.
        if let Some(n) = node.syn.as_symbol()
            && let Some(x) = self.name(n).strip_prefix("#%toplevel:")
        {
            let x = self.a.interner.get(x)?;
            return self.top.descs.get(&x).cloned().flatten().or_else(|| self.desc_again(x));
        }
        let syn = &node.syn;
        let items = syn.as_proper_list()?;
        let e = self.elems(at);
        match self.head(syn)? {
            // A shape written (`binding-shapes.md`): the names it gives.
            "modnames" => self.modnames_shape(&items[1..]),
            "moduleof" => {
                let (mut vals, mut descs) = (Vec::new(), Vec::new());
                for (k, m) in items.iter().enumerate().skip(1) {
                    let parts = m.as_proper_list()?;
                    let word = parts.first()?.as_symbol().map(|w| self.name(w))?;
                    let names: Vec<Sym> = match (parts.get(1)?.as_symbol(), parts.get(1)?.as_proper_list()) {
                        (Some(n), _) => vec![n],
                        (None, Some(ns)) if word == "abs" => ns.iter().filter_map(|n| n.as_symbol()).take(if ns.iter().all(|n| n.as_symbol().is_some()) { usize::MAX } else { 1 }).collect(),
                        (None, Some(ns)) => vec![ns.first()?.as_symbol()?],
                        _ => return None,
                    };
                    match word {
                        "val" => {
                            let t = e[k].and_then(|x| self.elem(x, 2));
                            let s = t.and_then(|t| self.ty(t));
                            vals.push((names[0], s));
                        }
                        "abs" => descs.extend(names.into_iter().map(|n| (n, None))),
                        "desc" => {
                            let t = e[k].and_then(|x| self.elem(x, 2));
                            let s = t.and_then(|t| self.ty(t));
                            descs.push((names[0], s));
                        }
                        _ => return None,
                    }
                }
                Some(Rc::new(Shape::Module { vals, descs }))
            }
            h @ ("load-moduleof" | "load-input-moduleof") => {
                let Datum::Str(p) = &items.get(1)?.datum else { return None };
                let (_, key) = load_key(self.dir, p, h == "load-input-moduleof");
                self.files.get(&key)?.module.clone()
            }
            "restrict" => {
                let Shape::Module { vals, descs } = &*self.ty(e.get(1).copied().flatten()?)? else { return None };
                let kept: Vec<Sym> = items[2..].iter().filter_map(|n| n.as_symbol()).collect();
                Some(Rc::new(Shape::Module {
                    vals: vals.iter().filter(|(n, _)| kept.contains(n)).cloned().collect(),
                    descs: descs.iter().filter(|(n, _)| kept.contains(n)).cloned().collect(),
                }))
            }
            "poly" => self.ty(e.last().copied().flatten()?),
            // A type a module gives: its own shape, if it is a module's.
            "select" if items.len() == 3 => {
                let n = items[2].as_symbol()?;
                self.exp(e[1]?)?.member(n, Ns::Desc)
            }
            "->" if items.len() == 3 => {
                let params = self.param_types(e[1]?);
                Shape::fun(params, self.ty(e[2]?))
            }
            "subr" => {
                let conv = items.get(1).is_some_and(|c| self.head(c) == Some("conv"));
                let k = if conv { 4 } else { 3 };
                let params = self.param_types(e.get(k - 1).copied().flatten()?);
                Shape::fun(params, self.ty(e.get(k).copied().flatten()?))
            }
            // A description function applied: what it makes, whatever it is
            // given.
            _ => match e.first().copied().flatten().map(|h| &a.nodes[h].kids) {
                Some(Kids::Ref(_, Ns::Desc, _)) => self.ty(e[0]?),
                _ => None,
            },
        }
    }
}

impl Macros {
    /// Form `form`, a program's after expansion (a top-level form, or, a
    /// file's items, a `module` of them, `module`): each `with`, `extend`
    /// and `include` in it with its module's shape written in, `#:shape
    /// ((value …) (description …))`, or `#:relied #f` where the shape is not
    /// known (`binding-shapes.md`, step 2); and, at the top level, what its
    /// definitions bind kept for the forms after it.
    pub(crate) fn shaped(&mut self, form: &Syntax, top: bool, dir: Option<std::path::PathBuf>, global: Global, interner: &Interner) -> R<Syntax> {
        let outer = std::mem::replace(&mut self.withs.shapes.dir, dir);
        let r = self.shaped_from(form, top, global, interner);
        self.withs.shapes.dir = outer;
        r
    }

    fn shaped_from(&mut self, form: &Syntax, top: bool, global: Global, interner: &Interner) -> R<Syntax> {
        let form = unshaped(form, interner);
        let walked = self.walked(&form, top, global, interner)?;
        for (n, ns, s) in walked.defined {
            let top = &mut self.withs.shapes.top;
            match ns {
                Ns::Value => {
                    top.vals.insert(n, s);
                }
                Ns::Desc if s.is_none() => {
                    top.descs.insert(n, None);
                    top.desc_forms.insert(n, form.clone());
                }
                Ns::Desc => {
                    top.descs.insert(n, s);
                    top.desc_forms.remove(&n);
                }
            }
        }
        Ok(with_written(&form, &mut Vec::new(), &walked.written, interner))
    }

    /// Form `form`, walked: the shapes to write into it, by the path of
    /// each form that opens a module; its own shape, as an expression's;
    /// and, `top`, what its definitions bind, with their shapes.
    fn walked(&self, form: &Syntax, top: bool, global: Global, interner: &Interner) -> R<Walked> {
        let none = HashMap::new();
        let mut out = Walked::default();
        let mut a = Aligner { m: self, interner, mode: Mode::Program, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new() };
        let t = Rc::new(if top { STy::Item } else { STy::Expr });
        let root = a.align(&t, form, None, Vec::new())?;
        let mut found = Vec::new();
        a.walk(root, &super::Env::default(), false, 0, &mut found, &mut Vec::new())?;
        let empty = TopShapes::default();
        let tops = if top { &self.withs.shapes.top } else { &empty };
        let mut c = Shaper::new(&a, &found, tops, &self.withs.shapes.files, self.withs.shapes.dir.as_deref(), global.filter(|_| top));
        // Every reference that reaches a module's names asks the module.
        for (at, env, _, _) in &found {
            if let Kids::Ref(n, ns, _) = a.nodes[*at].kids
                && env.levels().any(|l| matches!(l, Level::Shape(_)))
            {
                c.resolve(*at, n, ns);
            }
        }
        for (k, node) in a.nodes.iter().enumerate() {
            let Kids::Form(_) = node.kids else { continue };
            if !c.head(&node.syn).is_some_and(opens) || out.written.contains_key(&node.path) {
                continue;
            }
            let items = node.syn.as_proper_list().expect("a form");
            if items.get(1).and_then(|m| m.as_symbol()).is_some_and(|m| matches!(c.name(m), "#%fx" | "#%toplevel")) {
                continue;
            }
            let Some(m) = c.elem(k, 1) else { continue };
            let asked = c.asked.get(&m).cloned().unwrap_or_default();
            let s = (!asked.unknown).then(|| asked.written(node.syn.span));
            out.written.insert(node.path.clone(), s);
        }
        if !top {
            out.shape = c.exp(root);
            return Ok(out);
        }
        // What the top level's definitions bind, for the forms after.
        if let (STy::Item, Kids::Form(x)) = (&*a.nodes[root].core, &a.nodes[root].kids)
            && let Some((b, r)) = &a.nodes[*x].export
        {
            for level in a.eval(b, *r, form.span)? {
                match level {
                    Level::Rib(atoms) => {
                        for atom in atoms.iter().cloned() {
                            if let Atom::Lit(b, ns) = atom
                                && let Kids::Binder(n, _) = a.nodes[b].kids
                            {
                                out.defined.push((n, ns, c.binder(b)));
                            }
                        }
                    }
                    Level::Shape(m) => {
                        if let Some(Shape::Module { vals, descs }) = c.exp(m).as_deref() {
                            out.defined.extend(vals.iter().map(|(n, s)| (*n, Ns::Value, s.clone())));
                            out.defined.extend(descs.iter().map(|(n, s)| (*n, Ns::Desc, s.clone())));
                        }
                    }
                    _ => {}
                }
            }
        }
        Ok(out)
    }

    /// The shape of the file at `at` whose forms are `forms` (its own
    /// loads' shapes known already), kept by its key (`load_key`), with
    /// what to write into its forms (`file_forms_shaped`). A file that does
    /// not walk has no shape, and the checkers say why where it is read.
    pub(crate) fn file_shaped(&mut self, key: String, forms: &[Syntax], input: bool, dir: Option<std::path::PathBuf>, interner: &mut Interner) -> R<()> {
        self.ensure_kernel(interner)?;
        let params = forms.first().is_some_and(|f| crate::parse::module_parameters_of(f, interner).is_some());
        let Some(form) = file_form(forms, input && !params, interner) else {
            self.withs.shapes.files.insert(key, FileShape::default());
            return Ok(());
        };
        let outer = std::mem::replace(&mut self.withs.shapes.dir, dir);
        let walked = self.walked(&form, false, None, interner);
        self.withs.shapes.dir = outer;
        let walked = walked.unwrap_or_default();
        // An input's value is its expression's; the module
        // `load-input-moduleof` describes, what that makes, given what it
        // takes. A file of module parameters makes a module of its items.
        let (value, module) = match (params, walked.shape) {
            (true, m) => (Shape::fun(Vec::new(), m.clone()), m),
            (false, Some(f)) if input && matches!(&*f, Shape::Fun { .. }) => (Some(f.clone()), f.result()),
            (false, m) => (m.clone(), m),
        };
        self.withs.shapes.files.insert(key, FileShape { value, module, written: Some(Rc::new(walked.written)) });
        Ok(())
    }

    /// A file's forms, `forms`, as it is read to be checked, with the
    /// shapes its walk found written in: kept from when its shape was
    /// found (`file_shaped`), or found now, read from directory `dir`.
    pub(crate) fn file_forms_shaped(&mut self, key: &str, forms: Vec<Syntax>, input: bool, dir: Option<std::path::PathBuf>, interner: &mut Interner) -> Vec<Syntax> {
        let params = forms.first().is_some_and(|f| crate::parse::module_parameters_of(f, interner).is_some());
        let wrapped = !(input && !params);
        let Some(form) = file_form(&forms, !wrapped, interner) else { return forms };
        let written = match self.withs.shapes.files.get(key).and_then(|f| f.written.clone()) {
            Some(w) => w,
            None => {
                let outer = std::mem::replace(&mut self.withs.shapes.dir, dir);
                let walked = self.shapes_prepared(interner).and_then(|()| self.walked(&form, false, None, interner));
                self.withs.shapes.dir = outer;
                match walked {
                    Ok(w) => Rc::new(w.written),
                    Err(_) => return forms,
                }
            }
        };
        if self.shapes_prepared(interner).is_err() {
            return forms;
        }
        let shaped = with_written(&form, &mut Vec::new(), &written, interner);
        if wrapped { shaped.as_proper_list().expect("a module")[1..].to_vec() } else { vec![shaped] }
    }

    /// What `shaped` needs made first, which it cannot make itself: the
    /// kernel read, and the names it writes interned.
    pub(crate) fn shapes_prepared(&mut self, interner: &mut Interner) -> R<()> {
        interner.intern("relied");
        interner.intern("#f");
        self.ensure_kernel(interner)
    }

    /// The forms of the file at `at` as they were read for its shape, if
    /// they were, of the same text: taken, so read once.
    pub(crate) fn forms_read(&mut self, at: &str, text: &str) -> Option<Vec<Syntax>> {
        let (read, forms) = self.withs.shapes.read.remove(at)?;
        (read == text).then_some(forms)
    }

    /// Keeps the forms of the file at `at`, as read for its shape.
    pub(crate) fn keep_forms_read(&mut self, at: String, text: String, forms: Vec<Syntax>) {
        self.withs.shapes.read.insert(at, (text, forms));
    }

    /// `(define-syntax s (modnames …))`, `form`, if it is one: the shape
    /// named, its name given back; a macro of that name forgotten.
    pub(crate) fn shape_defined(&mut self, form: &Syntax, interner: &Interner) -> Option<Sym> {
        let [h, n, m] = form.as_proper_list()? else { return None };
        let (h, n) = (h.as_symbol()?, n.as_symbol()?);
        let head = m.as_proper_list()?.first()?.as_symbol()?;
        if interner.name(h) != "define-syntax" || interner.name(head) != "modnames" {
            return None;
        }
        self.defined.remove(&n);
        self.withs.shapes.named.insert(n, m.clone());
        Some(n)
    }

    /// Whether `n` names a shape (`shape_defined`).
    pub(crate) fn is_shape(&self, n: Sym) -> bool {
        self.withs.shapes.named.contains_key(&n)
    }

    /// Form `s` with each shape a name stands for written where a value
    /// supplies its types, a `define`'s or `the`'s type (`(define x S e)`,
    /// `(the S e)`, `S` a shape's name), and each such `define` made `(define
    /// x (the (modnames …) e))`, which the checkers seal there
    /// (`Checker::the_sealed`); outside quotes. The first shape used as a
    /// form's head, refused.
    pub(crate) fn sealed_written(&self, s: &Syntax, interner: &mut Interner) -> R<Syntax> {
        let Datum::List { items, tail } = &s.datum else { return Ok(s.clone()) };
        let head = items.first().and_then(|h| h.as_symbol());
        let name = head.map(|h| interner.name(h).to_string()).unwrap_or_default();
        if matches!(name.as_str(), "quote" | "quasiquote" | "%datum") {
            return Ok(s.clone());
        }
        if let Some(h) = head.filter(|h| self.is_shape(*h)) {
            return Err(FxError::at(s.span, format!("`{}` is a shape, not a macro: it is written as a `define`'s or `the`'s type", interner.name(h))));
        }
        let mut items = items.iter().map(|i| self.sealed_written(i, interner)).collect::<R<Vec<_>>>()?;
        let modnames = interner.intern("modnames");
        let shape_of = |t: &Syntax| -> Option<Syntax> {
            let named = t.as_symbol().and_then(|n| self.withs.shapes.named.get(&n)).cloned();
            let written = t.as_proper_list().and_then(|l| l.first()?.as_symbol()) == Some(modnames);
            named.or_else(|| written.then(|| t.clone()))
        };
        match (name.as_str(), &items[..]) {
            ("define", [_, x, t, e]) if tail.is_none() => {
                if let Some(m) = shape_of(t) {
                    let the = Syntax::symbol(s.span, interner.intern("the"));
                    let sealed = Syntax::list(s.span, vec![the, m, e.clone()]);
                    items = vec![items[0].clone(), x.clone(), sealed];
                }
            }
            ("the", [_, t, _]) if tail.is_none() => {
                if let Some(m) = shape_of(t) {
                    items[1] = m;
                }
            }
            _ => {}
        }
        let tail = tail.as_ref().map(|t| self.sealed_written(t, interner).map(Box::new)).transpose()?;
        Ok(Syntax::new(s.span, Datum::List { items, tail }))
    }

    /// The top-level forms noted, before and after their shapes were
    /// written, if they are kept (`Checker::keep_shapes_seen`).
    pub(crate) fn shapes_seen(&mut self) -> &mut Option<Vec<(String, String)>> {
        &mut self.withs.shapes.seen
    }

    /// Whether the file of `key` has had its shape found (or is being).
    pub(crate) fn file_shape_known(&self, key: &str) -> bool {
        self.withs.shapes.files.contains_key(key)
    }

    /// Notes that the file of `key` is being read for its shape, so that a
    /// load cycle finds none.
    pub(crate) fn file_shape_begun(&mut self, key: String) {
        self.withs.shapes.files.insert(key, FileShape::default());
    }
}

impl Known {
    /// Whether the top level defines `n`, a description if `desc`, as the
    /// forms walked before found it.
    pub(crate) fn top_has(&self, n: Sym, desc: bool) -> bool {
        self.aliases_defined.contains(&(n, desc)) || if desc { self.top.descs.contains_key(&n) } else { self.top.vals.contains_key(&n) }
    }
}

/// `s`, at `path`, with each shape of `written` written into the form at
/// its path, after its first operand.
fn with_written(s: &Syntax, path: &mut Vec<bool>, written: &Written, interner: &Interner) -> Syntax {
    let words = (interner.get("relied").expect("interned"), interner.get("#f").expect("interned"));
    with_written_in(s, path, written, interner, words)
}

fn with_written_in(s: &Syntax, path: &mut Vec<bool>, written: &Written, interner: &Interner, words: (Sym, Sym)) -> Syntax {
    let (shape, no) = words;
    let Datum::List { items, tail } = &s.datum else { return s.clone() };
    let mut out = Vec::with_capacity(items.len() + 2);
    let depth = path.len();
    // Only a form that opens a module is looked up: a long list's paths
    // are long.
    let opening = items.first().and_then(|h| h.as_symbol()).is_some_and(|h| opens(interner.name(h)));
    let written_here = if opening { written.get(&path[..depth]).cloned() } else { None };
    for (k, i) in items.iter().enumerate() {
        if k == 2
            && let Some(w) = &written_here
        {
            out.push(Syntax::new(s.span, Datum::Keyword(shape)));
            out.push(w.clone().unwrap_or_else(|| Syntax::symbol(s.span, no)));
        }
        path.push(true);
        out.push(with_written_in(i, path, written, interner, words));
        path.pop();
        path.push(false);
    }
    if items.len() == 2
        && let Some(w) = &written_here
    {
        out.push(Syntax::new(s.span, Datum::Keyword(shape)));
        out.push(w.clone().unwrap_or_else(|| Syntax::symbol(s.span, no)));
    }
    let tail = tail.as_ref().map(|t| Box::new(with_written_in(t, path, written, interner, words)));
    path.truncate(depth);
    Syntax::new(s.span, Datum::List { items: out, tail })
}

#[cfg(test)]
mod tests {
    use crate::Checker;
    use fixpt_read::FileId;

    /// Each form of `text`, its shapes written, checked: the forms as
    /// written, those that open a module alone.
    fn written(text: &str) -> Vec<String> {
        let mut c = Checker::new();
        let mut out = Vec::new();
        for f in c.read_in(FileId(0), text).expect("reads") {
            let shaped = c.shapes_written(&f, true);
            let shown = fixpt_read::write_syntax(&shaped, &c.interner);
            c.top(&f).unwrap_or_else(|e| panic!("`{shown}` checks: {}", e.message));
            let mut found = Vec::new();
            opened(&shaped, &c, &mut found);
            out.extend(found);
        }
        out
    }

    /// Each `with`, `extend` and `include` in `s` with a shape written,
    /// written up to its shape.
    fn opened(s: &fixpt_read::Syntax, c: &Checker, out: &mut Vec<String>) {
        let Some(items) = s.as_proper_list() else { return };
        if let [h, m, k, shape, ..] = items
            && matches!(&k.datum, fixpt_read::Datum::Keyword(w) if c.interner.name(*w) == "relied")
        {
            let w = |s| fixpt_read::write_syntax(s, &c.interner);
            out.push(format!("({} {} {})", w(h), w(m), w(shape)));
        }
        for i in items {
            opened(i, c, out);
        }
    }

    #[test]
    fn a_modules_shape_is_read_from_what_binds_it() {
        let text = include_str!("../../tests/shapes/read.fx");
        let w = written(text);
        // Each the names its body asks of its module, alone.
        assert_eq!(w[..5], ["(with m ((x) (t)))", "(with n ((x) ()))", "(with g ((y) ()))", "(with m ((sub) ()))", "(with sub ((z) ()))"]);
        assert_eq!(w[5], "(with p ((e-var) ()))");
    }

    #[test]
    fn a_shape_in_a_positive_place_is_known() {
        let w = written(include_str!("../../tests/shapes/positive.fx"));
        assert_eq!(w, ["(with n ((x) ()))", "(with m ((x) ()))"]);
    }

    #[test]
    fn what_a_hidden_include_gives_is_not_given() {
        let text = "(define a (module (define-type t int) (define x int 1)))
                    (define b (module (hide (include a)) (define-type t int) (define-type u int) (define y int 2)))
                    (define main (lambda () (with b y)))";
        // `int`, which the items name, asked of `a` too, is not written:
        // the checker holds `a` not to give it, as it reads the items.
        assert_eq!(written(text), ["(include a (() ()))", "(with b ((y) ()))"]);
    }

    #[test]
    fn a_module_of_no_known_shape_is_said_so() {
        let text = "(define-type sig (moduleof (val x int)))
                    (define h (lambda ((m sig)) (with m x)))
                    (define k (lambda ((ms (listof sig))) (let ((m (car ms))) (with m x))))";
        let mut c = Checker::new();
        let forms = c.read_in(FileId(0), text).expect("reads");
        let shown: Vec<String> = forms.iter().map(|f| {
            let s = c.shapes_written(f, true);
            fixpt_read::write_syntax(&s, &c.interner)
        }).collect();
        assert!(shown[1].contains("(with m #:relied ((x) ()) x)"), "{}", shown[1]);
        assert!(shown[2].contains("(with m #:relied |#f| x)"), "{}", shown[2]);
        c.top(&forms[0]).expect("checks");
        c.top(&forms[1]).expect("checks");
        let e = c.top(&forms[2]).expect_err("refused");
        assert!(e.message.contains("the names `m` gives are not known before it is checked"), "{}", e.message);
    }

    /// A record that is not the module's type's, as no walk writes it: the
    /// checker holds the module to the names it gives, and refuses one it
    /// gives that a reference took to be bound outside it, value or type.
    #[test]
    fn a_record_the_type_does_not_keep_is_refused() {
        let mut c = Checker::new();
        for (text, said) in [
            ("(define m (module (define x int 5))) (define main (lambda () (with m #:relied ((x y) ()) x)))", "its type has no `y`"),
            ("(define y int 1) (define m (module (define x int 5) (define y int 6))) (define main (lambda () (with m #:relied ((x) ()) (+ x y))))", "its type gives `y`, which the program took"),
            ("(define-type t int) (define m (module (define-type t bool))) (define main (lambda () (with m #:relied (() ()) (the t 5))))", "its type gives `t`, which the program took"),
            ("(define m (module (define x int 5) (define y int 6))) (define main (lambda () (with m #:relied ((x) ()) x)))", ""),
        ] {
            let forms = c.read_in(FileId(0), text).expect("reads");
            let (last, before) = forms.split_last().expect("forms");
            for f in before {
                c.top(f).expect("checks");
            }
            // A name no reference asked, the module may give.
            if said.is_empty() {
                c.top_as_shaped(last).expect("checks");
                continue;
            }
            let e = c.top_as_shaped(last).expect_err("refused");
            assert!(e.message.contains("gives other names than were read") && e.message.contains(said), "{}", e.message);
        }
    }
}
