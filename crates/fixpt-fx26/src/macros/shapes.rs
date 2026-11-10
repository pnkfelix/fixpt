//! Binding shapes (`docs/research/binding-shapes.md`, step 2): what a
//! module gives, by namespace, read from a program's syntax after its
//! expansion and before its types are known, so that what `with`,
//! `extend` and `include` bind is known where they are. Each such form has
//! its module's shape written into it, `(with m #:shape ((x …) (t …)) body
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
use crate::error::R;
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
    Fun(Rc<Shape>),
}

impl Shape {
    /// The names it gives in namespace `ns`, if it is a module's.
    fn gives(&self, n: Sym, ns: Ns) -> bool {
        match self {
            Shape::Module { vals, .. } if ns == Ns::Value => vals.iter().any(|(v, _)| *v == n),
            Shape::Module { descs, .. } => descs.iter().any(|(d, _)| *d == n),
            Shape::Fun(_) => false,
        }
    }

    /// Name `n`'s own shape, in namespace `ns`, if it gives one: a value
    /// that is a module, a type that is a module's.
    fn member(&self, n: Sym, ns: Ns) -> Option<Rc<Shape>> {
        let Shape::Module { vals, descs } = self else { return None };
        let list = if ns == Ns::Value { vals } else { descs };
        list.iter().find(|(v, _)| *v == n).and_then(|(_, s)| s.clone())
    }

    /// As written into a form (`#:shape`): `((value …) (description …))`.
    pub(crate) fn written(&self, span: Span) -> Option<Syntax> {
        let Shape::Module { vals, descs } = self else { return None };
        let names = |ns: Vec<Sym>| Syntax::list(span, ns.into_iter().map(|n| Syntax::symbol(span, n)).collect());
        Some(Syntax::list(span, vec![names(vals.iter().map(|(v, _)| *v).collect()), names(descs.iter().map(|(d, _)| *d).collect())]))
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
}

/// The shapes known from form to form: the top level's names', each file's
/// by its key (`load_key`), and the directory a file being read loads from.
#[derive(Clone, Debug, Default)]
pub(crate) struct Known {
    top: TopShapes,
    files: HashMap<String, FileShape>,
    dir: Option<std::path::PathBuf>,
}

/// Where a binder's value comes from, for its shape: the expression it is
/// bound to, the type it is declared to have, or (a description's binder)
/// the description it is defined as.
enum Source {
    Value(usize),
    Typed(usize),
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

/// `s` without the shapes written into it (`#:shape …`), as it was
/// expanded: what a program's walk reads.
pub(crate) fn unshaped(s: &Syntax, interner: &Interner) -> Syntax {
    let Datum::List { items, tail } = &s.datum else { return s.clone() };
    let mut out = Vec::with_capacity(items.len());
    let mut k = 0;
    while k < items.len() {
        if matches!(&items[k].datum, Datum::Keyword(w) if interner.name(*w) == "shape") && k == 2 {
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
    /// Each node's parent: the node of the list or form it is a part of.
    parent: Vec<Option<usize>>,
    envs: HashMap<usize, &'a super::Env>,
    /// Each node's shape as an expression (`false`) and as a type (`true`),
    /// once found; `None` while it is being found, so that a cycle finds
    /// none.
    memo: HashMap<(usize, bool), Option<Rc<Shape>>>,
}

impl<'a, 'm> Shaper<'a, 'm> {
    fn new(a: &'a Aligner<'m>, found: &'a super::Found, top: &'a TopShapes, files: &'a HashMap<String, FileShape>, dir: Option<&'a std::path::Path>) -> Self {
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
        Shaper { a, top, files, dir, parent, envs, memo: HashMap::new() }
    }

    fn name(&self, n: Sym) -> &'m str {
        let i: &'m Interner = self.a.interner;
        i.name(n)
    }

    fn head(&self, s: &Syntax) -> Option<&'m str> {
        s.as_proper_list()?.first()?.as_symbol().map(|h| self.name(h))
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
        for level in env.levels() {
            match level {
                Level::Rib(atoms) | Level::Earlier(atoms) => {
                    let b = atoms.iter().find_map(|x| match x {
                        Atom::Lit(b, m) if *m == ns && matches!(self.a.nodes[*b].kids, Kids::Binder(k, _) if k == n) => Some(*b),
                        _ => None,
                    });
                    if let Some(b) = b {
                        return Res::Binder(b);
                    }
                }
                // A module's own expression is not in the scope of what it
                // gives (an `include`'s, in its module's items).
                Level::Shape(m) if self.a.nodes[at].path.starts_with(&self.a.nodes[*m].path) => {}
                Level::Shape(m) => match self.exp(*m) {
                    Some(s) if s.gives(n, ns) => return Res::Member(*m, n, ns),
                    Some(_) => {}
                    None => return Res::Unknown,
                },
                Level::Cage(_) => {}
            }
        }
        Res::Free(n, ns)
    }

    /// Where binder `b`'s value comes from: the binding form it is in, by
    /// its place there.
    fn source(&self, b: usize) -> Option<Source> {
        let (q, i) = self.position(b)?;
        let list = &self.a.nodes[q].syn;
        let items = list.as_proper_list()?;
        match (self.head(list), i, items.len()) {
            (Some("define"), 1, 3) => Some(Source::Value(self.elem(q, 2)?)),
            (Some("define" | "define*"), 1, 4) => Some(Source::Typed(self.elem(q, 2)?)),
            (Some("define-type"), 1, 3) => Some(Source::Typed(self.elem(q, 2)?)),
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

    fn binder(&mut self, b: usize) -> Option<Rc<Shape>> {
        match self.source(b)? {
            Source::Value(e) => self.exp(e),
            Source::Typed(t) => self.ty(t),
        }
    }

    /// The shape of what a reference, at `at`, of `n` refers to.
    fn reference(&mut self, at: usize, n: Sym, ns: Ns) -> Option<Rc<Shape>> {
        match self.resolve(at, n, ns) {
            Res::Binder(b) => self.binder(b),
            Res::Member(m, n, ns) => self.exp(m)?.member(n, ns),
            Res::Free(n, Ns::Value) => self.top.vals.get(&n).cloned().flatten(),
            Res::Free(n, Ns::Desc) => self.top.descs.get(&n).cloned().flatten(),
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
            Some("lambda" | "rlambda") => Some(Rc::new(Shape::Fun(self.exp(last?)?))),
            // An application: its operator's result.
            _ => match &*self.exp(self.operator(at)?)? {
                Shape::Fun(s) => Some(s.clone()),
                Shape::Module { .. } => None,
            },
        }
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

    fn ty_found(&mut self, at: usize) -> Option<Rc<Shape>> {
        let a = self.a;
        let node = &a.nodes[at];
        if let Kids::Ref(n, Ns::Desc, _) = node.kids {
            return self.reference(at, n, Ns::Desc);
        }
        let syn = &node.syn;
        let items = syn.as_proper_list()?;
        let e = self.elems(at);
        match self.head(syn)? {
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
            "->" if items.len() == 3 => Some(Rc::new(Shape::Fun(self.ty(e[2]?)?))),
            "subr" => {
                let conv = items.get(1).is_some_and(|c| self.head(c) == Some("conv"));
                let k = if conv { 4 } else { 3 };
                Some(Rc::new(Shape::Fun(self.ty(e.get(k).copied().flatten()?)?)))
            }
            _ => None,
        }
    }
}

impl Macros {
    /// Form `form`, a program's after expansion (a top-level form, or, a
    /// file's items, a `module` of them, `module`): each `with`, `extend`
    /// and `include` in it with its module's shape written in, `#:shape
    /// ((value …) (description …))`, or `#:shape #f` where the shape is not
    /// known (`binding-shapes.md`, step 2); and, at the top level, what its
    /// definitions bind kept for the forms after it.
    pub(crate) fn shaped(&mut self, form: &Syntax, top: bool, dir: Option<std::path::PathBuf>, interner: &mut Interner) -> R<Syntax> {
        let outer = std::mem::replace(&mut self.withs.shapes.dir, dir);
        let r = self.shaped_from(form, top, interner);
        self.withs.shapes.dir = outer;
        r
    }

    fn shaped_from(&mut self, form: &Syntax, top: bool, interner: &mut Interner) -> R<Syntax> {
        self.ensure_kernel(interner)?;
        let form = unshaped(form, interner);
        let walked = self.walked(&form, top, interner)?;
        for (n, ns, s) in walked.defined {
            match ns {
                Ns::Value => self.withs.shapes.top.vals.insert(n, s),
                Ns::Desc => self.withs.shapes.top.descs.insert(n, s),
            };
        }
        Ok(with_written(&form, &mut Vec::new(), &walked.written, interner))
    }

    /// Form `form`, walked: the shapes to write into it, by the path of
    /// each form that opens a module; its own shape, as an expression's;
    /// and, `top`, what its definitions bind, with their shapes.
    fn walked(&self, form: &Syntax, top: bool, interner: &Interner) -> R<Walked> {
        let none = HashMap::new();
        let mut out = Walked::default();
        let mut a = Aligner { m: self, interner, mode: Mode::Program, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new() };
        let t = Rc::new(if top { STy::Item } else { STy::Expr });
        let root = a.align(&t, form, None, Vec::new())?;
        let mut found = Vec::new();
        a.walk(root, &super::Env::default(), false, 0, &mut found, &mut Vec::new())?;
        let empty = TopShapes::default();
        let tops = if top { &self.withs.shapes.top } else { &empty };
        let mut c = Shaper::new(&a, &found, tops, &self.withs.shapes.files, self.withs.shapes.dir.as_deref());
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
            let s = c.exp(m).and_then(|s| s.written(node.syn.span));
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
        let walked = self.walked(&form, false, interner);
        self.withs.shapes.dir = outer;
        let walked = walked.unwrap_or_default();
        let module = walked.shape;
        let value = if params { module.clone().map(|m| Rc::new(Shape::Fun(m))) } else { module.clone() };
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
                let walked = self.ensure_kernel(interner).and_then(|()| self.walked(&form, false, interner));
                self.withs.shapes.dir = outer;
                match walked {
                    Ok(w) => Rc::new(w.written),
                    Err(_) => return forms,
                }
            }
        };
        let shaped = with_written(&form, &mut Vec::new(), &written, interner);
        if wrapped { shaped.as_proper_list().expect("a module")[1..].to_vec() } else { vec![shaped] }
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

/// `s`, at `path`, with each shape of `written` written into the form at
/// its path, after its first operand.
fn with_written(s: &Syntax, path: &mut Vec<bool>, written: &Written, interner: &mut Interner) -> Syntax {
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
            out.push(Syntax::new(s.span, Datum::Keyword(interner.intern("shape"))));
            out.push(w.clone().unwrap_or_else(|| Syntax::symbol(s.span, interner.intern("#f"))));
        }
        path.push(true);
        out.push(with_written(i, path, written, interner));
        path.pop();
        path.push(false);
    }
    if items.len() == 2
        && let Some(w) = &written_here
    {
        out.push(Syntax::new(s.span, Datum::Keyword(interner.intern("shape"))));
        out.push(w.clone().unwrap_or_else(|| Syntax::symbol(s.span, interner.intern("#f"))));
    }
    let tail = tail.as_ref().map(|t| Box::new(with_written(t, path, written, interner)));
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
            && matches!(&k.datum, fixpt_read::Datum::Keyword(w) if c.interner.name(*w) == "shape")
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
        assert_eq!(w[..5], ["(with m ((x sub) (t)))", "(with n ((x) (t)))", "(with g ((y) ()))", "(with m ((x sub) (t)))", "(with sub ((z) ()))"]);
        assert!(w[5].starts_with("(with p ((") && w[5].contains(" e-var "), "{}", w[5]);
    }

    #[test]
    fn what_a_hidden_include_gives_is_not_given() {
        let text = "(define a (module (define-type t int) (define x int 1)))
                    (define b (module (hide (include a)) (define-type t int) (define-type u int) (define y int 2)))
                    (define main (lambda () (with b y)))";
        assert_eq!(written(text), ["(include a ((x) (t)))", "(with b ((y) (u)))"]);
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
        assert!(shown[1].contains("(with m #:shape ((x) ()) x)"), "{}", shown[1]);
        assert!(shown[2].contains("(with m #:shape |#f| x)"), "{}", shown[2]);
    }

    /// A shape that is not the module's type's, as no walk writes it: the
    /// checker holds the module to the shape, and refuses it.
    #[test]
    fn a_shape_the_type_does_not_have_is_refused() {
        let mut c = Checker::new();
        for (text, said) in [
            ("(define m (module (define x int 5))) (define main (lambda () (with m #:shape ((x y) ()) x)))", "its type has no `y`"),
            ("(define m (module (define x int 5) (define-type t int))) (define main (lambda () (with m #:shape ((x) ()) x)))", "its type gives `t` too"),
        ] {
            let forms = c.read_in(FileId(0), text).expect("reads");
            c.top(&forms[0]).expect("checks");
            let e = c.top_as_shaped(&forms[1]).expect_err("refused");
            assert!(e.message.contains("gives other names than were read") && e.message.contains(said), "{}", e.message);
        }
    }
}
