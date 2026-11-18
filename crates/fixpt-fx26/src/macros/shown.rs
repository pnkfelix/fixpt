//! A signature in Herman's form, `(macro/addressed σ made)`, as one inferred
//! is shown: in shapes and facts, `(macro SHAPE MADE FACT …)`, if one says
//! it (`typed-macros.md`, "Decided: signatures in shapes and facts").
//!
//! Each part an address or a fact names is labelled: by the first clause's
//! pattern variable at the same place, if it has one free, else `p1`, `p2`,
//! …; each import a `bind`, a named node's export an `export` or `export*`,
//! a repeated element's import `(bind v in e) ...`, an element's export
//! what `(v ...)` names; each `mu` a `letrec-shape`'s shape, its union's
//! members `end`, the empty one, and `more`, `more2`, ….
//!
//! What is shown is checked: elaborated back (`contract::elaborated`), it
//! must be the signature itself, or none is shown and Herman's form is, so
//! that the one shown always means what was inferred. Syntax to syntax, as
//! `macros-shown.fx` does the same.

use crate::heap_syn::{At, Syn, V};
use fixpt_read::{Interner, Sym};

/// Signature `sig`, in Herman's form, in shapes and facts, its labels from
/// `clause`'s pattern, `((_ . pattern) template)`: none if that does not
/// say the same.
pub(crate) fn in_shapes(sig: &Syn, clause: Option<&Syn>, interner: &mut Interner) -> Option<Syn> {
    let items = sig.list()?;
    let [h, sigma, made] = &items[..] else { return None };
    if !h.sym().is_some_and(|h| interner.name(h) == "macro/addressed") {
        return None;
    }
    let at = sig.at();
    let pattern = clause.and_then(|c| c.split()).and_then(|(p, _)| p.split()).map(|(_, ops)| ops);
    let mut cx = Cx { interner, shapes: Vec::new() };
    let (tree, mut facts, made) = cx.node(*sigma, pattern, Some(*made))?;
    let made = made.expect("the top's");
    let under = Syn::named(at, "_", cx.interner);
    let top = match tree.view() {
        V::List { items, tail } => {
            let all: Vec<Syn> = std::iter::once(under).chain(items.iter().copied()).collect();
            Syn::of_list(at, &all, tail)
        }
        V::Nil => Syn::lst(at, vec![under]),
        _ => return None,
    };
    let shape = if cx.shapes.is_empty() {
        top
    } else {
        let defs: Vec<Syn> = cx.shapes.iter().map(|(n, d)| Syn::lst(at, vec![Syn::symbol(at, *n, cx.interner), d.expect("defined")])).collect();
        let head = Syn::named(at, "letrec-shape", cx.interner);
        Syn::lst(at, vec![head, Syn::lst(at, defs), top])
    };
    let head = Syn::named(at, "macro", cx.interner);
    let mut all = vec![head, shape, made];
    all.append(&mut facts);
    let shown = Syn::lst(at, all);
    // Said the same, or not shown.
    let back = super::contract::elaborated(&shown, cx.interner).ok()?;
    (flat(&back, cx.interner) == flat(sig, cx.interner)).then_some(shown)
}

struct Cx<'a> {
    interner: &'a mut Interner,
    /// The `letrec-shape`'s shapes, each `mu`'s, as first met; its node or
    /// union once written.
    shapes: Vec<(Sym, Option<Syn>)>,
}

/// A region of a node: the node's own, or a repeated element's, in the
/// region `parent` at the list's path; the pattern there, if known; what
/// an element exports.
struct Region {
    parent: Option<(usize, Vec<bool>)>,
    pattern: Option<Syn>,
    export: Option<Syn>,
}

/// A node being shown: its regions, the imports met, innermost first, and
/// each labelled part's name and whether it is written `place`.
#[derive(Default)]
struct Node {
    regions: Vec<Region>,
    imports: Vec<(usize, Vec<bool>, Syn)>,
    /// Each part named: its region and path; the name, given when written.
    named: Vec<((usize, Vec<bool>), Option<Sym>)>,
    places: Vec<(usize, Vec<bool>)>,
    used: Vec<String>,
    counter: usize,
}

impl Node {
    fn element(&self, r: usize, path: &[bool]) -> Option<usize> {
        self.regions.iter().position(|g| g.parent.as_ref().is_some_and(|(pr, pp)| *pr == r && pp == path))
    }

    fn name_of(&self, r: usize, path: &[bool]) -> Option<Sym> {
        self.named.iter().find(|((nr, np), _)| *nr == r && np == path).and_then(|(_, n)| *n)
    }

    fn wanted(&self, r: usize, path: &[bool]) -> bool {
        self.named.iter().any(|((nr, np), _)| *nr == r && np == path)
    }

    fn want(&mut self, r: usize, path: &[bool]) {
        if !self.wanted(r, path) {
            self.named.push(((r, path.to_vec()), None));
        }
    }
}

/// What a fact names: a part, or `(v ...)`, every repetition's.
enum Named {
    Part(usize, Vec<bool>),
    Every(usize, Vec<bool>),
}

impl Cx<'_> {
    fn sym(&mut self, at: At, n: &str) -> Syn {
        Syn::named(at, n, self.interner)
    }

    fn head(&self, s: &Syn) -> Option<String> {
        s.list().and_then(|l| l.first().and_then(|h| h.sym())).map(|h| self.interner.name(h).to_string())
    }

    fn is(&self, s: &Syn, n: &str) -> bool {
        s.sym().is_some_and(|x| self.interner.name(x) == n)
    }

    /// Whether list `s` is a syntax type's form, not a list of parts (as
    /// `contract.rs`'s `is_form` reads it).
    fn is_form(&self, s: &Syn) -> bool {
        match self.head(s).as_deref() {
            Some("many" | "literal" | "trailmark" | "oneof" | "union") => true,
            Some("expr" | "bvar" | "lambda") => s.list().and_then(|l| l.get(1).copied()).is_some_and(|k| matches!(k.view(), V::Keyword(_))),
            _ => false,
        }
    }

    /// Node `sigma`, its labels from `pattern` (the top's): its tree and
    /// its facts; at the top (`made` given), what its uses make.
    fn node(&mut self, sigma: Syn, pattern: Option<Syn>, made: Option<Syn>) -> Option<(Syn, Vec<Syn>, Option<Syn>)> {
        let mut n = Node { regions: vec![Region { parent: None, pattern, export: None }], ..Node::default() };
        let (sigma, export) = match self.head(&sigma).as_deref() {
            Some("export") if made.is_none() => {
                let l = sigma.list()?;
                (*l.get(1)?, Some(*l.get(2)?))
            }
            _ => (sigma, None),
        };
        let bare = self.strip(sigma, 0, Vec::new(), &mut n)?;
        // What each fact names, wanted labelled.
        let mut binds = Vec::new();
        for (r, tp, b) in std::mem::take(&mut n.imports) {
            n.want(r, &tp);
            let l = self.bound(&b, r, &mut n)?;
            binds.push((r, tp, l));
        }
        let mut exports = Vec::new();
        let mut cage = false;
        if let Some(b) = export {
            let items = b.list()?;
            match self.interner.name(items[0].sym()?) {
                "rho" => {
                    for e in &items[1..] {
                        exports.push(self.entry(e, 0, &mut n)?);
                    }
                }
                "cage" => {
                    cage = true;
                    for ring in items[1..].iter().rev() {
                        exports.push(self.bound(ring, 0, &mut n)?);
                    }
                }
                _ => return None,
            }
        }
        let mut defined = Vec::new();
        let made = match made {
            Some(m) if self.head(&m).as_deref() == Some("defn") => {
                for e in &m.list()?[1..] {
                    let parts = e.list()?;
                    let [p, d] = &parts[..] else { return None };
                    if d.sym().is_some() {
                        defined.push((self.entry(e, 0, &mut n)?, None));
                    } else {
                        let path = path_of(p, self.interner)?;
                        n.want(0, &path);
                        defined.push((Named::Part(0, path), Some(*d)));
                    }
                }
                Some(m)
            }
            m => m,
        };
        let tree = self.write(bare, 0, Vec::new(), &mut n)?;
        if n.named.iter().any(|(_, s)| s.is_none()) {
            return None;
        }
        let at = sigma.at();
        let mut facts = Vec::new();
        for (r, tp, l) in binds {
            let (bind, kw) = (self.sym(at, "bind"), self.sym(at, "in"));
            let t = Syn::symbol(at, n.name_of(r, &tp)?, self.interner);
            let l = self.said(&l, &n, at)?;
            facts.push(Syn::lst(at, vec![bind, l, kw, t]));
            if r != 0 {
                facts.push(self.sym(at, "..."));
            }
        }
        if !exports.is_empty() {
            let mut items = vec![self.sym(at, if cage { "export*" } else { "export" })];
            for l in &exports {
                items.push(self.said(l, &n, at)?);
            }
            facts.push(Syn::lst(at, items));
        }
        let made = match made {
            Some(m) if self.head(&m).as_deref() == Some("defn") => {
                let mut items = vec![self.sym(at, "defn")];
                for (l, d) in &defined {
                    let l = self.said(l, &n, at)?;
                    items.push(match d {
                        Some(d) => Syn::lst(at, vec![l, *d]),
                        None => l,
                    });
                }
                Some(Syn::lst(m.at(), items))
            }
            m => m,
        };
        Some((tree, facts, made))
    }

    /// A label said: its name, or `(name ...)`.
    fn said(&mut self, l: &Named, n: &Node, at: At) -> Option<Syn> {
        match l {
            Named::Part(r, p) => Some(Syn::symbol(at, n.name_of(*r, p)?, self.interner)),
            Named::Every(r, p) => {
                let name = Syn::symbol(at, n.name_of(*r, p)?, self.interner);
                let dots = self.sym(at, "...");
                Some(Syn::lst(at, vec![name, dots]))
            }
        }
    }

    /// What binding `b` of region `r` says, one label: `(rho entry)`,
    /// `(cage (at path))`, or a ring, `(at path)`.
    fn bound(&mut self, b: &Syn, r: usize, n: &mut Node) -> Option<Named> {
        let items = b.list()?;
        match (self.interner.name(items[0].sym()?), &items[1..]) {
            ("rho", [e]) => self.entry(e, r, n),
            ("cage", [ring]) if self.head(ring).as_deref() == Some("at") => self.bound(ring, r, n),
            ("at", [p]) => {
                let path = path_of(p, self.interner)?;
                n.want(r, &path);
                Some(Named::Part(r, path))
            }
            _ => None,
        }
    }

    /// A rib's entry `(path δ)` of region `r`: its part, or, a list's rib
    /// of what its element exports, one entry, `(v ...)`.
    fn entry(&mut self, e: &Syn, r: usize, n: &mut Node) -> Option<Named> {
        let parts = e.list()?;
        let [p, d] = &parts[..] else { return None };
        let path = path_of(p, self.interner)?;
        let d = self.interner.name(d.sym()?).to_string();
        if d == "rib"
            && let Some(er) = n.element(r, &path)
        {
            let ex = n.regions[er].export?;
            let items = ex.list()?;
            let [h, inner] = &items[..] else { return None };
            if !self.is(h, "rho") {
                return None;
            }
            let Named::Part(_, ep) = self.entry(inner, er, n)? else { return None };
            return Some(Named::Every(er, ep));
        }
        n.want(r, &path);
        if d == "place" {
            n.places.push((r, path.clone()));
        }
        Some(Named::Part(r, path))
    }

    /// `s`, at `path` of region `r`, its imports, `mu`s and elements'
    /// exports taken out and noted; none if one is where a fact cannot say
    /// it.
    fn strip(&mut self, s: Syn, r: usize, path: Vec<bool>, n: &mut Node) -> Option<Syn> {
        match self.head(&s).as_deref() {
            Some("import") => {
                let items = s.list()?;
                let [_, inner, b] = &items[..] else { return None };
                let bare = self.strip(*inner, r, path.clone(), n)?;
                n.imports.push((r, path, *b));
                return Some(bare);
            }
            Some("export" | "path" | "rho" | "cage") => return None,
            Some("mu") => {
                let items = s.list()?;
                let [_, name, body] = &items[..] else { return None };
                self.shape(name.sym()?, *body)?;
                return Some(*name);
            }
            Some("oneof" | "union") => {
                let items = s.list()?;
                let mut out = vec![self.sym(s.at(), "oneof")];
                for m in &items[1..] {
                    out.push(self.plain(*m)?);
                }
                return Some(Syn::lst(s.at(), out));
            }
            Some("many") => {
                let items = s.list()?;
                let [h, inner] = &items[..] else { return None };
                let inner = self.plain(*inner)?;
                return Some(Syn::lst(s.at(), vec![*h, inner]));
            }
            _ if self.is_form(&s) => return Some(s),
            _ => {}
        }
        let Some((items, tail)) = self.parts(&s) else { return Some(s) };
        let (mut out, mut p) = (Vec::new(), path);
        let len = items.len();
        for (i, item) in items.iter().enumerate() {
            // `elem ...`: the element a region of its own.
            if i + 2 == len && tail.is_none() && self.is(&items[i + 1], "...") {
                let pattern = n.regions[r].pattern.and_then(|pt| at_path(pt, &p)).and_then(|c| c.split()).map(|(e, _)| e);
                let er = n.regions.len();
                n.regions.push(Region { parent: Some((r, p.clone())), pattern, export: None });
                let elem = match self.head(item).as_deref() {
                    Some("export") => {
                        let l = item.list()?;
                        n.regions[er].export = Some(*l.get(2)?);
                        *l.get(1)?
                    }
                    _ => *item,
                };
                out.push(self.strip(elem, er, Vec::new(), n)?);
                out.push(items[i + 1]);
                return Some(Syn::of_list(s.at(), &out, None));
            }
            let mut ap = p.clone();
            ap.push(true);
            out.push(self.strip(*item, r, ap, n)?);
            p.push(false);
        }
        let tail = match tail {
            Some(t) => Some(self.strip(t, r, p, n)?),
            None => None,
        };
        Some(Syn::of_list(s.at(), &out, tail))
    }

    /// A tree that says no fact: a union's member, a `many`'s part.
    fn plain(&mut self, s: Syn) -> Option<Syn> {
        let mut n = Node { regions: vec![Region { parent: None, pattern: None, export: None }], ..Node::default() };
        let bare = self.strip(s, 0, Vec::new(), &mut n)?;
        (n.imports.is_empty() && n.regions.iter().all(|g| g.export.is_none())).then_some(bare)
    }

    /// `mu` `name`'s shape, `body`, written once: a union's members each a
    /// node, or one node.
    fn shape(&mut self, name: Sym, body: Syn) -> Option<()> {
        if self.shapes.iter().any(|(n, _)| *n == name) {
            return Some(());
        }
        let k = self.shapes.len();
        self.shapes.push((name, None));
        let at = body.at();
        let def = if matches!(self.head(&body).as_deref(), Some("oneof" | "union")) {
            let mut out = vec![self.sym(at, "union")];
            let mut more = 0;
            for m in &body.list()?[1..] {
                let (tree, facts, _) = self.node(*m, None, None)?;
                let label = if matches!(tree.view(), V::Nil) {
                    "end".to_string()
                } else {
                    more += 1;
                    if more == 1 { "more".to_string() } else { format!("more{more}") }
                };
                let mut items = vec![self.sym(at, &label), tree];
                items.extend(facts);
                out.push(Syn::lst(at, items));
            }
            Syn::lst(at, out)
        } else {
            let (tree, facts, _) = self.node(body, None, None)?;
            let mut items = vec![Syn::symbol(at, name, self.interner), tree];
            items.extend(facts);
            Syn::lst(at, items)
        };
        self.shapes[k].1 = Some(def);
        Some(())
    }

    /// A name for the part at `path` of region `r`: its pattern variable
    /// there, if free, else the next `pN` free.
    fn fresh(&mut self, r: usize, path: &[bool], n: &mut Node) -> Sym {
        let free = |s: &str, n: &Node, cx: &Cx| !matches!(s, "_" | "..." | "@" | "." | "in") && !n.used.iter().any(|u| u == s) && !cx.shapes.iter().any(|(m, _)| cx.interner.name(*m) == s);
        let from_pattern = n.regions[r].pattern.and_then(|pt| at_path(pt, path)).and_then(|v| v.sym()).map(|v| self.interner.name(v).to_string());
        let name = match from_pattern {
            Some(v) if free(&v, n, self) => v,
            _ => loop {
                n.counter += 1;
                let v = format!("p{}", n.counter);
                if free(&v, n, self) {
                    break v;
                }
            },
        };
        n.used.push(name.clone());
        self.interner.intern(&name)
    }

    /// Bare tree `s`, at `path` of region `r`, written: each part named,
    /// `name @ σ`, a tail `name @ . σ`, an element `name @ σ ...`.
    fn write(&mut self, s: Syn, r: usize, path: Vec<bool>, n: &mut Node) -> Option<Syn> {
        let typed = |cx: &mut Cx, t: Syn, r: usize, p: &[bool], n: &Node| {
            if n.places.iter().any(|(pr, pp)| *pr == r && pp == p) && cx.is(&t, "dvar") { cx.sym(t.at(), "place") } else { t }
        };
        if self.is_form(&s) {
            return Some(s);
        }
        let Some((items, tail)) = self.parts(&s) else { return Some(s) };
        let (mut out, mut p) = (Vec::new(), path);
        let len = items.len();
        for (i, item) in items.iter().enumerate() {
            if i + 2 == len && tail.is_none() && self.is(&items[i + 1], "...") {
                let er = n.element(r, &p)?;
                if n.wanted(er, &[]) {
                    let name = self.fresh(er, &[], n);
                    self.named(n, er, &[], name);
                    out.push(Syn::symbol(s.at(), name, self.interner));
                    out.push(self.sym(s.at(), "@"));
                }
                let elem = self.write(*item, er, Vec::new(), n)?;
                out.push(typed(self, elem, er, &[], n));
                out.push(items[i + 1]);
                return Some(Syn::of_list(s.at(), &out, None));
            }
            let mut ap = p.clone();
            ap.push(true);
            if n.wanted(r, &ap) {
                let name = self.fresh(r, &ap, n);
                self.named(n, r, &ap, name);
                out.push(Syn::symbol(s.at(), name, self.interner));
                out.push(self.sym(s.at(), "@"));
            }
            let part = self.write(*item, r, ap.clone(), n)?;
            out.push(typed(self, part, r, &ap, n));
            p.push(false);
        }
        let tail = match tail {
            Some(t) => {
                let w = self.write(t, r, p.clone(), n)?;
                let w = typed(self, w, r, &p, n);
                if n.wanted(r, &p) {
                    // A tail labelled is a name or a word: a list's parts
                    // would be read as the list's own.
                    if !matches!(w.view(), V::Symbol(_)) {
                        return None;
                    }
                    let name = self.fresh(r, &p, n);
                    self.named(n, r, &p, name);
                    out.push(Syn::symbol(s.at(), name, self.interner));
                    out.push(self.sym(s.at(), "@"));
                }
                Some(w)
            }
            None => None,
        };
        // A tail that is a list, its items the list's.
        let tail = match tail.map(|t| t.view()) {
            Some(V::List { items, tail }) => {
                out.extend(items.iter().copied());
                tail
            }
            Some(V::Nil) => None,
            _ => tail,
        };
        Some(Syn::of_list(s.at(), &out, tail))
    }

    /// List `s`'s parts and tail; a rest that is a form, `(bvar . (import
    /// …))`, read as one list, its tail, as `sig_text` shows it. None for
    /// no list.
    fn parts(&self, s: &Syn) -> Option<(Vec<Syn>, Option<Syn>)> {
        let V::List { mut items, mut tail } = s.view() else { return None };
        let word = |x: &Syn| x.sym().is_some_and(|w| matches!(self.interner.name(w), "import" | "export" | "mu" | "oneof" | "union" | "many" | "literal" | "trailmark"));
        if let Some(k) = (1..items.len()).find(|&k| word(&items[k])) {
            tail = Some(Syn::of_list(s.at(), &items[k..], tail));
            items.truncate(k);
        }
        Some((items, tail))
    }

    fn named(&self, n: &mut Node, r: usize, p: &[bool], name: Sym) {
        if let Some(e) = n.named.iter_mut().find(|((nr, np), _)| *nr == r && np == p) {
            e.1 = Some(name);
        }
    }
}

/// `s` written, each list's tail that is a list its items: the same
/// structure, however it was built.
fn flat(s: &Syn, interner: &Interner) -> String {
    let V::List { items, mut tail } = s.view() else { return s.written(interner) };
    let mut parts: Vec<String> = items.iter().map(|i| flat(i, interner)).collect();
    let mut end = None;
    while let Some(t) = tail {
        match t.view() {
            V::List { items, tail: more } => {
                parts.extend(items.iter().map(|i| flat(i, interner)));
                tail = more;
            }
            V::Nil => tail = None,
            _ => {
                end = Some(flat(&t, interner));
                tail = None;
            }
        }
    }
    match end {
        Some(e) => format!("({} . {e})", parts.join(" ")),
        None => format!("({})", parts.join(" ")),
    }
}

/// `(path #:a #:d …)`'s steps, or `()`'s, none.
fn path_of(p: &Syn, interner: &Interner) -> Option<Vec<bool>> {
    match p.view() {
        V::Nil => Some(Vec::new()),
        V::List { items, tail: None } if items.first().and_then(|h| h.sym()).is_some_and(|h| interner.name(h) == "path") => items[1..]
            .iter()
            .map(|k| match k.view() {
                V::Keyword(w) if interner.name(w) == "a" => Some(true),
                V::Keyword(w) if interner.name(w) == "d" => Some(false),
                _ => None,
            })
            .collect(),
        _ => None,
    }
}

/// Pattern `p`'s part at `path`, if it has one.
fn at_path(p: Syn, path: &[bool]) -> Option<Syn> {
    let mut s = p;
    for step in path {
        let (car, cdr) = s.split()?;
        s = if *step { car } else { cdr };
    }
    Some(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::macros::Macros;
    use crate::macros::infer::Unsigned;

    /// Each macro of the tests' programs with a `syntax-rules`, its
    /// signature inferred from its clauses: shown in shapes and facts, that
    /// signature written back is the macro's, read as the one inferred, and
    /// the macro defined by it as by the one inferred, or refused as it.
    #[test]
    fn inferred_shown_in_shapes() {
        let dir = format!("{}/tests/programs/macros", env!("CARGO_MANIFEST_DIR"));
        let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
        names.sort();
        let (mut shapes, mut herman, mut wrong) = (Vec::new(), Vec::new(), Vec::new());
        for path in &names {
            let text = std::fs::read_to_string(path).unwrap();
            let (mut heap, mut syms) = (fixpt_heap::Heap::unfixed(), crate::heap_syn::SymTable::default());
            let mut interner = Interner::of_names(heap.names());
            crate::heap_syn::with_syntax(&mut heap, &mut syms, || {
                let Ok(forms) = crate::heap_syn::read_syn_side(&text, &mut interner) else { return };
                let mut m = Macros::default();
                m.ensure_kernel(&mut interner).unwrap();
                for f in &forms {
                    let Some(items) = f.list() else { continue };
                    let ds = items.first().and_then(|h| h.sym()).is_some_and(|h| interner.name(h) == "define-syntax");
                    let rules = items.last().and_then(|r| r.list()).filter(|r| r.first().and_then(|h| h.sym()).is_some_and(|h| interner.name(h) == "syntax-rules"));
                    let (true, Some(rules), 3 | 4) = (ds, rules, items.len()) else {
                        let _ = m.define(f, &mut interner);
                        continue;
                    };
                    let name = items[1].sym().unwrap();
                    let label = format!("{} {}", path.file_name().unwrap().to_string_lossy(), interner.name(name));
                    let Ok((lits, clauses)) = crate::macros::rules_parts(&rules[1..], f.at(), &interner) else { continue };
                    let u = Unsigned { name, lits, clauses: clauses.clone(), span: f.at() };
                    let Ok(s) = m.clone().infer(&[u], &mut interner) else {
                        let _ = m.define(f, &mut interner);
                        continue;
                    };
                    let h = s[0];
                    match in_shapes(&h, clauses.first(), &mut interner) {
                        Some(c) => {
                            let ct = crate::macros::infer::sig_text(&c, &interner);
                            let with = |sig: Syn| Syn::lst(f.at(), vec![items[0], items[1], sig, *items.last().unwrap()]);
                            let (fc, fh) = (with(c), with(h));
                            let (rc, rh) = (m.clone().signature(&c, &mut interner), m.clone().signature(&h, &mut interner));
                            let same = match (&rc, &rh) {
                                (Ok(a), Ok(b)) => a.1 == b.1 && a.2 == b.2 && a.3 == b.3,
                                (Err(_), Err(_)) => true,
                                _ => false,
                            };
                            let (dc, dh) = (m.clone().define(&fc, &mut interner).is_ok(), m.clone().define(&fh, &mut interner).is_ok());
                            if !same || dc != dh {
                                wrong.push(format!("{label}\n    {ct}\n    {}", h.written(&interner)));
                            }
                            shapes.push(format!("{label}\n    {ct}"));
                        }
                        None => herman.push(format!("{label}\n    {}", crate::macros::infer::sig_text(&h, &interner))),
                    }
                    let _ = m.define(f, &mut interner);
                }
            });
        }
        println!("in shapes and facts ({}):\n  {}", shapes.len(), shapes.join("\n  "));
        println!("Herman's ({}):\n  {}", herman.len(), herman.join("\n  "));
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
        // As many as when this was built: those Herman's form alone says,
        // `typed-macros.md`'s seven.
        assert!(shapes.len() >= 216, "only {} in shapes and facts", shapes.len());
    }
}
