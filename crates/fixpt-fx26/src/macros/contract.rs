//! A signature in shapes and facts (`typed-macros.md`, "Decided: signatures
//! in shapes and facts, notation C revived"), elaborated to Herman's form,
//! `(macro/addressed σ made)`, which the checker reads: each label its
//! part's path from its region's root, each `bind` an import on the part
//! it names, each `export` a rib's export of its node, each `export*` a
//! ribcage's. Syntax to syntax, so that the expander written in FX-26 does
//! the same (`macros-contract.fx`).
//!
//! ```text
//! (macro SHAPE MADE FACT …)
//! SHAPE ::= (letrec-shape ((name NODE-OR-UNION) …) TOP) | TOP
//! TOP   ::= (_ PART …)
//! NODE  ::= (node-name TREE FACT …)      UNION ::= (union NODE …)
//! PART  ::= name @ σ | σ | … name @ . σ (a tail)
//! FACT  ::= (bind L in name) | (export L …) | (export* L …)
//! L     ::= label | (label ...)
//! MADE  ::= expr | desc | defn | (defn D …)   D ::= label | (label ...) | (label SIGNATURE)
//! ```

use crate::error::{FxError, R};
use crate::heap_syn::{At, Syn, V};
use fixpt_hash::HashMap;
use fixpt_read::{Interner, Sym};

/// What a labelled part provides, to a `bind` or an `export`: a value's
/// binder, a description's, a place's (both); what a part of a named shape
/// exports, a rib or a ribcage; nothing.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Gives {
    Var,
    Dvar,
    Place,
    Rib,
    Cage,
    Nothing,
}

/// A label of a region: its part's path from the region's root, what it
/// gives; or, a label inside a list's repeated element, the list's path,
/// and its path in the element, what it gives.
#[derive(Clone, Debug)]
enum Label {
    Here(Vec<bool>, Gives),
    Repeated(Vec<bool>, Vec<bool>, Gives),
}

/// A named shape: its definition, and what it exports.
struct Named {
    def: Syn,
    gives: Gives,
}

struct Cx<'a> {
    interner: &'a mut Interner,
    named: HashMap<Sym, Named>,
    /// The named shapes being written, innermost last: a reference to one
    /// is its `mu`'s variable.
    open: Vec<Sym>,
}

/// Whether signature `s` is one in shapes and facts: `(macro SHAPE …)`, its
/// shape `(_ …)` or `(letrec-shape …)`.
pub(crate) fn is_contract(s: &Syn, interner: &Interner) -> bool {
    let Some(items) = s.list() else { return false };
    // A shape may be dotted, `(_ part … . σ)`: its first item, whatever its tail.
    let head = |x: &Syn| match x.view() {
        V::List { items, .. } => items.first().and_then(|h| h.sym()).map(|h| interner.name(h).to_string()),
        _ => None,
    };
    items.len() >= 3 && items[0].sym().is_some_and(|h| interner.name(h) == "macro") && matches!(head(&items[1]).as_deref(), Some("_" | "letrec-shape"))
}

/// Signature `s`, in shapes and facts, as Herman's: `(macro/addressed σ
/// made)`.
pub(crate) fn elaborated(s: &Syn, interner: &mut Interner) -> R<Syn> {
    let items = s.list().expect("a list");
    let at = s.at();
    let (shape, made, facts) = (items[1], items[2], &items[3..]);
    let mut cx = Cx { interner, named: HashMap::default(), open: Vec::new() };
    let top = cx.shape(shape)?;
    // The top's parts after its `_`: the use's operands, the signature's
    // region.
    let (parts, tail) = list_parts(&top).ok_or_else(|| FxError::at(top.at(), "a signature's shape is `(_ part …)`, as a `syntax-rules` pattern is"))?;
    if parts.first().and_then(|h| h.sym()).is_none_or(|h| cx.name(h) != "_") {
        return Err(FxError::at(top.at(), "a signature's shape is `(_ part …)`, as a `syntax-rules` pattern is"));
    }
    let operands = list_of(top.at(), &parts[1..], tail);
    let mut labels = HashMap::default();
    let mut sigma = cx.tree(&operands, Vec::new(), &mut labels, &mut Vec::new())?;
    // What a use defines first: each element's export for a `(v ...)`
    // there before the facts'.
    let (made, adds) = cx.made(&made, &labels)?;
    sigma = cx.facts(sigma, facts, &labels, true, adds)?;
    let head = Syn::named(at, "macro/addressed", cx.interner);
    Ok(Syn::lst(at, vec![head, sigma, made]))
}

/// A list's parts, and its tail if dotted.
fn list_parts(s: &Syn) -> Option<(Vec<Syn>, Option<Syn>)> {
    match s.view() {
        V::List { items, tail } => Some((items.to_vec(), tail)),
        V::Nil => Some((Vec::new(), None)),
        _ => None,
    }
}

impl Cx<'_> {
    fn name(&self, n: Sym) -> String {
        self.interner.name(n).to_string()
    }

    fn sym(&mut self, at: At, n: &str) -> Syn {
        Syn::named(at, n, self.interner)
    }

    /// `SHAPE`: a `letrec-shape`'s names noted, its top given back.
    fn shape(&mut self, s: Syn) -> R<Syn> {
        let Some(items) = s.list() else { return Ok(s) };
        if !items.first().and_then(|h| h.sym()).is_some_and(|h| self.name(h) == "letrec-shape") {
            return Ok(s);
        }
        let usage = "`(letrec-shape ((name node) …) (_ part …))`, a node `(node-name tree fact …)` or `(union node …)`";
        let [_, defs, top] = &items[..] else { return Err(FxError::at(s.at(), usage)) };
        for d in defs.list().ok_or_else(|| FxError::at(defs.at(), usage))? {
            let Some(&[n, def]) = d.list().as_deref() else {
                return Err(FxError::at(d.at(), usage));
            };
            let name = n.sym().ok_or_else(|| FxError::at(n.at(), usage))?;
            if self.named.contains_key(&name) {
                return Err(FxError::at(n.at(), format!("`{}` is a shape's name twice", self.name(name))));
            }
            self.named.insert(name, Named { def, gives: Gives::Nothing });
        }
        // What each exports, from its facts: an `export`'s a rib, an
        // `export*`'s a ribcage.
        let names: Vec<Sym> = self.named.keys().copied().collect();
        for n in names {
            let gives = self.def_gives(self.named[&n].def)?;
            self.named.get_mut(&n).expect("named").gives = gives;
        }
        Ok(*top)
    }

    /// What a node, or each member of a union, exports.
    fn def_gives(&mut self, def: Syn) -> R<Gives> {
        let items = def.list().unwrap_or_default();
        if items.first().and_then(|h| h.sym()).is_some_and(|h| self.name(h) == "union") {
            let mut g = Gives::Nothing;
            for m in &items[1..] {
                let mg = self.def_gives(*m)?;
                if mg != Gives::Nothing {
                    if g != Gives::Nothing && g != mg {
                        return Err(FxError::at(m.at(), "a union's members export a rib and a ribcage, `export` and `export*`: one kind"));
                    }
                    g = mg;
                }
            }
            return Ok(g);
        }
        let mut g = Gives::Nothing;
        for f in items.iter().skip(2) {
            match f.list().and_then(|l| l.first().and_then(|h| h.sym())).map(|h| self.name(h)).as_deref() {
                Some("export") => g = Gives::Rib,
                Some("export*") => g = Gives::Cage,
                _ => {}
            }
        }
        Ok(g)
    }

    /// Tree `s` at `path` from its region's root, as a syntax type: each
    /// labelled part noted in `labels`, each repeated element its own
    /// region (`repeated`, the labels in it, by the list's path).
    fn tree(&mut self, s: &Syn, path: Vec<bool>, labels: &mut HashMap<Sym, Label>, repeated: &mut Vec<(Vec<bool>, HashMap<Sym, Label>)>) -> R<Syn> {
        match s.view() {
            V::List { .. } if self.is_form(s) => self.form(s, path, labels, repeated),
            V::List { items, tail } => {
                let at = s.at();
                let n = items.len();
                let (mut out, mut i, mut p) = (Vec::new(), 0, path.clone());
                let mut tail_out = None;
                while i < n {
                    // A tail labelled: `name @ . σ`.
                    if i + 2 == n && tail.is_some() && self.at_sign(&items[i + 1]) {
                        let t = tail.expect("a tail");
                        let g = self.gives(&t);
                        self.label(&items[i], Label::Here(p.clone(), g), labels)?;
                        tail_out = Some(self.tree(&t, p.clone(), labels, repeated)?);
                        break;
                    }
                    // `name @ σ`, or `σ`.
                    let (label, t, used) = if i + 2 < n && self.at_sign(&items[i + 1]) { (Some(items[i]), items[i + 2], 3) } else { (None, items[i], 1) };
                    let mut ap = p.clone();
                    ap.push(true);
                    // `part ...`: the element a region of its own, its
                    // labels the list's, repeated, the list at `p`.
                    if items.get(i + used).is_some_and(|x| self.dots(x)) {
                        let mut inner = HashMap::default();
                        let elem = self.tree(&t, Vec::new(), &mut inner, repeated)?;
                        if let Some(l) = label {
                            let g = self.gives(&t);
                            self.label(&l, Label::Here(Vec::new(), g), &mut inner)?;
                        }
                        for (name, l) in inner {
                            let Label::Here(ep, eg) = l else {
                                return Err(FxError::at(t.at(), "a repeated part in a repeated part: not yet"));
                            };
                            if labels.insert(name, Label::Repeated(p.clone(), ep, eg)).is_some() {
                                return Err(FxError::at(t.at(), format!("`{}` labels two parts", self.name(name))));
                            }
                        }
                        out.push(elem);
                        out.push(items[i + used]);
                        if i + used + 1 < n || tail.is_some() {
                            return Err(FxError::at(items[i + used].at(), "`...` comes last in a list"));
                        }
                        break;
                    }
                    if let Some(l) = label {
                        let g = self.gives(&t);
                        self.label(&l, Label::Here(ap.clone(), g), labels)?;
                    }
                    out.push(self.tree(&t, ap, labels, repeated)?);
                    i += used;
                    p.push(false);
                }
                if tail_out.is_none()
                    && let Some(t) = tail
                {
                    tail_out = Some(self.tree(&t, p, labels, repeated)?);
                }
                Ok(list_of(at, &out, tail_out))
            }
            V::Symbol(n) if self.named.contains_key(&n) => self.reference(s, n),
            V::Symbol(n) if self.name(n) == "place" => Ok(self.sym(s.at(), "dvar")),
            _ => Ok(*s),
        }
    }

    /// Whether list `s` is a syntax type's form, not a list of parts.
    fn is_form(&self, s: &Syn) -> bool {
        let Some(items) = s.list() else { return false };
        let head = items.first().and_then(|h| h.sym()).map(|h| self.name(h));
        match head.as_deref() {
            Some("many" | "literal" | "trailmark" | "oneof" | "union") => true,
            Some("expr" | "bvar" | "lambda") => items.get(1).is_some_and(|k| matches!(k.view(), V::Keyword(_))),
            _ => false,
        }
    }

    /// A syntax type's form: `(many σ)` its part a tree; the rest as written.
    fn form(&mut self, s: &Syn, path: Vec<bool>, labels: &mut HashMap<Sym, Label>, repeated: &mut Vec<(Vec<bool>, HashMap<Sym, Label>)>) -> R<Syn> {
        let items = s.list().expect("a list");
        match items[0].sym().map(|h| self.name(h)).as_deref() {
            Some("many") if items.len() == 2 => {
                let t = self.tree(&items[1], path, labels, repeated)?;
                Ok(Syn::lst(s.at(), vec![items[0], t]))
            }
            Some("union" | "oneof") => {
                let mut out = vec![self.sym(s.at(), "oneof")];
                for m in &items[1..] {
                    let mut none = HashMap::default();
                    out.push(self.tree(m, Vec::new(), &mut none, repeated)?);
                    if !none.is_empty() {
                        return Err(FxError::at(m.at(), "a label in a union's member that has no name: name the member, a node in a `letrec-shape`, whose facts may say it"));
                    }
                }
                Ok(Syn::lst(s.at(), out))
            }
            _ => Ok(*s),
        }
    }

    fn at_sign(&self, s: &Syn) -> bool {
        s.sym().is_some_and(|n| self.name(n) == "@")
    }

    fn dots(&self, s: &Syn) -> bool {
        s.sym().is_some_and(|n| self.name(n) == "...")
    }

    /// What a part of type `t` gives: a binder, itself; a part of a named
    /// shape, what its node exports.
    fn gives(&self, t: &Syn) -> Gives {
        match t.sym().map(|n| (n, self.interner.name(n))) {
            Some((_, "bvar")) => Gives::Var,
            Some((_, "dvar")) => Gives::Dvar,
            Some((_, "place")) => Gives::Place,
            Some((n, _)) if self.named.contains_key(&n) => self.named[&n].gives,
            _ => match t.list().and_then(|l| l.first().and_then(|h| h.sym())).map(|h| self.name(h)).as_deref() {
                Some("bvar") => Gives::Var,
                _ => Gives::Nothing,
            },
        }
    }

    fn label(&mut self, n: &Syn, l: Label, labels: &mut HashMap<Sym, Label>) -> R<()> {
        let name = n.sym().ok_or_else(|| FxError::at(n.at(), "a part's label is a name, `name @ σ`"))?;
        if labels.insert(name, l).is_some() {
            return Err(FxError::at(n.at(), format!("`{}` labels two parts", self.name(name))));
        }
        Ok(())
    }

    /// A named shape referred to: its node, or union, written once, `(mu
    /// name σ)`; inside its own writing, the `mu`'s variable.
    fn reference(&mut self, s: &Syn, n: Sym) -> R<Syn> {
        if self.open.contains(&n) {
            return Ok(*s);
        }
        self.open.push(n);
        let def = self.named[&n].def;
        let r = self.def_sigma(def);
        self.open.pop();
        let at = s.at();
        let mu = self.sym(at, "mu");
        Ok(Syn::lst(at, vec![mu, *s, r?]))
    }

    /// A node's or a union's syntax type: each member a region of its own,
    /// its facts its annotations; a union's members exporting one kind, one
    /// that says none an empty one.
    fn def_sigma(&mut self, def: Syn) -> R<Syn> {
        let items = def.list().ok_or_else(|| FxError::at(def.at(), "a node is `(node-name tree fact …)`"))?;
        if items.first().and_then(|h| h.sym()).is_some_and(|h| self.name(h) == "union") {
            let kind = self.def_gives(def)?;
            let mut out = vec![self.sym(def.at(), "oneof")];
            for m in &items[1..] {
                let mut t = self.node_sigma(*m)?;
                if kind != Gives::Nothing && self.def_gives(*m)? == Gives::Nothing {
                    let at = m.at();
                    let b = self.sym(at, if kind == Gives::Cage { "cage" } else { "rho" });
                    let ex = self.sym(at, "export");
                    t = Syn::lst(at, vec![ex, t, Syn::lst(at, vec![b])]);
                }
                out.push(t);
            }
            return Ok(Syn::lst(def.at(), out));
        }
        self.node_sigma(def)
    }

    fn node_sigma(&mut self, node: Syn) -> R<Syn> {
        let items = node.list().filter(|l| l.len() >= 2).ok_or_else(|| FxError::at(node.at(), "a node is `(node-name tree fact …)`"))?;
        let mut labels = HashMap::default();
        let sigma = self.tree(&items[1], Vec::new(), &mut labels, &mut Vec::new())?;
        self.facts(sigma, &items[2..], &labels, false, Vec::new())
    }

    /// Facts `fs` of a region whose labels are `labels`, on its syntax type
    /// `sigma`: each `bind` an import on the part it names, `export`s and
    /// `export*`s the region's export (none at a signature's top, `top`:
    /// what a use defines is said in what it makes); `pre`, what repeated
    /// elements export for what a use defines, first.
    fn facts(&mut self, sigma: Syn, fs: &[Syn], labels: &HashMap<Sym, Label>, top: bool, pre: Vec<(Vec<bool>, Syn)>) -> R<Syn> {
        let mut imports: Vec<(Vec<bool>, Syn)> = Vec::new();
        let mut rib: Vec<Syn> = Vec::new();
        let mut rings: Option<Vec<Syn>> = None;
        let mut elements: HashMap<Vec<bool>, Vec<Syn>> = HashMap::default();
        self.add_elements(&mut elements, pre);
        // Each repetition's facts, `(bind v in e) ...`: by the list's path,
        // the part's in the element, the binding.
        let mut each: Vec<(Vec<bool>, Vec<bool>, Syn)> = Vec::new();
        let mut i = 0;
        while i < fs.len() {
            let f = &fs[i];
            i += 1;
            if fs.get(i).is_some_and(|x| self.dots(x)) {
                if fs.get(i + 1).is_some_and(|x| self.dots(x)) {
                    return Err(FxError::at(fs[i + 1].at(), "a fact under more than one `...`: not yet"));
                }
                each.push(self.each_bound(f, labels)?);
                i += 1;
                continue;
            }
            let items = f.list().unwrap_or_default();
            let head = items.first().and_then(|h| h.sym()).map(|h| self.name(h));
            match (head.as_deref(), &items[..]) {
                (Some("bind"), [_, l, kw, m]) if kw.sym().is_some_and(|k| self.name(k) == "in") => {
                    let target = m.sym().and_then(|m| labels.get(&m).cloned()).ok_or_else(|| FxError::at(m.at(), "`(bind L in name)`: `name` a label of this node"))?;
                    let Label::Here(tp, _) = target else {
                        return Err(FxError::at(m.at(), "a fact binding in a repeated part is each repetition's: followed by `...`"));
                    };
                    let (b, adds) = self.bound(l, labels, false)?;
                    self.add_elements(&mut elements, adds);
                    imports.push((tp, b));
                }
                (Some("export"), [_, ls @ ..]) if !top => {
                    for l in ls {
                        let (entry, adds) = self.entry(l, labels, false)?;
                        self.add_elements(&mut elements, adds);
                        rib.push(entry);
                    }
                }
                (Some("export*"), [_, ls @ ..]) if !top => {
                    let mut rs = Vec::new();
                    for l in ls {
                        let (ring, adds) = self.entry(l, labels, true)?;
                        self.add_elements(&mut elements, adds);
                        rs.push(ring);
                    }
                    // Innermost first: the last written.
                    rs.reverse();
                    rings = Some(rs);
                }
                (Some("export" | "export*"), _) => return Err(FxError::at(f.at(), "what a use defines is said in what its signature makes, `(defn label …)`: the top node exports nothing")),
                _ => return Err(FxError::at(f.at(), "a fact is `(bind L in name)`, `(export L …)` or `(export* L …)`")),
            }
        }
        let mut sigma = sigma;
        // Each repetition's facts, inside its element; then each element
        // exporting what a fact says of its labels.
        for (lp, tp, b) in each {
            sigma = self.annotate_in_element(sigma, &lp, &tp, b)?;
        }
        for (ep, entries) in elements {
            sigma = self.annotate_element(sigma, &ep, entries)?;
        }
        for (tp, b) in imports {
            sigma = self.annotate(sigma, &tp, "import", b)?;
        }
        let at = sigma.at();
        if !rib.is_empty() && rings.is_some() {
            return Err(FxError::at(at, "a node exports one level, `export`, or nested ones, `export*`, not both"));
        }
        if !rib.is_empty() {
            let rho = self.sym(at, "rho");
            let b = Syn::lst(at, std::iter::once(rho).chain(rib).collect());
            sigma = self.annotate(sigma, &[], "export", b)?;
        } else if let Some(rs) = rings {
            let cage = self.sym(at, "cage");
            let b = Syn::lst(at, std::iter::once(cage).chain(rs).collect());
            sigma = self.annotate(sigma, &[], "export", b)?;
        }
        Ok(sigma)
    }

    /// What repeated elements must export, `adds`, by the list's path,
    /// onto `elements`: each entry once, however many facts name `(v ...)`.
    fn add_elements(&self, elements: &mut HashMap<Vec<bool>, Vec<Syn>>, adds: Vec<(Vec<bool>, Syn)>) {
        for (ep, e) in adds {
            let es = elements.entry(ep).or_default();
            let w = e.written(self.interner);
            if !es.iter().any(|x| x.written(self.interner) == w) {
                es.push(e);
            }
        }
    }

    /// A fact under `...`, `(bind v in e) ...`, each repetition's: `v` and
    /// `e` labels of one list's element, each the repetition's own; the
    /// list's path, `e`'s in the element, and what it imports there,
    /// addressed from the element's root. One that names what is outside
    /// its repetition (every repetition's, `(v ...)`, or a label around the
    /// list) needs an import from an outer region's root: not yet (§289).
    fn each_bound(&mut self, f: &Syn, labels: &HashMap<Sym, Label>) -> R<(Vec<bool>, Vec<bool>, Syn)> {
        let items = f.list().unwrap_or_default();
        let (l, m) = match &items[..] {
            [h, l, kw, m] if h.sym().is_some_and(|h| self.name(h) == "bind") && kw.sym().is_some_and(|k| self.name(k) == "in") => (*l, *m),
            _ => return Err(FxError::at(f.at(), "a fact under `...` is a `bind`, each repetition's: what a list exports is every repetition's, `(export (x ...))`")),
        };
        let outside = |at: &Syn| FxError::at(at.at(), "a fact under `...` that names what is outside its repetition: not yet (TODO §289)");
        let repeated = |x: &Syn, this: &Self| -> R<(Sym, Vec<bool>, Vec<bool>, Gives)> {
            let n = x.sym().ok_or_else(|| outside(x))?;
            match labels.get(&n) {
                Some(Label::Repeated(lp, ep, g)) => Ok((n, lp.clone(), ep.clone(), *g)),
                Some(Label::Here(..)) => Err(outside(x)),
                None => Err(FxError::at(x.at(), format!("`{}` labels no part of this node", this.name(n)))),
            }
        };
        let (ln, llp, lep, g) = repeated(&l, self)?;
        let (_, mlp, mep, _) = repeated(&m, self)?;
        if llp != mlp {
            return Err(FxError::at(f.at(), "a fact under `...` names one list's repetition: these are of two lists"));
        }
        if g == Gives::Nothing {
            return Err(FxError::at(l.at(), format!("`{}` labels a part that binds nothing", self.name(ln))));
        }
        let at = f.at();
        let b = if g == Gives::Cage {
            let (cage, a) = (self.sym(at, "cage"), self.sym(at, "at"));
            let p = self.path(at, &lep);
            Syn::lst(at, vec![cage, Syn::lst(at, vec![a, p])])
        } else {
            let rho = self.sym(at, "rho");
            let e = self.rib_entry(at, &lep, g)?;
            Syn::lst(at, vec![rho, e])
        };
        Ok((llp, mep, b))
    }

    /// `sigma` with the part at `path` of the repeated element of the list
    /// at `list` imported `b`, addressed from the element's root.
    fn annotate_in_element(&mut self, sigma: Syn, list: &[bool], path: &[bool], b: Syn) -> R<Syn> {
        let at = sigma.at();
        let Some((first, rest)) = list.split_first() else {
            let (elem, dots) = sigma.split().ok_or_else(|| FxError::at(at, "a repeated part not found in its tree"))?;
            let elem = self.annotate(elem, path, "import", b)?;
            return Ok(cons(at, elem, dots));
        };
        let (car, cdr) = sigma.split().ok_or_else(|| FxError::at(at, "a repeated part not found in its tree"))?;
        let (car, cdr) = if *first { (self.annotate_in_element(car, rest, path, b)?, cdr) } else { (car, self.annotate_in_element(cdr, rest, path, b)?) };
        Ok(cons(at, car, cdr))
    }

    /// What `(bind L in …)` imports: one level of `L`'s, a ribcage if it
    /// gives one.
    fn bound(&mut self, l: &Syn, labels: &HashMap<Sym, Label>, _nested: bool) -> R<(Syn, Vec<(Vec<bool>, Syn)>)> {
        let at = l.at();
        let (entry, adds) = self.entry(l, labels, false).or_else(|e| match self.entry(l, labels, true) {
            Ok(r) => Ok(r),
            Err(_) => Err(e),
        })?;
        let cage_like = entry.list().and_then(|x| x.first().and_then(|h| h.sym())).is_some_and(|h| self.name(h) == "at");
        let b = if cage_like {
            let cage = self.sym(at, "cage");
            Syn::lst(at, vec![cage, entry])
        } else {
            let rho = self.sym(at, "rho");
            Syn::lst(at, vec![rho, entry])
        };
        Ok((b, adds))
    }

    /// `L`, a label or `(label ...)`, as a rib's entry `(path δ)`, or, in a
    /// ribcage (`ring`), a ring: `(rho (path δ))` or `(at path)`; and what
    /// each repeated element must export for it, by the list's path.
    fn entry(&mut self, l: &Syn, labels: &HashMap<Sym, Label>, ring: bool) -> R<(Syn, Vec<(Vec<bool>, Syn)>)> {
        let at = l.at();
        let (name, repeated) = match l.list().as_deref() {
            Some([n, d]) if self.dots(d) => (n.sym(), true),
            _ => (l.sym(), false),
        };
        let name = name.ok_or_else(|| FxError::at(at, "a fact names a label, or `(label ...)`, every repetition's"))?;
        let label = labels.get(&name).cloned().ok_or_else(|| FxError::at(at, format!("`{}` labels no part of this node", self.name(name))))?;
        let mut adds = Vec::new();
        let (path, gives) = match (label, repeated) {
            (Label::Here(p, g), false) => (p, g),
            (Label::Repeated(lp, ep, g), true) => {
                // Each element exports it; the list, every element's.
                if g != Gives::Nothing {
                    let e = self.rib_entry(at, &ep, g)?;
                    adds.push((lp.clone(), e));
                }
                (lp, Gives::Rib)
            }
            (Label::Here(..), true) => return Err(FxError::at(at, format!("`{}` is not repeated: named alone, not `({0} ...)`", self.name(name)))),
            (Label::Repeated(..), false) => return Err(FxError::at(at, format!("`{}` is a repeated part's: `({0} ...)`, every repetition's, or a fact under `...`, each repetition's", self.name(name)))),
        };
        if gives == Gives::Nothing {
            return Err(FxError::at(at, format!("`{}` labels a part that binds nothing", self.name(name))));
        }
        let e = if ring {
            if gives == Gives::Cage {
                let a = self.sym(at, "at");
                let p = self.path(at, &path);
                Syn::lst(at, vec![a, p])
            } else {
                let rho = self.sym(at, "rho");
                let e = self.rib_entry(at, &path, gives)?;
                Syn::lst(at, vec![rho, e])
            }
        } else if gives == Gives::Cage {
            let a = self.sym(at, "at");
            let p = self.path(at, &path);
            Syn::lst(at, vec![a, p])
        } else {
            self.rib_entry(at, &path, gives)?
        };
        Ok((e, adds))
    }

    fn rib_entry(&mut self, at: At, path: &[bool], g: Gives) -> R<Syn> {
        let d = match g {
            Gives::Var => "var",
            Gives::Dvar => "dvar",
            Gives::Place => "place",
            Gives::Rib => "rib",
            Gives::Cage => return Err(FxError::at(at, "a ribcage at one level: `export*`, nested")),
            Gives::Nothing => "none",
        };
        let p = self.path(at, path);
        let d = self.sym(at, d);
        Ok(Syn::lst(at, vec![p, d]))
    }

    /// `(path #:a #:d …)`, or `()`.
    fn path(&mut self, at: At, path: &[bool]) -> Syn {
        if path.is_empty() {
            return Syn::nil(at);
        }
        let mut items = vec![self.sym(at, "path")];
        for s in path {
            let k = self.interner.intern(if *s { "a" } else { "d" });
            items.push(Syn::new(at, V::Keyword(k), self.interner));
        }
        Syn::lst(at, items)
    }

    /// `sigma` with the part at `path` annotated, `(how part b)`.
    fn annotate(&mut self, sigma: Syn, path: &[bool], how: &str, b: Syn) -> R<Syn> {
        let at = sigma.at();
        let Some((first, rest)) = path.split_first() else {
            let h = self.sym(at, how);
            return Ok(Syn::lst(at, vec![h, sigma, b]));
        };
        let (car, cdr) = sigma.split().ok_or_else(|| FxError::at(at, "a label's part not found in its tree"))?;
        let (car, cdr) = if *first { (self.annotate(car, rest, how, b)?, cdr) } else { (car, self.annotate(cdr, rest, how, b)?) };
        Ok(cons(at, car, cdr))
    }

    /// `sigma` with the repeated element of the list at `path` exporting
    /// `entries`, one rib.
    fn annotate_element(&mut self, sigma: Syn, path: &[bool], entries: Vec<Syn>) -> R<Syn> {
        let at = sigma.at();
        let Some((first, rest)) = path.split_first() else {
            // The list: `(elem ...)`.
            let (elem, dots) = sigma.split().ok_or_else(|| FxError::at(at, "a repeated part not found in its tree"))?;
            let rho = self.sym(at, "rho");
            let b = Syn::lst(at, std::iter::once(rho).chain(entries).collect());
            let ex = self.sym(at, "export");
            let elem = Syn::lst(at, vec![ex, elem, b]);
            return Ok(cons(at, elem, dots));
        };
        let (car, cdr) = sigma.split().ok_or_else(|| FxError::at(at, "a repeated part not found in its tree"))?;
        let (car, cdr) = if *first { (self.annotate_element(car, rest, entries)?, cdr) } else { (car, self.annotate_element(cdr, rest, entries)?) };
        Ok(cons(at, car, cdr))
    }

    /// `MADE`: `(defn D …)` Herman's, each label its path, `(label ...)`
    /// every repetition's, the list's rib; and what each repeated element
    /// must export for it, by the list's path.
    fn made(&mut self, m: &Syn, labels: &HashMap<Sym, Label>) -> R<(Syn, Vec<(Vec<bool>, Syn)>)> {
        let Some(items) = m.list() else { return Ok((*m, Vec::new())) };
        if !items.first().and_then(|h| h.sym()).is_some_and(|h| self.name(h) == "defn") {
            return Ok((*m, Vec::new()));
        }
        let mut out = vec![items[0]];
        let mut adds = Vec::new();
        for d in &items[1..] {
            // `(label ...)`: every repetition's, as a fact names it.
            if let Some([n, dots]) = d.list().as_deref()
                && self.dots(dots)
            {
                if n.sym().is_none() {
                    return Err(FxError::at(d.at(), "every repetition's macro binder, `((label (macro …)) ...)`: not yet"));
                }
                let (e, more) = self.entry(d, labels, false)?;
                adds.extend(more);
                out.push(e);
                continue;
            }
            let (n, sig) = match d.list().as_deref() {
                Some([n, sig]) => (*n, Some(*sig)),
                _ => (*d, None),
            };
            let name = n.sym().ok_or_else(|| FxError::at(n.at(), "what a use defines is a label, `(label ...)` or `(label (macro …))`"))?;
            let (p, g) = match labels.get(&name).cloned() {
                Some(Label::Here(p, g)) => (p, g),
                Some(Label::Repeated(..)) => return Err(FxError::at(n.at(), format!("`{0}` is a repeated part's: `({0} ...)`, every repetition's", self.name(name)))),
                None => return Err(FxError::at(n.at(), format!("`{}` labels no part of this signature's top", self.name(name)))),
            };
            let at = d.at();
            let path = self.path(at, &p);
            // A macro's binder: its signature as written, read where it is
            // (`Macros::signature`), and said so.
            let delta = match sig {
                Some(s) => s,
                None => {
                    let e = self.rib_entry(at, &p, g)?;
                    out.push(e);
                    continue;
                }
            };
            out.push(Syn::lst(at, vec![path, delta]));
        }
        Ok((Syn::lst(m.at(), out), adds))
    }
}

/// Items `items` and `tail` as one list: none, the tail itself.
fn list_of(at: At, items: &[Syn], tail: Option<Syn>) -> Syn {
    match (items, tail) {
        ([], Some(t)) => t,
        _ => Syn::of_list(at, items, tail),
    }
}

/// `(car . cdr)`, a list's parts kept a list.
fn cons(at: At, car: Syn, cdr: Syn) -> Syn {
    match cdr.view() {
        V::List { items, tail } => {
            let mut all = vec![car];
            all.extend(items.iter().copied());
            Syn::of_list(at, &all, tail)
        }
        V::Nil => Syn::lst(at, vec![car]),
        _ => Syn::of_list(at, &[car], Some(cdr)),
    }
}
