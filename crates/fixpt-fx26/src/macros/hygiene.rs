//! Hygiene, one mechanism (`docs/research/binding-shapes.md`, step 3):
//! after a form is expanded, each name an expansion introduced and left
//! free, an alias `%~N:x` (`procedural::alias_base`), made the name it
//! stands for where its macro is defined, by the program's walk: a
//! top-level macro's, the top level's `x`, written so (`(with #%toplevel
//! x)`, `#%toplevel:x`), which nothing around it captures. An alias the
//! expansion bound, here or at the top level before, is a name of its own,
//! and stays. No alias reaches the checkers.

use super::procedural::alias_base;
use super::{Aligner, Atom, Env, Kids, Level, Macros, Mode, Ns, STy};
use crate::error::R;
use fixpt_read::{Datum, Interner, Sym, Syntax};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// What an alias is written as: the top level's value or description.
enum Made {
    TopValue(String),
    TopDesc(String),
}

impl Macros {
    /// Form `form`, a top-level form after expansion, its free aliases
    /// made the names they stand for (above); itself if it has none.
    pub(crate) fn aliases_resolved(&mut self, form: &Syntax, interner: &mut Interner) -> R<Syntax> {
        if !has_alias(form, interner) {
            return Ok(form.clone());
        }
        self.ensure_kernel(interner)?;
        let none = HashMap::new();
        let mut parts: Vec<(Vec<bool>, fixpt_read::Span, Made)> = Vec::new();
        let mut made: Vec<(usize, Made)> = Vec::new();
        let mut defined = Vec::new();
        {
            let mut a = Aligner { m: self, interner, mode: Mode::Program, pvars: &none, nodes: Vec::new(), unplaced: Vec::new(), work: Vec::new() };
            let root = a.align(&Rc::new(STy::Item), form, None, Vec::new())?;
            let mut found = Vec::new();
            a.walk(root, &Env::default(), false, 0, &mut found, &mut Vec::new())?;
            // What the form's definitions bind, the top level's.
            let mut top = HashSet::new();
            if let Kids::Form(x) = a.nodes[root].kids
                && let Some((b, r)) = &a.nodes[x].export
            {
                for level in a.eval(b, *r, form.span)? {
                    if let Level::Rib(atoms) = level {
                        top.extend(atoms.iter().filter_map(|x| if let Atom::Lit(t, _) = x { Some(*t) } else { None }));
                    }
                }
            }
            // The aliases it defines at the top level: names of their own.
            for b in &top {
                if let Kids::Binder(n, d) = a.nodes[*b].kids
                    && alias_base(a.name(n)).is_some()
                {
                    defined.push((n, d == Ns::Desc));
                }
            }
            let binder_named = |atoms: &[Atom], n: Sym, ns: Ns| {
                atoms.iter().find_map(|x| match x {
                    Atom::Lit(b, m) if *m == ns && matches!(a.nodes[*b].kids, Kids::Binder(k, _) if k == n) => Some(*b),
                    _ => None,
                })
            };
            for (at, env, _, _) in &found {
                let Kids::Ref(n, ns, _) = a.nodes[*at].kids else { continue };
                let Some(base) = alias_base(a.name(n)) else { continue };
                // Bound by the expansion, here or at the top level before.
                let bound = env.levels().any(|l| matches!(l, Level::Rib(atoms) | Level::Earlier(atoms) if binder_named(atoms, n, ns).is_some()));
                let global = a.m.withs.shapes.top_has(n, ns == Ns::Desc);
                if bound || global {
                    continue;
                }
                // The top level's, where a top-level macro is defined: so
                // written, which nothing around it captures.
                made.push((*at, top_made(ns, base)));
            }
            let at = |k: usize| (a.nodes[k].path.clone(), a.nodes[k].syn.span);
            for (r, m) in made {
                let (p, sp) = at(r);
                parts.push((p, sp, m));
            }
        }
        self.withs.shapes.aliases_defined.extend(defined);
        let (with, toplevel) = (interner.intern("with"), interner.intern("#%toplevel"));
        let mut written: HashMap<Vec<bool>, Syntax> = HashMap::new();
        for (p, span, m) in parts {
            let s = match m {
                Made::TopDesc(n) => Syntax::symbol(span, interner.intern(&format!("#%toplevel:{n}"))),
                Made::TopValue(n) => {
                    let n = interner.intern(&n);
                    Syntax::list(span, vec![Syntax::symbol(span, with), Syntax::symbol(span, toplevel), Syntax::symbol(span, n)])
                }
            };
            written.insert(p, s);
        }
        Ok(written_at(form, &mut Vec::new(), &written))
    }
}

/// The top level's `base`, a value or (`ns`) a description, so written.
fn top_made(ns: Ns, base: &str) -> Made {
    match ns {
        Ns::Desc => Made::TopDesc(base.to_string()),
        Ns::Value => Made::TopValue(base.to_string()),
    }
}

/// Whether `s` holds an alias, outside quotes.
fn has_alias(s: &Syntax, interner: &Interner) -> bool {
    match &s.datum {
        Datum::Symbol(x) => alias_base(interner.name(*x)).is_some(),
        Datum::List { items, tail } => {
            let quoted = items.first().and_then(|h| h.as_symbol()).is_some_and(|h| matches!(interner.name(h), "quote" | "quasiquote" | "%datum"));
            !quoted && (items.iter().any(|i| has_alias(i, interner)) || tail.as_ref().is_some_and(|t| has_alias(t, interner)))
        }
        _ => false,
    }
}

/// `s`, at `path`, with each part `written` holds at its path written so.
fn written_at(s: &Syntax, path: &mut Vec<bool>, written: &HashMap<Vec<bool>, Syntax>) -> Syntax {
    if let Some(w) = written.get(path) {
        return w.clone();
    }
    match &s.datum {
        Datum::List { items, tail } => {
            let depth = path.len();
            let mut out = Vec::with_capacity(items.len());
            for i in items {
                path.push(true);
                out.push(written_at(i, path, written));
                path.pop();
                path.push(false);
            }
            let tail = tail.as_ref().map(|t| Box::new(written_at(t, path, written)));
            path.truncate(depth);
            Syntax::new(s.span, Datum::List { items: out, tail })
        }
        _ => s.clone(),
    }
}
