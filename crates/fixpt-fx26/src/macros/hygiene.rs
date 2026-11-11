//! Hygiene, one mechanism (`docs/research/binding-shapes.md`, step 3):
//! after a form is expanded, each name an expansion introduced and left
//! free, an alias `%~N:x` (`procedural::alias_base`), made the name it
//! stands for where its macro is defined (`DefEnv`), by the program's walk:
//! a top-level macro's, the top level's `x`, written so (`(with #%toplevel
//! x)`, `#%toplevel:x`); a file's macro's, the file's value `(with
//! %shared:key x)` or else the standard one, `(with #%fx x)`: none of
//! which anything around it captures. An alias the expansion bound, here
//! or at the top level before, is a name of its own, and stays. No alias
//! reaches the checkers.

use super::procedural::{alias_base, alias_made};
use super::{Aligner, Atom, Env, Free, Kids, Level, Macros, Mode, Ns, STy};
use crate::error::R;
use fixpt_read::{Datum, Interner, Sym, Syntax};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Where a macro is defined, what its expansions' aliases are read in: the
/// top level; a file, `%shared:key` the hidden global every load of it is
/// and the values its module shows (its other names the standard
/// environment's, which a file's macro's check has held them to).
/// Or a module file's items, as the file's own macros see them, which no
/// qualifier names: an alias becomes the plain name, and a binder at the
/// use that would capture it is renamed (`Checker::file_own_expanded`).
#[derive(Clone, Debug, Default)]
pub(crate) enum DefEnv {
    #[default]
    Top,
    File { shared: Sym, values: Rc<HashSet<Sym>> },
    Within,
}

/// What an alias is written as: the top level's value or qualified name, or
/// a value of a module's (`(with m x)`).
enum Made {
    TopValue(String),
    TopDesc(String),
    Of(Sym, String),
    Plain(String),
}

impl Macros {
    /// Form `form`, a top-level form after expansion, its free aliases
    /// made the names they stand for (above); itself if it has none.
    pub(crate) fn aliases_resolved(&mut self, form: &Syntax, interner: &mut Interner) -> R<Syntax> {
        if !has_alias(form, interner) {
            return Ok(form.clone());
        }
        self.ensure_kernel(interner)?;
        let fx = interner.intern("#%fx");
        let none = HashMap::new();
        let mut parts: Vec<(Vec<bool>, fixpt_read::Span, Made)> = Vec::new();
        let mut made: Vec<(usize, Made)> = Vec::new();
        let mut defined = Vec::new();
        let mut next_fresh = self.withs.captors;
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
            // The binder a name `n` refers to in `env`, innermost first; or
            // whether a module's names come first, which may have it.
            let innermost = |env: &Env, n: Sym, ns: Ns| -> Result<Option<usize>, ()> {
                for level in env.levels() {
                    match level {
                        Level::Rib(atoms) | Level::Earlier(atoms) => {
                            if let Some(b) = binder_named(atoms, n, ns) {
                                return Ok(Some(b));
                            }
                        }
                        Level::Shape(_) => return Err(()),
                        Level::Cage(_) => {}
                    }
                }
                Ok(None)
            };
            // The binders at uses that would capture a name a file's own
            // macro introduces.
            let mut captors: HashSet<usize> = HashSet::new();
            for (at, env, _, _) in &found {
                let Kids::Ref(n, ns, free) = a.nodes[*at].kids else { continue };
                let Some(base) = alias_base(a.name(n)) else { continue };
                let def_env = alias_made(a.name(n)).and_then(|k| a.m.withs.def_envs.get(&k));
                // Bound by the expansion, here or at the top level before.
                let bound = env.levels().any(|l| matches!(l, Level::Rib(atoms) | Level::Earlier(atoms) if binder_named(atoms, n, ns).is_some()));
                let global = !matches!(def_env, Some(DefEnv::Within)) && a.m.withs.shapes.top_has(n, ns == Ns::Desc);
                if bound || global {
                    continue;
                }
                // Where its macro is defined: so written, which nothing
                // around it captures; in a file's own, the plain name, its
                // captor at the use renamed.
                let m = match def_env {
                    Some(DefEnv::Within) => {
                        let captor = match a.interner.get(base) {
                            Some(x) => innermost(env, x, ns),
                            None => Ok(None),
                        };
                        match captor {
                            Ok(Some(b)) if !top.contains(&b) => {
                                captors.insert(b);
                            }
                            Ok(_) => {}
                            Err(()) => {
                                let span = a.nodes[*at].syn.span;
                                return Err(crate::error::FxError::at(span, format!("`{base}`, which a macro of this file names, where a `with` or `include` around its use may give it: not yet")));
                            }
                        }
                        Made::Plain(base.to_string())
                    }
                    None | Some(DefEnv::Top) => top_made(free, ns, base),
                    Some(DefEnv::File { shared, values }) => match free {
                        Free::Toplevel if a.interner.get(base).is_some_and(|v| values.contains(&v)) => Made::Of(*shared, base.to_string()),
                        Free::Toplevel => Made::Of(fx, base.to_string()),
                        Free::Plain => Made::Plain(base.to_string()),
                        // A file's macro writes its descriptions through
                        // its module whole (`Action::ModuleType`).
                        _ => return Err(crate::error::FxError::at(a.nodes[*at].syn.span, format!("`{base}`: a file's macro's description named apart from its module, not yet"))),
                    },
                };
                made.push((*at, m));
            }
            // Each captor renamed, and each reference to it.
            if !captors.is_empty() {
                let mut fresh: HashMap<usize, String> = HashMap::new();
                let mut sorted: Vec<usize> = captors.iter().copied().collect();
                sorted.sort_by(|x, y| a.nodes[*x].path.iter().map(|s| !s).cmp(a.nodes[*y].path.iter().map(|s| !s)));
                for b in sorted {
                    let Kids::Binder(n, _) = a.nodes[b].kids else { unreachable!("a binder") };
                    next_fresh += 1;
                    // Spelled apart from a template's fresh names, `%x:N`,
                    // and counted apart, as the FX-26 one counts them.
                    fresh.insert(b, format!("%{}~{}", a.name(n), next_fresh));
                }
                for (at, env, _, _) in &found {
                    let Kids::Ref(n, ns, _) = a.nodes[*at].kids else { continue };
                    if alias_base(a.name(n)).is_none()
                        && let Ok(Some(b)) = innermost(env, n, ns)
                        && let Some(f) = fresh.get(&b)
                    {
                        made.push((*at, Made::Plain(f.clone())));
                    }
                }
                made.extend(fresh.into_iter().map(|(b, f)| (b, Made::Plain(f))));
            }
            let at = |k: usize| (a.nodes[k].path.clone(), a.nodes[k].syn.span);
            for (r, m) in made {
                let (p, sp) = at(r);
                parts.push((p, sp, m));
            }
        }
        self.withs.captors = next_fresh;
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
                Made::Plain(n) => Syntax::symbol(span, interner.intern(&n)),
                Made::Of(m, n) => {
                    let n = interner.intern(&n);
                    Syntax::list(span, vec![Syntax::symbol(span, with), Syntax::symbol(span, m), Syntax::symbol(span, n)])
                }
            };
            written.insert(p, s);
        }
        Ok(written_at(form, &mut Vec::new(), &written))
    }
}

/// The top level's `base`, written as `free` says: a value, `(with
/// #%toplevel base)`; qualified (a description's name, a specification's),
/// `#%toplevel:base`; as written (a global's, which nothing shadows); a
/// `with`'s module, by its namespace `ns`.
fn top_made(free: Free, ns: Ns, base: &str) -> Made {
    match (free, ns) {
        (Free::Toplevel, _) | (Free::Bound, Ns::Value) => Made::TopValue(base.to_string()),
        (Free::Qualified, _) | (Free::Bound, Ns::Desc) => Made::TopDesc(base.to_string()),
        (Free::Plain, _) => Made::Plain(base.to_string()),
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
