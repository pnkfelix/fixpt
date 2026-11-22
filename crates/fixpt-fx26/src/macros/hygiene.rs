//! Hygiene, one mechanism (`docs/research/binding-shapes.md`, step 3):
//! after a form is expanded, each name an expansion introduced and left
//! free, an alias `%~K.N:x` (`procedural::alias_base`), made the name it
//! stands for where its macro is defined (`DefEnv`), by the program's walk:
//! a top-level macro's, the top level's `x`, written so (`(with #%toplevel
//! x)`, `#%toplevel:x`); a file's macro's, the file's value `(with
//! %shared:key x)` or else the standard one, `(with #%fx x)`: none of
//! which anything around it captures. An alias the expansion bound, here
//! or at the top level before, is a name of its own, and stays. No alias
//! reaches the checkers.

use super::procedural::{alias_base, alias_made};
use super::{Aligner, Atom, Env, Free, Kids, Level, Macros, Ns, STy};
use super::paths::Path;
use crate::error::R;
use fixpt_read::{Interner, Sym};
use crate::heap_syn::{At, Syn, V};
use fixpt_hash::{HashMap, HashSet};
use std::rc::Rc;

/// Where a macro is defined, what its expansions' aliases are read in: the
/// top level; a file, `%shared:key` the hidden global every load of it is
/// and the values its module shows (its other names the standard
/// environment's, which a file's macro's check has held them to); or, if
/// `instance`, the importer's instance of the file in place of `%shared:key`
/// (`binding-shapes.md`, step 4 (c)), a binder at the use that would
/// capture its name renamed, as for a module file's items below; an
/// instance a path names, `env::m` (`import-with-syntax` of one), is
/// written as its `with`s (`super::module_named`), the path's first name
/// the one a binder at the use is kept from capturing.
/// Or a module file's items, as the file's own macros see them, which no
/// qualifier names: an alias becomes the plain name, and a binder at the
/// use that would capture it is renamed (`Checker::file_own_expanded`).
#[derive(Clone, Debug, Default)]
pub(crate) enum DefEnv {
    #[default]
    Top,
    /// And, `internal`, each of the file's macros, by its name there, as
    /// its importer has it (`%syntax:key:name`): what a transformer's
    /// renamed name that is one means (`Macros::procedural_opened`).
    /// And `frame`, the file's frame, whose values a name it does not show
    /// that its macros write reaches, `(with (with shared frame) x)`, before
    /// any standard one (`TODO.md` §300).
    File { shared: Sym, values: Rc<HashSet<Sym>>, instance: bool, internal: Rc<HashMap<Sym, Sym>>, frame: super::Frame },
    Within,
}

/// What an alias is written as: the top level's value or qualified name, or
/// a value of a module's (`(with m x)`).
enum Made {
    TopValue(String),
    TopDesc(String),
    Of(Sym, String),
    /// A value of a module's frame, `(with (with m frame) x)`.
    Framed(Sym, Sym, String),
    Plain(String),
    /// A module, an instance's name or path, as an expression.
    Module(Sym),
}

impl Macros {
    /// Form `form`, a top-level form after expansion, its free aliases
    /// made the names they stand for (above); itself if it has none.
    pub(crate) fn aliases_resolved(&mut self, form: &Syn, interner: &mut Interner) -> R<Syn> {
        if !has_alias(form, interner) {
            return Ok(form.clone());
        }
        self.ensure_kernel(interner)?;
        let fx = interner.intern("#%fx");
        let none = HashMap::default();
        let mut parts: Vec<(Path, At, Made)> = Vec::new();
        let mut made: Vec<(usize, Made)> = Vec::new();
        let mut defined = Vec::new();
        let mut next_fresh = self.withs.captors;
        let key = self.withs.form_key.clone();
        {
            let (a, root, found, _) = Aligner::program(self, interner, &none, &Rc::new(STy::Item), form, false, &HashSet::default())?;
            // What the form's definitions bind, the top level's.
            let mut top = HashSet::default();
            if let Kids::Form(x) = a.nodes[root].kids
                && let Some((b, r)) = &a.nodes[x].export
            {
                for level in a.eval(b, *r, form.at())? {
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
            let mut captors: HashSet<usize> = HashSet::default();
            for (at, env, _, _) in &found {
                let Kids::Ref(n, ns, free) = a.nodes[*at].kids else { continue };
                let Some(base) = alias_base(a.name(n)) else { continue };
                let def_env = alias_made(a.name(n)).and_then(|k| a.m.withs.def_envs.get(k));
                // Bound by the expansion, here or at the top level before.
                let bound = env.levels().any(|l| matches!(l, Level::Rib(atoms) | Level::Earlier(atoms) if binder_named(atoms, n, ns).is_some()));
                let global = !matches!(def_env, Some(DefEnv::Within)) && a.m.withs.shapes.top_has(n, ns == Ns::Desc);
                if bound || global {
                    continue;
                }
                // Where its macro is defined: so written, which nothing
                // around it captures; in a file's own, the plain name, its
                // captor at the use renamed.
                // A binder at the use that would capture `x`, a value's or
                // `ns`'s, which the macro's expansion names as written:
                // noted, to be renamed.
                // Refused where a module's names come first, which may give
                // it: at the alias, in a module file; an instance's, at the
                // form, the alias in another file's text.
                let mut captured = |x: Sym, ns: Ns, inst: bool| -> R<()> {
                    match innermost(env, x, ns) {
                        // A `module`'s item, whose name is its label too, is
                        // not renamed: that would change what the module gives.
                        Ok(Some(b)) if !top.contains(&b) && within_module(form, &a.nodes[b].path.steps(), a.interner) => {
                            let span = if inst { form.at() } else { a.nodes[*at].syn.at() };
                            return Err(crate::error::FxError::at(span, format!("`{}`, which an expansion here names as its macro has it, is bound inside a `module` around the use, where renaming it may change what the module gives: not yet", a.interner.name(x))));
                        }
                        Ok(Some(b)) if !top.contains(&b) => {
                            captors.insert(b);
                        }
                        Ok(_) => {}
                        Err(()) => {
                            let (span, what) = if inst { (form.at(), "the instance an imported macro names") } else { (a.nodes[*at].syn.at(), "which a macro of this file names") };
                            return Err(crate::error::FxError::at(span, format!("`{}`, {what}, where a `with` or `include` around its use may give it: not yet", a.interner.name(x))));
                        }
                    }
                    Ok(())
                };
                let m = match def_env {
                    Some(DefEnv::Within) => {
                        if let Some(x) = a.interner.get(base) {
                            captured(x, ns, false)?;
                        }
                        Made::Plain(base.to_string())
                    }
                    None | Some(DefEnv::Top) => top_made(free, ns, base),
                    // An instance's value, `(with lib name)`, and its name
                    // as a type's module, `(select lib T)` (`InstanceType`):
                    // `lib` the importer's, which nothing at the use captures.
                    Some(DefEnv::File { shared, values, instance: true, .. }) if free == Free::Toplevel && a.interner.get(base).is_some_and(|v| values.contains(&v)) => {
                        captured(super::path_root(*shared, a.interner), Ns::Value, true)?;
                        Made::Of(*shared, base.to_string())
                    }
                    Some(DefEnv::File { shared, instance: true, frame: frame @ Some(f), .. }) if free == Free::Toplevel && a.interner.get(base).is_some_and(|v| super::frame_holds(frame, v)) => {
                        captured(super::path_root(*shared, a.interner), Ns::Value, true)?;
                        Made::Framed(*shared, f.name, base.to_string())
                    }
                    Some(DefEnv::File { shared, instance: true, .. }) if free == Free::Qualified && a.interner.get(base) == Some(*shared) => {
                        captured(super::path_root(*shared, a.interner), Ns::Value, true)?;
                        Made::Module(*shared)
                    }
                    Some(DefEnv::File { shared, values, frame, .. }) => match free {
                        Free::Toplevel if a.interner.get(base).is_some_and(|v| values.contains(&v)) => Made::Of(*shared, base.to_string()),
                        Free::Toplevel if let Some(f) = frame.as_ref().filter(|_| a.interner.get(base).is_some_and(|v| super::frame_holds(frame, v))) => Made::Framed(*shared, f.name, base.to_string()),
                        Free::Toplevel => Made::Of(fx, base.to_string()),
                        Free::Plain => Made::Plain(base.to_string()),
                        // A file's macro writes its descriptions through
                        // its module whole (`Action::ModuleType`).
                        _ => return Err(crate::error::FxError::at(a.nodes[*at].syn.at(), format!("`{base}`: a file's macro's description named apart from its module, not yet"))),
                    },
                };
                made.push((*at, m));
            }
            // Each captor renamed, and each reference to it.
            if !captors.is_empty() {
                let mut fresh: HashMap<usize, String> = HashMap::default();
                let mut sorted: Vec<usize> = captors.iter().copied().collect();
                super::sort_by_path(&mut sorted, |x| a.nodes[x].path, form);
                for b in sorted {
                    let Kids::Binder(n, _) = a.nodes[b].kids else { unreachable!("a binder") };
                    next_fresh += 1;
                    // Spelled apart from a template's fresh names, `%x:K.N`,
                    // and counted apart, as the FX-26 one counts them.
                    fresh.insert(b, format!("%{}~{key}.{next_fresh}", a.name(n)));
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
            let at = |k: usize| (a.nodes[k].path, a.nodes[k].syn.at());
            for (r, m) in made {
                let (p, sp) = at(r);
                parts.push((p, sp, m));
            }
        }
        self.withs.captors = next_fresh;
        self.withs.shapes.aliases_defined.extend(defined);
        let (with, toplevel) = (interner.intern("with"), interner.intern("#%toplevel"));
        let mut written: HashMap<Path, Syn> = HashMap::default();
        for (p, span, m) in parts {
            let s = match m {
                Made::TopDesc(n) => Syn::named(span, &format!("#%toplevel:{n}"), interner),
                Made::TopValue(n) => {
                    let n = interner.intern(&n);
                    Syn::lst(span, vec![Syn::symbol(span, with, interner), Syn::symbol(span, toplevel, interner), Syn::symbol(span, n, interner)])
                }
                Made::Plain(n) => Syn::named(span, &n, interner),
                Made::Module(m) => super::module_named(span, m, interner),
                Made::Of(m, n) => {
                    let n = interner.intern(&n);
                    let m = super::module_named(span, m, interner);
                    Syn::lst(span, vec![Syn::symbol(span, with, interner), m, Syn::symbol(span, n, interner)])
                }
                Made::Framed(m, f, n) => {
                    let n = interner.intern(&n);
                    let m = super::module_named(span, m, interner);
                    let inner = Syn::lst(span, vec![Syn::symbol(span, with, interner), m, Syn::symbol(span, f, interner)]);
                    Syn::lst(span, vec![Syn::symbol(span, with, interner), inner, Syn::symbol(span, n, interner)])
                }
            };
            written.insert(p, s);
        }
        Ok(written_at(form, Path::ROOT, &written))
    }
}

/// The top level's `base`, written as `free` says: a value, `(with
/// #%toplevel base)`; qualified (a description's name, a specification's),
/// `#%toplevel:base`; as written (a global's, which nothing shadows); a
/// `with`'s module, by its namespace `ns`.
fn top_made(free: Free, ns: Ns, base: &str) -> Made {
    match (free, ns) {
        (Free::Toplevel | Free::Inner, _) | (Free::Bound, Ns::Value) => Made::TopValue(base.to_string()),
        (Free::Qualified, _) | (Free::Bound, Ns::Desc) => Made::TopDesc(base.to_string()),
        (Free::Plain, _) => Made::Plain(base.to_string()),
    }
}

/// Whether `s` holds an alias, outside quotes.
fn has_alias(s: &Syn, interner: &Interner) -> bool {
    match &s.view() {
        V::Symbol(x) => alias_base(interner.name(*x)).is_some(),
        V::List { items, tail } => {
            let quoted = items.first().and_then(|h| h.sym()).is_some_and(|h| matches!(interner.name(h), "quote" | "quasiquote" | "%datum"));
            !quoted && (items.iter().any(|i| has_alias(i, interner)) || tail.as_ref().is_some_and(|t| has_alias(t, interner)))
        }
        _ => false,
    }
}

/// Whether `path`, in `form`, is inside a `(module …)` of it, not its head
/// (FX-26's `within-module?`, alike): a binder there may be an item, which
/// its name labels.
fn within_module(form: &Syn, path: &[bool], interner: &Interner) -> bool {
    let (mut s, mut p) = (*form, path);
    loop {
        let Some(items) = s.list() else { return false };
        if !p.is_empty() && items.first().and_then(|h| h.sym()).is_some_and(|h| interner.name(h) == "module") {
            return true;
        }
        let k = p.iter().take_while(|b| !**b).count();
        let Some(next) = items.get(k).filter(|_| k < p.len()) else { return false };
        (s, p) = (*next, &p[k + 1..]);
    }
}

/// `s`, at `path`, with each part `written` holds at its path written so.
fn written_at(s: &Syn, path: Path, written: &HashMap<Path, Syn>) -> Syn {
    if let Some(w) = written.get(&path) {
        return w.clone();
    }
    match &s.view() {
        V::List { items, tail } => {
            // Each item's path, the car of the cdrs before it.
            let mut rest = path;
            let mut out = Vec::with_capacity(items.len());
            for i in items {
                out.push(written_at(i, rest.push(true), written));
                rest = rest.push(false);
            }
            let tail = tail.as_ref().map(|t| written_at(t, rest, written));
            Syn::of_list(s.at(), &out, tail)
        }
        _ => s.clone(),
    }
}
