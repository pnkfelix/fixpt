//! Syscalls (`docs/research/syscalls.md`): `(define-syscall name "host"
//! type)` and `(define-optional-syscall name "host" type)`, declared only
//! by a runtime's own code, and `(syscall-available? name)`.
//!
//! A declaration is checked alone, never against a runtime: the form, the
//! type's shape, its effect, the types that cross, where it is. Its type is
//! then printed in canonical form, and the declaration expands into two
//! definitions, each given that text: a hidden global,
//! `%syscall-available:NAME`, whether the runtime has it (which
//! `(syscall-available? NAME)` names), for a required one checked as it is
//! made (`%syscall-require`); and `NAME`, a procedure that calls the
//! runtime by host name (`%syscallN`). The checker written in FX-26 does the same
//! (`check-program.fx`, `k-define-syscall`), word for word.

use crate::ast::{Atom, Effect, IoKind, Kind, Region, Ty, TyId, D};
use crate::check::Checker;
use crate::error::{FxError, R};
use crate::top::Top;
use fixpt_read::{Datum, Span, Syntax};
use std::collections::HashMap;

/// The prefix of a declaration's hidden global, whether the runtime has it.
pub const AVAILABLE: &str = "%syscall-available:";

/// The most arguments a syscall takes (`fixpt_runtime::syscall::MAX_ARGS`).
pub const MAX_ARGS: usize = 6;

const SHAPE: &str = "a syscall's type is a `subr`, or a `poly` over regions only of one";
const CROSSING: &str =
    "a syscall takes and gives only `int`, `i64`, `u64`, `bool`, `char`, `unit`, `string`, `(flatarrayof i64 r)` and `(bytevectorof r)`";
const EFFECTS: &str =
    "a syscall's effect holds only reads, writes and allocations of its regions, I/O, `spin` and `nondet`";
const HOST: &str = "a syscall's host name is a string, `namespace:name/version`";

/// Whether `s` is a host name: a namespace, a colon, a name, a slash and a
/// version, the first two of lower-case letters, digits and `-`, the
/// version a number from 1.
pub fn valid_host(s: &str) -> bool {
    let part = |p: &str| !p.is_empty() && p.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-');
    let Some((ns, rest)) = s.split_once(':') else { return false };
    let Some((name, version)) = rest.rsplit_once('/') else { return false };
    part(ns)
        && part(name)
        && !version.is_empty()
        && version.bytes().all(|b| b.is_ascii_digit())
        && !version.starts_with('0')
}

/// A syntax tree's text, as the canonical form prints it: atoms apart by
/// one space, no other whitespace.
pub fn text(s: &Syntax, name: &dyn Fn(fixpt_read::Sym) -> String) -> String {
    match &s.datum {
        Datum::Symbol(x) => name(*x),
        Datum::List { items, .. } => {
            let parts: Vec<String> = items.iter().map(|i| text(i, name)).collect();
            format!("({})", parts.join(" "))
        }
        _ => unreachable!("a canonical type holds names and lists"),
    }
}

/// The names a canonical type and a declaration's expansion are made of.
const NAMES: &[&str] = &[
    "poly", "region", "subr", "maxeff", "read", "write", "alloc", "io", "spin", "nondet", "flatarrayof", "bytevectorof", "i64",
    "lambda", "the", "begin", "define", "bool", "string", "pure", "%syscall-require", "%syscall-available?",
];

impl Checker {
    /// Each of `NAMES`, the region binders `r1` to `rn` and the parameters
    /// `x1` to `xn`, the `%syscallN`s and the I/O kinds, interned.
    fn syscall_names(&mut self, n: usize) -> HashMap<String, fixpt_read::Sym> {
        let mut all: Vec<String> = NAMES.iter().map(|s| s.to_string()).collect();
        all.extend((1..=n.max(MAX_ARGS)).flat_map(|i| [format!("r{i}"), format!("x{i}")]));
        all.extend((0..=MAX_ARGS).map(|i| format!("%syscall{i}")));
        all.extend(IoKind::ALL.iter().map(|k| k.name().to_string()));
        all.into_iter().map(|s| (s.clone(), self.interner.intern(&s))).collect()
    }

    /// `(define-syscall name "host" type)` (`required`), or
    /// `(define-optional-syscall …)`: checked, then the definition it
    /// expands into, checked as a module file built in is.
    pub(crate) fn define_syscall(&mut self, form: &Syntax, items: &[Syntax], required: bool) -> R<Top> {
        let span = form.span;
        let what = if required { "define-syscall" } else { "define-optional-syscall" };
        if self.in_built_in == 0 && !self.syscalls {
            return Err(FxError::at(span, "syscalls are declared only by a runtime's own code"));
        }
        let [_, name, host, ty] = items else {
            return Err(FxError::at(span, format!("`({what} name \"host-name\" type)`")));
        };
        let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "expected a name"))?;
        let host_name = match &host.datum {
            Datum::Str(h) if valid_host(h) => h.clone(),
            _ => return Err(FxError::at(host.span, HOST)),
        };
        let t = self.parse_type(ty)?;
        let binders = match self.arena.get(self.arena.resolve(t)) {
            Ty::Poly { binders, .. } => binders.len(),
            _ => 0,
        };
        let names = self.syscall_names(binders);
        let canonical = self.canonical(&names, t, ty.span, span)?;
        let canonical_text = text(&canonical, &|s| self.interner.name(s).to_string());
        let companion = self.interner.intern(&format!("{AVAILABLE}{}", self.interner.name(name)));
        let (available, def) = self.syscall_expansion(&names, span, name, companion, &host_name, &canonical, &canonical_text, required);
        self.in_built_in += 1;
        // Whether the runtime has it, first, hidden as a loaded file's
        // global is (`hoisted`).
        let first = self.top(&available);
        let top = first.and_then(|first| {
            self.hoisted.push((first, std::rc::Rc::new(available)));
            self.top(&def)
        });
        self.in_built_in -= 1;
        top
    }

    /// `(syscall-available? name)`, for `name` a syscall declared: its
    /// hidden global, whether the runtime has it.
    pub(crate) fn syscall_available_form(&mut self, form: &Syntax, items: &[Syntax]) -> R<Syntax> {
        let usage = "`syscall-available?` takes the name of a syscall declared";
        let [_, name] = items else {
            return Err(FxError::at(form.span, usage));
        };
        let Some(n) = name.as_symbol() else { return Err(FxError::at(name.span, usage)) };
        let companion = self.interner.intern(&format!("{AVAILABLE}{}", self.interner.name(n)));
        if self.lookup(companion).is_none() {
            return Err(FxError::at(form.span, usage));
        }
        Ok(Syntax::symbol(form.span, companion))
    }

    /// The definitions a declaration is, its type `canonical`, `TEXT`
    /// printed, `LABEL` being `syscall NAME ("HOST")`:
    ///
    /// ```text
    /// (define %syscall-available:NAME bool (%syscall-available? HOST TEXT))
    /// (define NAME TYPE (lambda ((x1 P1) …) (the R (%syscallN LABEL HOST TEXT x1 …))))
    /// ```
    ///
    /// for a required one the first `(begin (%syscall-require LABEL HOST
    /// TEXT) #t)`; every part of the type the canonical form's. A `poly`'s
    /// binders are in scope in its definition, which is checked against its
    /// body.
    #[allow(clippy::too_many_arguments)]
    fn syscall_expansion(
        &self,
        names: &HashMap<String, fixpt_read::Sym>,
        span: Span,
        name: fixpt_read::Sym,
        companion: fixpt_read::Sym,
        host: &str,
        canonical: &Syntax,
        text: &str,
        required: bool,
    ) -> (Syntax, Syntax) {
        let sym = |s: &str| Syntax::symbol(span, names[s]);
        let string = |s: &str| Syntax::new(span, Datum::Str(s.to_string()));
        let list = |items: Vec<Syntax>| Syntax::list(span, items);
        let label = format!("syscall {} (\"{host}\")", self.interner.name(name));
        let parts = |s: &Syntax| s.as_proper_list().expect("canonical").to_vec();
        let subr = match &parts(canonical)[..] {
            [h, _, body] if h.as_symbol().is_some_and(|h| self.interner.name(h) == "poly") => body.clone(),
            _ => canonical.clone(),
        };
        let [_, _, params, result] = &parts(&subr)[..] else { unreachable!("a canonical `subr`") };
        let params = parts(params);
        let xs: Vec<Syntax> = (1..=params.len()).map(|i| sym(&format!("x{i}"))).collect();
        // The call at the declared effect: `%syscallN`'s, a binder, so given.
        let [_, effect, ..] = &parts(&subr)[..] else { unreachable!("a canonical `subr`") };
        let strings = [sym("string"), sym("string"), sym("string")].into_iter().chain(params.iter().cloned());
        let at = list(vec![sym("subr"), effect.clone(), list(strings.collect()), result.clone()]);
        let op = list(vec![sym("the"), at, sym(&format!("%syscall{}", params.len()))]);
        let call = [op, string(&label), string(host), string(text)];
        let call = list(call.into_iter().chain(xs.iter().cloned()).collect());
        let typed = params.iter().zip(&xs).map(|(p, x)| list(vec![x.clone(), p.clone()])).collect();
        let value = list(vec![sym("lambda"), list(typed), list(vec![sym("the"), result.clone(), call])]);
        let available = match required {
            true => {
                let check = list(vec![sym("%syscall-require"), string(&label), string(host), string(text)]);
                list(vec![sym("begin"), check, Syntax::new(span, Datum::Bool(true))])
            }
            false => list(vec![sym("%syscall-available?"), string(host), string(text)]),
        };
        (
            list(vec![sym("define"), Syntax::symbol(span, companion), sym("bool"), available]),
            list(vec![sym("define"), Syntax::symbol(span, name), canonical.clone(), value]),
        )
    }

    /// Type `t`, a syscall's, in canonical form (`docs/fx26.md`,
    /// "Syscalls"): every name expanded, effects flattened, deduplicated and
    /// sorted by their text, region binders `r1`, `r2`, … in order.
    /// Refused, at `at`, where it is not a syscall's type.
    fn canonical(&self, names: &HashMap<String, fixpt_read::Sym>, t: TyId, at: Span, span: Span) -> R<Syntax> {
        let sym = |s: &str| Syntax::symbol(span, names[s]);
        let list = |items: Vec<Syntax>| Syntax::list(span, items);
        let fail = |m: &str| FxError::at(at, m);
        let t = self.arena.resolve(t);
        let (binders, body) = match self.arena.get(t).clone() {
            Ty::Poly { binders, body } => (binders, self.arena.resolve(body)),
            _ => (Vec::new(), t),
        };
        let mut renamed = HashMap::new();
        let mut written = Vec::new();
        for (i, (v, k)) in binders.iter().enumerate() {
            if *k != Kind::Region {
                return Err(fail(SHAPE));
            }
            let n = format!("r{}", i + 1);
            written.push(list(vec![sym(&n), sym("region")]));
            renamed.insert(*v, n);
        }
        let Ty::Subr { conv, effect, params, result, spec } = self.arena.get(body).clone() else {
            return Err(fail(SHAPE));
        };
        // Called as the program calls any procedure: no `conv` but its own.
        if conv != self.conv_default || spec.is_some() {
            return Err(fail(SHAPE));
        }
        if params.len() > MAX_ARGS {
            return Err(fail(&format!("a syscall takes at most {MAX_ARGS} arguments")));
        }
        let region = |r: Region| match r {
            Region::Var(v) => renamed.get(&v).map(|n| sym(n)).ok_or_else(|| fail("a syscall's regions are its `poly`'s")),
            _ => Err(fail("a syscall's regions are its `poly`'s")),
        };
        let crossing = |p: TyId| -> R<Syntax> {
            let p = self.arena.resolve(p);
            match self.arena.get(p).clone() {
                Ty::Base(b) if ["int", "i64", "u64", "bool", "char", "unit", "string"].contains(&self.interner.name(b)) => {
                    Ok(Syntax::symbol(span, b))
                }
                Ty::Named { which: crate::check::FLATARRAYOF_INDEX, args } => match &args[..] {
                    [D::Type(e), D::Region(r)]
                        if matches!(self.arena.get(self.arena.resolve(*e)), Ty::Base(b) if self.interner.name(*b) == "i64") =>
                    {
                        Ok(list(vec![sym("flatarrayof"), sym("i64"), region(*r)?]))
                    }
                    _ => Err(fail(CROSSING)),
                },
                Ty::Named { which: crate::check::BYTEVECTOROF_INDEX, args } => match &args[..] {
                    [D::Region(r)] => Ok(list(vec![sym("bytevectorof"), region(*r)?])),
                    _ => Err(fail(CROSSING)),
                },
                _ => Err(fail(CROSSING)),
            }
        };
        let effect = self.canonical_effect(&effect, &region, &sym, &list, &fail)?;
        let params = params.iter().map(|p| crossing(*p)).collect::<R<Vec<_>>>()?;
        let subr = list(vec![sym("subr"), effect, list(params), crossing(result)?]);
        Ok(match binders.is_empty() {
            true => subr,
            false => list(vec![sym("poly"), list(written), subr]),
        })
    }

    /// A syscall's effect, canonical: its atoms' texts sorted, each once;
    /// none `pure`, one alone, else in a `maxeff`.
    fn canonical_effect(
        &self,
        effect: &Effect,
        region: &dyn Fn(Region) -> R<Syntax>,
        sym: &dyn Fn(&str) -> Syntax,
        list: &dyn Fn(Vec<Syntax>) -> Syntax,
        fail: &dyn Fn(&str) -> FxError,
    ) -> R<Syntax> {
        let mut atoms = Vec::new();
        for a in effect.0.iter() {
            atoms.push(match *a {
                Atom::Read(r) => list(vec![sym("read"), region(r).map_err(|_| fail(EFFECTS))?]),
                Atom::Write(r) => list(vec![sym("write"), region(r).map_err(|_| fail(EFFECTS))?]),
                Atom::Alloc(r) => list(vec![sym("alloc"), region(r).map_err(|_| fail(EFFECTS))?]),
                Atom::Io(k) => list(vec![sym("io"), sym(k.name())]),
                Atom::Spin => sym("spin"),
                Atom::Nondet => sym("nondet"),
                Atom::Stage => sym("stage"),
                _ => return Err(fail(EFFECTS)),
            });
        }
        let name = |s: fixpt_read::Sym| self.interner.name(s).to_string();
        let mut texts: Vec<(String, Syntax)> = atoms.into_iter().map(|a| (text(&a, &name), a)).collect();
        texts.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
        texts.dedup_by(|a, b| a.0 == b.0);
        let mut atoms: Vec<Syntax> = texts.into_iter().map(|(_, a)| a).collect();
        Ok(match atoms.len() {
            0 => sym("pure"),
            1 => atoms.pop().expect("one"),
            _ => list(std::iter::once(sym("maxeff")).chain(atoms).collect()),
        })
    }
}
