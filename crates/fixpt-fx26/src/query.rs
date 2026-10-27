//! Questions about a program's definitions, by their types and effects
//! (`,query` at the REPL, `fixpt query`; `docs/fx26.md`, "Queries"): which
//! have an effect, which mention a type, which make one, take one apart, or
//! change one. The program's sources are checked again, each a file of its
//! own, so that every answer says where its definition is.
//!
//! The answers are from the definitions' types, as written or as the
//! checker inferred them: a polymorphic definition whose type, as it is,
//! could only match once instantiated is listed apart, as one that may.

use crate::ast::{Atom, D, Effect, Exp, ExpId, ModItem, Region, Ty, TyId};
use crate::check::Checker;
use crate::top::Top;
use fixpt_read::{FileId, Span, Sym};
use std::collections::HashSet;

/// Where a program came from: a file's path, or the REPL's name for a form
/// typed (`<fx26:3>`); its text; and the directory its `load-module`s are
/// from.
#[derive(Clone, Debug)]
pub struct Source {
    pub name: String,
    pub text: String,
    pub base: Option<std::path::PathBuf>,
}

/// The first source's file number: past those of the files a program loads
/// (`Checker::files_read`, from 1001), so that a place says which.
const SOURCE0: u32 = 1 << 24;

/// A question. Of a procedure, it *gives* a `T` if the type mentions `T`
/// where a value comes out (its result, a field of that, what a callback
/// it takes is called with), and *needs* one if it mentions `T` where a
/// value goes in (a parameter, or one of a procedure it returns): by
/// polarity, so `(subr ((subr (T) unit)) unit)` gives one.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Query {
    /// `effect E`: definitions whose own effect has every atom of `E`.
    Effect(String),
    /// `uses T`: definitions whose type mentions `T`.
    Uses(String),
    /// `returns T`: procedures that give a `T`.
    Returns(String),
    /// `constructs T`: procedures that give a `T` without needing one.
    Constructs(String),
    /// `transforms T`: procedures that give a `T` only for one.
    Transforms(String),
    /// `consumes T`: procedures that need a `T` and give none.
    Consumes(String),
    /// `mutates T`: procedures that need a `T` and may write a region `T`
    /// is in: themselves, or a procedure they take or return.
    Mutates(String),
}

/// The questions, for help.
pub const USAGE: &[(&str, &str)] = &[
    ("effect E", "definitions whose own effect has E's atoms, as `(write @r)`"),
    ("uses T", "definitions whose type mentions T, written or inferred"),
    ("returns T", "procedures that give a T: as a result, or a callback's argument"),
    ("constructs T", "procedures that give a T without needing one"),
    ("transforms T", "procedures that give a T only for one"),
    ("consumes T", "procedures that need a T and give none"),
    ("mutates T", "procedures that need a T and may write a region T is in, themselves or a procedure they take or return"),
];

/// `KIND ARG`, as `,query` is given it: the argument one datum.
pub fn parse(text: &str) -> Result<Query, String> {
    let text = text.trim();
    let (kind, rest) = text.split_once(char::is_whitespace).unwrap_or((text, ""));
    let (arg, after) = datum(rest.trim())?;
    let after = after.trim();
    let only = |q: Query| if after.is_empty() { Ok(q) } else { Err(format!("`{kind}` takes one argument; `{after}` is past it")) };
    match kind {
        "effect" => only(Query::Effect(arg)),
        "uses" => only(Query::Uses(arg)),
        "consumes" => only(Query::Consumes(arg)),
        "mutates" => only(Query::Mutates(arg)),
        "returns" => only(Query::Returns(arg)),
        "constructs" => only(Query::Constructs(arg)),
        "transforms" => only(Query::Transforms(arg)),
        _ => Err(format!("no query `{kind}`: {}", USAGE.iter().map(|(u, _)| format!("`{u}`")).collect::<Vec<_>>().join(", "))),
    }
}

/// The first datum of `text`, as text, and what follows it.
fn datum(text: &str) -> Result<(String, &str), String> {
    if text.is_empty() {
        return Err("a type or an effect is wanted".into());
    }
    if !text.starts_with('(') {
        let end = text.find(char::is_whitespace).unwrap_or(text.len());
        return Ok((text[..end].to_string(), &text[end..]));
    }
    let mut depth = 0;
    for (i, ch) in text.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Ok((text[..=i].to_string(), &text[i + 1..]));
                }
            }
            _ => {}
        }
    }
    Err(format!("`{text}` is not closed"))
}

/// A program checked again for questions: the checker, its sources by file
/// number, and its definitions.
pub struct Program {
    pub checker: Checker,
    sources: Vec<Source>,
    defs: Vec<Def>,
}

/// A definition, or a module's item: its name as shown, its type, and
/// where it is.
struct Def {
    name: String,
    ty: TyId,
    span: Option<Span>,
}

/// One answer: a definition, its type as shown, and where it is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hit {
    pub name: String,
    pub ty: String,
    pub place: String,
    /// Only once instantiated, or for an effect the definition does not
    /// name: one that may.
    pub may: bool,
}

/// `sources` checked again, in order, with checker `c` (as the session's
/// is set, its program not in it), each a file of its own, keeping each
/// expression's type.
pub fn load(mut c: Checker, sources: &[Source]) -> Result<Program, String> {
    c.record_types = true;
    let mut tops: Vec<(Top, Option<Span>)> = Vec::new();
    for (i, s) in sources.iter().enumerate() {
        let file = FileId(SOURCE0 + i as u32);
        c.base_dir = s.base.clone();
        let forms = c.read_in(file, &s.text).map_err(|e| format!("{}: {}", s.name, e.message))?;
        let done = c.declare_ahead(&forms).map_err(|e| format!("{}: {}", s.name, e.message))?;
        for (f, done) in forms.iter().zip(done) {
            if done {
                continue;
            }
            let d = c.top_defining(f).map_err(|e| format!("{}: {}", place_of(&c, sources, e.span), e.message))?;
            tops.extend(d.hoisted.into_iter().chain(d.run).map(|(t, form)| (t, Some(form.span))));
        }
    }
    let defs = definitions(&mut c, &tops);
    Ok(Program { checker: c, sources: sources.to_vec(), defs })
}

/// Each global the program defines, latest last, and each item of a module
/// it defines or loads, as `m:x` or `file:x`.
fn definitions(c: &mut Checker, tops: &[(Top, Option<Span>)]) -> Vec<Def> {
    let mut named: Vec<(Sym, ExpId, Option<Span>)> = Vec::new();
    for (t, span) in tops {
        match t {
            Top::Define { name, exp, .. } => named.push((*name, *exp, *span)),
            Top::DefineRec { bindings, .. } => named.extend(bindings.iter().map(|(n, _, e)| (*n, *e, *span))),
            _ => {}
        }
    }
    // The latest definition of each name.
    let mut seen = HashSet::new();
    named.reverse();
    named.retain(|(n, _, _)| seen.insert(*n));
    named.reverse();
    let mut defs = Vec::new();
    for (name, exp, span) in named {
        let Some(ty) = c.global_type(name) else { continue };
        let text = c.interner.name(name).to_string();
        let shared = text.strip_prefix("%shared:").map(str::to_string);
        if text.starts_with('%') && shared.is_none() {
            continue;
        }
        if shared.is_none() {
            defs.push(Def { name: text.clone(), ty, span });
        }
        // A module's items, each where its module has it.
        let module = match c.arena.exp_at(exp).clone() {
            Exp::Var(v) => c.interner.name(v).starts_with("%shared:").then(|| loaded_module(c, v)).flatten(),
            Exp::Module(_) => Some(exp),
            _ => loaded_module_of(c, exp),
        };
        let prefix = shared.map(|p| p.rsplit('/').next().unwrap_or(&p).to_string()).unwrap_or(text);
        if let Ty::Module { vals, .. } = c.arena.get(c.arena.resolve(ty)).clone() {
            for (x, t) in vals {
                let item = module.and_then(|m| item_span(c, m, x));
                defs.push(Def { name: format!("{prefix}:{}", c.interner.name(x)), ty: t, span: item.or(span) });
            }
        }
    }
    defs
}

/// The module expression a load's hidden global `v` was made from.
fn loaded_module(c: &Checker, v: Sym) -> Option<ExpId> {
    let key = c.interner.name(v).strip_prefix("%shared:")?.to_string();
    c.loaded.iter().find(|(_, (p, _, _))| key.ends_with(p.as_str()) || *p == key).map(|(e, _)| *e)
}

/// The module expression `exp` is, if it is a file's, loaded.
fn loaded_module_of(c: &Checker, exp: ExpId) -> Option<ExpId> {
    c.loaded.contains_key(&exp).then_some(exp)
}

/// Where item `x` of module expression `m` is defined.
fn item_span(c: &Checker, m: ExpId, x: Sym) -> Option<Span> {
    let Exp::Module(items) = c.arena.exp_at(m) else { return None };
    items.iter().find_map(|it| match it {
        ModItem::Val { name, init, .. } if *name == x => Some(c.arena.span_of(*init)),
        ModItem::Rec(bs) => bs.iter().find(|(n, _, _)| *n == x).map(|(_, _, e)| c.arena.span_of(*e)),
        _ => None,
    })
}

/// `span` as `file:line:col`: a source's name, or a loaded file's path.
fn place_of(c: &Checker, sources: &[Source], span: Span) -> String {
    let (name, text): (String, &str) = if span.file.0 >= SOURCE0 {
        match sources.get((span.file.0 - SOURCE0) as usize) {
            Some(s) => (s.name.clone(), &s.text),
            None => return "?".into(),
        }
    } else if let Some((_, path, text)) = c.load_sites.get(&span.file) {
        (path.clone(), text)
    } else {
        return "?".into();
    };
    let at = (span.start as usize).min(text.len());
    let line = text[..at].matches('\n').count() + 1;
    let col = text[..at].rsplit('\n').next().unwrap_or("").chars().count() + 1;
    format!("{name}:{line}:{col}")
}

/// What a type is asked about as: a type, or a generative type's name,
/// which any application of it matches.
enum Want {
    Ty(TyId),
    Gen(u32),
}

impl Program {
    /// The answers to `q`, definite first, each in the program's order.
    pub fn answer(&mut self, q: &Query) -> Result<Vec<Hit>, String> {
        let c = &mut self.checker;
        let mut hits = Vec::new();
        let defs = std::mem::take(&mut self.defs);
        let result = (|| {
            match q {
                Query::Effect(e) => {
                    let want = c.effect_of_str(e).map_err(|e| e.message)?;
                    for d in &defs {
                        let Some((latent, _, _, _)) = subr_parts(c, d.ty) else { continue };
                        match effect_match(&want, &latent) {
                            Some(may) => hits.push((d, may)),
                            None => {}
                        }
                    }
                }
                Query::Uses(t) => {
                    let want = want_of(c, t)?;
                    for d in &defs {
                        if holds(c, d.ty, &want).any() {
                            hits.push((d, false));
                        }
                    }
                }
                Query::Returns(t) | Query::Constructs(t) | Query::Transforms(t) => {
                    let want = want_of(c, t)?;
                    for d in &defs {
                        if subr_parts(c, d.ty).is_none() {
                            continue;
                        }
                        let h = holds(c, d.ty, &want);
                        let wanted = match q {
                            Query::Constructs(_) => h.free,
                            Query::Transforms(_) => h.tolled,
                            _ => h.gives(),
                        };
                        if wanted {
                            hits.push((d, false));
                        }
                    }
                }
                Query::Consumes(t) => {
                    let want = want_of(c, t)?;
                    for d in &defs {
                        let h = holds(c, d.ty, &want);
                        if subr_parts(c, d.ty).is_some() && h.needs && !h.gives() {
                            hits.push((d, false));
                        }
                    }
                }
                Query::Mutates(t) => {
                    let want = want_of(c, t)?;
                    let Want::Ty(tt) = want else { return Err(format!("`mutates` wants a type, not a family: `{t}` applied")) };
                    let regions = mutable_regions(c, tt);
                    if regions.is_empty() {
                        return Err(format!("nothing in `{t}` can be written: no ref, array, cell, pair or bloblet it holds"));
                    }
                    for d in &defs {
                        if subr_parts(c, d.ty).is_none() || !holds(c, d.ty, &want).needs {
                            continue;
                        }
                        let mut effects = Vec::new();
                        effects_in(c, d.ty, &mut effects, &mut HashSet::new());
                        let writes = |e: &Effect, r: &Region| e.0.contains(&Atom::Write(*r)) || e.0.contains(&Atom::Init(*r));
                        if effects.iter().any(|e| regions.iter().any(|r| writes(e, r))) {
                            hits.push((d, false));
                        } else if effects.iter().any(|e| e.0.iter().any(|a| matches!(a, Atom::Var(_) | Atom::App(_) | Atom::Write(Region::Var(_)) | Atom::Init(Region::Var(_))))) {
                            hits.push((d, true));
                        }
                    }
                }
            }
            Ok(())
        })();
        let out = result.map(|()| {
            let mut out: Vec<Hit> = hits
                .iter()
                .map(|(d, may)| Hit {
                    name: d.name.clone(),
                    ty: crate::typeat::named(c, d.ty),
                    place: d.span.map_or_else(|| "?".into(), |s| place_of(c, &self.sources, s)),
                    may: *may,
                })
                .collect();
            out.sort_by_key(|h| h.may);
            out
        });
        self.defs = defs;
        out
    }
}

/// `t`'s latent effect, parameters and result, under any `poly`; and
/// whether it is polymorphic.
fn subr_parts(c: &Checker, t: TyId) -> Option<(Effect, Vec<TyId>, TyId, bool)> {
    let mut t = c.arena.resolve(t);
    let mut poly = false;
    while let Ty::Poly { body, .. } = c.arena.get(t) {
        t = c.arena.resolve(*body);
        poly = true;
    }
    let (e, ps, r) = c.arena.get(t).as_subr()?;
    Some((e, ps, r, poly))
}

/// Whether `latent` has every atom of `want`: `Some(false)`; or might,
/// once instantiated, for an atom an effect variable or a region variable
/// could be: `Some(true)`; else `None`.
fn effect_match(want: &Effect, latent: &Effect) -> Option<bool> {
    if want.within(latent) {
        return Some(false);
    }
    let unknown = latent.0.iter().any(|a| matches!(a, Atom::Var(_) | Atom::App(_)));
    let could = |a: &Atom| {
        Effect::atom(*a).within(latent)
            || unknown
            || latent.0.iter().any(|b| match (a, b) {
                (Atom::Read(_), Atom::Read(Region::Var(_)))
                | (Atom::Write(_), Atom::Write(Region::Var(_)))
                | (Atom::Alloc(_), Atom::Alloc(Region::Var(_)))
                | (Atom::Goto(_), Atom::Goto(Region::Var(_)))
                | (Atom::Comefrom(_), Atom::Comefrom(Region::Var(_)))
                | (Atom::Await(_), Atom::Await(Region::Var(_)))
                | (Atom::Init(_), Atom::Init(Region::Var(_)))
                | (Atom::Send(_), Atom::Send(Region::Var(_)))
                | (Atom::Receive(_), Atom::Receive(Region::Var(_))) => true,
                _ => false,
            })
    };
    want.0.iter().all(could).then_some(true)
}

/// `t` read as what a question is about: a generative type's bare name
/// matches any application of it.
fn want_of(c: &mut Checker, t: &str) -> Result<Want, String> {
    if !t.starts_with('(')
        && let Some(sym) = c.interner.get(t)
        && let Some(i) = c.generatives.iter().position(|g| g.name == sym)
        && !c.generatives[i].params.is_empty()
    {
        return Ok(Want::Gen(i as u32));
    }
    let t = c.type_of_str(t).map_err(|e| e.message)?;
    Ok(Want::Ty(as_checked(c, t)))
}

/// Type `t`, read by its names once the program is checked, as checking
/// made the program's types: what a module's effect or type read as
/// `(select m x)` before `m` was known is, put in (`typeat::named` does the
/// same to print).
fn as_checked(c: &mut Checker, t: TyId) -> TyId {
    let mut map = std::collections::HashMap::new();
    for ((m, e), v) in c.effect_selects.clone() {
        if let Ok(x) = c.selected_effect(m, e, Span::new(FileId(0), 0, 0)) {
            map.insert(v, D::Effect(x));
        }
    }
    for n in c.value_names() {
        if let Some(mt) = c.type_of_name(n)
            && let Ty::Module { descs, .. } = c.arena.get(c.arena.resolve(mt)).clone()
        {
            for (k, x) in descs {
                c.select_map.insert((n, k), x);
            }
        }
    }
    c.subst(t, &map)
}

/// How a value of a type holds what a question is about, `T`, as its
/// customer sees it (the code given the value):
///
/// - `free`: it gives the customer a `T` the customer need not have: a `T`
///   it holds, returns, or calls back with, reached without calling a
///   procedure whose arguments oblige the customer to make a `T`;
/// - `tolled`: it gives a `T`, but only through such a call: it transforms
///   `T`s (`(subr (T) T)`, or `(subr ((subr ((subr (T) T)) unit)) unit)`);
/// - `needs`: it may take a `T` from the customer.
///
/// A procedure the customer calls obliges it to make a `T` if `T` is in
/// one of its parameters as data, or as what a callback the customer
/// writes returns: not as what such a callback is given, which the
/// customer receives (`docs/fx26.md`, "Queries").
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
struct Holds {
    free: bool,
    tolled: bool,
    needs: bool,
}

impl Holds {
    fn any(self) -> bool {
        self.free || self.tolled || self.needs
    }
    fn gives(self) -> bool {
        self.free || self.tolled
    }
}

/// Whether type `t` is what `want` names.
fn is_wanted(c: &mut Checker, t: TyId, want: &Want) -> bool {
    let ty = c.arena.get(t).clone();
    match want {
        Want::Gen(w) => matches!(&ty, Ty::Named { which, .. } if which == w),
        Want::Ty(x) => {
            let x = c.arena.resolve(*x);
            t == x || (std::mem::discriminant(&ty) == std::mem::discriminant(c.arena.get(x)) && c.subtype(t, x) && c.subtype(x, t))
        }
    }
}

/// How a value of `t` holds what `want` names (`Holds`).
fn holds(c: &mut Checker, t: TyId, want: &Want) -> Holds {
    let mut h = Holds::default();
    let mut seen = HashSet::new();
    // Each type with whether the customer receives it (or gives it), and
    // whether reaching it obliged the customer to make a `T`.
    let mut todo = vec![(t, true, false)];
    while let Some((t, positive, toll)) = todo.pop() {
        let t = c.arena.resolve(t);
        if !seen.insert((t, positive, toll)) {
            continue;
        }
        if is_wanted(c, t, want) {
            match (positive, toll) {
                (true, false) => h.free = true,
                (true, true) => h.tolled = true,
                (false, _) => h.needs = true,
            }
            continue;
        }
        let ty = c.arena.get(t).clone();
        // A procedure: one the customer calls (given it) tolls the way to
        // all it gives, if its arguments oblige the customer to make a `T`.
        let call = match &ty {
            Ty::Subr { params, result, .. } => Some((params.clone(), *result)),
            Ty::Composable { arg, answer, .. } => Some((vec![*arg], *answer)),
            _ => None,
        };
        if let Some((params, result)) = call {
            let toll = toll || (positive && params.iter().any(|p| obliges(c, *p, want)));
            todo.extend(params.iter().map(|p| (*p, !positive, toll)));
            todo.push((result, positive, toll));
            continue;
        }
        for (k, side) in children(&ty) {
            match side {
                Side::Same | Side::Flip => todo.push((k, positive, toll)),
                Side::Both => todo.extend([(k, true, toll), (k, false, toll)]),
            }
        }
    }
    h
}

/// Whether giving a value of `t` obliges the giver to make what `want`
/// names: it holds one as data, or a procedure in it returns one; not
/// what a procedure in it is given.
fn obliges(c: &mut Checker, t: TyId, want: &Want) -> bool {
    let mut seen = HashSet::new();
    let mut todo = vec![t];
    while let Some(t) = todo.pop() {
        let t = c.arena.resolve(t);
        if !seen.insert(t) {
            continue;
        }
        if is_wanted(c, t, want) {
            return true;
        }
        let ty = c.arena.get(t).clone();
        todo.extend(children(&ty).into_iter().filter(|(_, side)| *side != Side::Flip).map(|(k, _)| k));
    }
    false
}

/// Where a type inside another is, as a value of the outer gives one: the
/// same way, the other way (a procedure's parameter, what a continuation
/// waits for), or both (held where it can be written, or a prompt's).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Side {
    Same,
    Flip,
    Both,
}

/// The types directly inside `ty`, each with its side.
fn children(ty: &Ty) -> Vec<(TyId, Side)> {
    use Side::*;
    let ds = |ds: &[D]| -> Vec<(TyId, Side)> {
        ds.iter()
            .filter_map(|d| match d {
                D::Type(t) | D::Fun(t) => Some((*t, Same)),
                _ => None,
            })
            .collect()
    };
    match ty {
        Ty::Union(ms) => ms.iter().map(|m| (*m, Same)).collect(),
        Ty::Subr { params, result, .. } => params.iter().map(|p| (*p, Flip)).chain([(*result, Same)]).collect(),
        Ty::Poly { body, .. } => vec![(*body, Same)],
        Ty::Ref(t, _) | Ty::MarkKey(t, _) | Ty::ICell(t, _) | Ty::Array(t, _, _) => vec![(*t, Both)],
        Ty::Pair(a, b, _, _) => vec![(*a, Same), (*b, Same)],
        Ty::PromptTag { answer, payload, .. } => vec![(*answer, Both), (*payload, Both)],
        Ty::Composable { arg, answer, .. } => vec![(*arg, Flip), (*answer, Same)],
        Ty::Product(fs) | Ty::Sum(fs) => fs.iter().map(|(_, t)| (*t, Same)).collect(),
        Ty::Bloblet { fields, frozen, .. } => fields.iter().map(|f| (*f, if *frozen { Same } else { Both })).collect(),
        Ty::Named { args, .. } => ds(args),
        Ty::NList { elem, .. } => vec![(*elem, Same)],
        Ty::Module { descs, vals, .. } => descs.iter().chain(vals).map(|(_, t)| (*t, Same)).collect(),
        Ty::Lam { body, .. } => ds(std::slice::from_ref(body)),
        Ty::App { fun, args } => [(*fun, Same)].into_iter().chain(ds(args)).collect(),
        Ty::Link(Some(t)) => vec![(*t, Same)],
        _ => Vec::new(),
    }
}

/// The regions of what a value of `t` holds that can be written: its refs,
/// arrays, cells, pairs and bloblets not frozen, as far as its data goes;
/// not into the procedures it holds, whose own state is theirs.
fn mutable_regions(c: &Checker, t: TyId) -> HashSet<Region> {
    let (mut out, mut seen, mut todo) = (HashSet::new(), HashSet::new(), vec![t]);
    while let Some(t) = todo.pop() {
        let t = c.arena.resolve(t);
        if !seen.insert(t) {
            continue;
        }
        let ty = c.arena.get(t).clone();
        match &ty {
            Ty::Ref(_, r) | Ty::Array(_, _, r) | Ty::ICell(_, r) | Ty::Pair(_, _, r, _) => {
                out.insert(*r);
            }
            Ty::Bloblet { frozen: false, region, .. } => {
                out.insert(*region);
            }
            Ty::Subr { .. } | Ty::Composable { .. } | Ty::PromptTag { .. } => continue,
            _ => {}
        }
        todo.extend(children(&ty).into_iter().map(|(k, _)| k));
    }
    out.retain(|r| !matches!(r, Region::Global(_) | Region::Globals | Region::Frozen(..)));
    out
}

/// Every effect in `t`: each procedure's latent effect, its own and those
/// of the procedures it takes or returns, wherever they are.
fn effects_in(c: &Checker, t: TyId, out: &mut Vec<Effect>, seen: &mut HashSet<TyId>) {
    let t = c.arena.resolve(t);
    if !seen.insert(t) {
        return;
    }
    let ty = c.arena.get(t).clone();
    match &ty {
        Ty::Subr { effect, .. } | Ty::PromptTag { effect, .. } | Ty::Composable { effect, .. } => out.push(effect.clone()),
        _ => {}
    }
    for (k, _) in children(&ty) {
        effects_in(c, k, out, seen);
    }
}
