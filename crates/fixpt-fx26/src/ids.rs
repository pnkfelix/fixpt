//! Each expression's identity as the front end written in FX-26 keeps it
//! (`parser-types.fx`, `parser-ids.fx`): its position, its number in a
//! walk of the program's trees that takes each expression before what is
//! in it, the forms in order, from 0; where it starts and ends beside, its
//! provenance. What the checkers find of an expression is kept by it
//! (`docs/research/loads-and-places.md`, "Decided: identity by
//! position").
//!
//! The Rust front end tells its expressions apart by [`ExpId`]; [`Kth`]
//! numbers them, walking the same trees in the same order, so that what
//! the Rust checker finds is keyed as the FX-26 compiler looks it up
//! (`syn::rust_facts`).

use crate::ast::{Exp, ExpId, ModItem};
use crate::check::Checker;
use crate::top::Top;
use crate::heap_syn::{Shape, Syn, V};
use fixpt_heap::{ObjType, Value};
use fixpt_read::Interner;
use fixpt_hash::HashMap;

/// A reading: a digest of the session's state before it, `s`, and the
/// trees `text` reads as, never 0; or none, if it does not read (the Rust
/// checker's facts are of reading 0 until the FX-26 compiler gives them its
/// trees'). Not a count, so that whoever reads the same in the same state
/// makes the same and needs to ask no one; of the trees, not the text, so
/// that no space, comment, spelling or position tells two readings apart
/// that mean the same: `readings.fx`'s `reading-of`, the same function.
pub fn reading_of(s: i64, text: &str) -> Option<i64> {
    let mut names = Interner::new();
    crate::heap_syn::aside(|| {
        let trees = crate::heap_syn::read_syn_unplaced(text, &mut names).ok()?;
        Some(trees_reading_of(s, &trees, &names))
    })
}

/// The switches a driver set that change what a check finds, as text, as
/// the checker written in FX-26 writes its own (`checked-settings`): the
/// program's convention, then each switch on. Folded into each reading
/// ([`form_reading`]), so that a text read under other switches is another.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Settings {
    pub native: bool,
    pub globals_effects: bool,
    pub defer_reruns: bool,
    pub syscalls: bool,
    pub built_in: bool,
}

impl Settings {
    /// The switches checker `c` is set to.
    pub fn of(c: &Checker) -> Settings {
        Settings {
            native: c.conv_default == crate::ast::Conv::Native,
            globals_effects: c.globals_effects,
            defer_reruns: c.defer_reruns,
            syscalls: c.syscalls,
            built_in: c.in_built_in > 0,
        }
    }

    pub fn text(&self) -> String {
        let on = |b: bool, s: &'static str| if b { s } else { "" };
        format!(
            "{}{}{}{}{}",
            if self.native { "native" } else { "cellular" },
            on(self.globals_effects, " globals-effects"),
            on(self.defer_reruns, " defer-reruns"),
            on(self.syscalls, " syscalls"),
            on(self.built_in, " built-in")
        )
    }
}

/// What a text is read in: the session's state `at` (the standard
/// environment's where it begins) and the switches its checker is set to.
/// Given to each entry that reads (`syn.rs`), which leaves `at` the state
/// after if the checker kept the text, else as it was: a text refused, or
/// tried, leaves the session as it was. (`path`'s count is the FX-26
/// parser's own, as long as its front end lasts: `walked-total`.)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct State {
    pub at: i64,
    pub settings: Settings,
}

/// What an expression's key is made of (`docs/research/loads-and-places.md`,
/// "Decided: three keys"; `parser-ids.fx`): `Path`, its place in the
/// session's walk, the cheap key, by default; `Digest`, its place in its
/// form's, beside the form's reading; `Full`, the digest of its path down
/// the form, beside the form's reading; `Validate`, `Full`'s, the others
/// checked against it. As `FIXPT_FACT_KEYS` says (`path`, `digest`, `full`,
/// `validate`), once for the process.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Path = 0,
    Digest = 1,
    Full = 2,
    Validate = 3,
}

static MODE: std::sync::OnceLock<Mode> = std::sync::OnceLock::new();

/// The process's mode, as `FIXPT_FACT_KEYS` says, unless [`set_mode`] said
/// first.
pub fn mode() -> Mode {
    *MODE.get_or_init(|| match std::env::var("FIXPT_FACT_KEYS").as_deref() {
        Ok("digest") => Mode::Digest,
        Ok("full") => Mode::Full,
        Ok("validate") => Mode::Validate,
        _ => Mode::Path,
    })
}

/// The process's mode made `m`, if nothing has asked it yet (a test's, of
/// its own process): whether it is `m` now.
pub fn set_mode(m: Mode) -> bool {
    *MODE.get_or_init(|| m) == m
}

/// A form's reading (`readings.fx`'s `form-reading`, the same function):
/// the session's state before it, `s`, folded with the switches the checker
/// is set to, the form's trees, and each file the form loads first, by its
/// key and its trees (or its text, if it does not read), in the order of
/// the keys; never 0. The state after the form, which the next is read in.
///
/// Of syntax lent (`crate::heap_syn`): the files it loads read there too.
pub fn form_reading(s: i64, settings: &Settings, form: Syn, names: &Interner, loads: &[(String, String)]) -> i64 {
    let mut loads: Vec<&(String, String)> = loads.iter().collect();
    loads.sort_by(|a, b| a.0.cmp(&b.0));
    let h = fold_tree(fold_text(s & MASK, &settings.text()), form, names);
    let h = loads.iter().fold(h, |h, (key, file)| {
        let h = fold_run(h, 17, key);
        let mut names = Interner::new();
        let h = match crate::heap_syn::read_syn_unplaced(file, &mut names) {
            Ok(trees) => trees.into_iter().fold(h, |h, t| fold_tree(h, t, &names)),
            Err(_) => fold_text(h, file),
        };
        fold1(h, mark(0))
    });
    if h == 0 { 1 } else { h }
}

/// The session's state after `text`, read in `s` under `settings`, each of
/// its forms in turn ([`form_reading`]), the files the `i`th loads first
/// `loads[i]` (none past the end); none if it does not read. A text with no
/// form leaves it as it was.
pub fn forms_state(s: i64, settings: &Settings, text: &str, loads: &[Vec<(String, String)>]) -> Option<i64> {
    let mut names = Interner::new();
    crate::heap_syn::aside(|| {
        let forms = crate::heap_syn::read_syn_unplaced(text, &mut names).ok()?;
        Some(forms.into_iter().enumerate().fold(s, |s, (i, f)| form_reading(s, settings, f, &names, loads.get(i).map_or(&[][..], |l| &l[..]))))
    })
}

/// A session's state where its checker begins in the standard environment
/// (`readings.fx`'s `standard-state`): the reading of its trees, in no
/// state before; the text of this build's (`standard::standard_text`).
pub fn standard_state() -> i64 {
    static STATE: std::sync::OnceLock<i64> = std::sync::OnceLock::new();
    *STATE.get_or_init(|| reading_of(0, &crate::standard::standard_text()).unwrap_or(0))
}

/// The state `s`, as a staged step's text is read in it: with the type it
/// is checked against, `rep`, and the types its names are given, `named`,
/// each a rep's bytes, folded in (`readings.fx`'s `with-reps`); none, `s`
/// as it is.
pub fn with_reps(s: i64, rep: &[u8], named: &[(String, Vec<u8>)]) -> i64 {
    if rep.is_empty() && named.is_empty() {
        return s;
    }
    let rep_of = |h: i64, b: &[u8]| fold1(b.iter().fold(h, |h, x| fold1(h, *x as i64)), mark(0));
    let h = named.iter().fold(rep_of(fold1(s & MASK, mark(18)), rep), |h, (n, b)| rep_of(fold_run(h, 19, n), b));
    if h == 0 { 1 } else { h }
}

impl State {
    /// Where a checker begins, in the standard environment: its state
    /// ([`standard_state`]), the default switches.
    pub fn begun() -> State {
        State { at: standard_state(), settings: Settings::default() }
    }
}

/// The reading of `trees`, read in `s`, their names in `names`.
pub fn trees_reading_of(s: i64, trees: &[Syn], names: &Interner) -> i64 {
    let h = trees.iter().fold(s & MASK, |h, t| fold_tree(h, *t, names));
    if h == 0 { 1 } else { h }
}

/// The reading of a text that is no trees (`readings.fx`'s
/// `text-reading-of`): its characters, in `s`.
pub fn text_reading_of(s: i64, text: &str) -> i64 {
    let h = fold_text(s & MASK, text);
    if h == 0 { 1 } else { h }
}

const MASK: i64 = (1 << 40) - 1;

/// One piece, a character's code or a mark, folded in, each step a fixnum.
fn fold1(h: i64, x: i64) -> i64 {
    (h * 1_000_003 + x + 1) & MASK
}

/// Mark `m`, past every character's code (`readings.fx`'s list of them).
fn mark(m: i64) -> i64 {
    0x11_0000 + m
}

fn fold_text(h: i64, text: &str) -> i64 {
    text.chars().fold(h, |h, c| fold1(h, c as i64))
}

/// `text` after mark `m`, then the end's.
fn fold_run(h: i64, m: i64, text: &str) -> i64 {
    fold1(fold_text(fold1(h, mark(m)), text), mark(0))
}

/// Tree `t` folded in, as `readings.fx`'s `fold-tree` folds it: an atom
/// by what the reader made of it in the heap, as it has it (an integer
/// first, so that `4/2` is `2`, as FX-26 reads it).
fn fold_tree(h: i64, t: Syn, names: &Interner) -> i64 {
    let all = |h: i64, xs: Vec<Syn>| xs.into_iter().fold(h, |h, x| fold_tree(h, x, names));
    match t.shape() {
        Shape::Nil => fold1(fold1(h, mark(1)), mark(2)),
        Shape::List | Shape::Dotted | Shape::Vector => match t.view() {
            V::List { items, tail: None } => fold1(all(fold1(h, mark(1)), items), mark(2)),
            V::List { items, tail: Some(tail) } => fold1(fold_tree(fold1(all(fold1(h, mark(3)), items), mark(4)), tail, names), mark(2)),
            V::Vector(items) => fold1(all(fold1(h, mark(5)), items), mark(2)),
            _ => unreachable!("a list or a vector"),
        },
        Shape::Symbol(n) => fold_run(h, 6, names.name(n)),
        Shape::Keyword(n) => fold_run(h, 7, names.name(n)),
        _ => crate::heap_syn::rd(|r| {
            let (heap, d) = (r.heap, crate::heap_syn::datum_of(r.heap, r.value(t)));
            if d.is_fixnum() || heap.is_a(d, ObjType::Bignum) {
                fold_run(h, 10, &fixpt_runtime::write_value(heap, d))
            } else if heap.is_a(d, ObjType::Flonum) {
                fold_run(h, 11, &heap.flonum_value(d).to_bits().to_string())
            } else if heap.is_a(d, ObjType::Ratnum) {
                let w = fixpt_runtime::write_value(heap, d);
                let (a, b) = w.split_once('/').expect("a ratio written `a/b`");
                fold_run(fold_run(h, 15, a), 15, b)
            } else if heap.is_a(d, ObjType::String) {
                fold_run(h, 8, &heap.string_to_rust(d))
            } else if d.is_char() {
                fold1(fold1(h, mark(9)), d.as_char() as i64)
            } else if d == Value::TRUE || d == Value::FALSE {
                fold1(h, mark(if d == Value::TRUE { 12 } else { 13 }))
            } else if heap.is_a(d, ObjType::Bytevector) {
                let bs = (0..heap.bytevector_len(d)).map(|i| heap.bytevector_ref(d, i));
                fold1(bs.fold(fold1(h, mark(14)), |h, b| fold1(h, b as i64)), mark(0))
            } else {
                fold1(h, mark(16))
            }
        }),
    }
}

/// Each expression walked, its place in the walk; and, walked form by form
/// ([`Kth::keyed`], [`Kth::form`]), its key as the mode makes it, as the
/// FX-26 parser does (`parser-ids.fx`).
#[derive(Default)]
pub struct Kth {
    /// How many have been walked.
    seen: u32,
    of: HashMap<ExpId, u32>,
    keys: HashMap<ExpId, (i64, i64)>,
    /// The mode, if the walk keys by one.
    mode: Option<Mode>,
    /// How many the session walked before the form; how many of the form
    /// have been walked; the form's reading (0 in `path`); and, in `full`,
    /// the frames down the form: each expression around the one walked,
    /// the innermost last, by its path's digest and how many of what is in
    /// it have been walked.
    walked: i64,
    in_form: i64,
    reading: i64,
    frames: Vec<(i64, i64)>,
}

impl Kth {
    pub fn new() -> Kth {
        Kth::default()
    }

    /// A walk that keys by `mode`, the session having walked `walked`.
    pub fn keyed(mode: Mode, walked: i64) -> Kth {
        Kth { mode: Some(mode), walked, ..Kth::default() }
    }

    /// The expressions of a form's trees `tops` (what it makes, after the
    /// hidden globals of the files it loads first), of its reading `r`
    /// ([`form_reading`]).
    pub fn form(&mut self, c: &Checker, r: i64, tops: &[&Top]) {
        let mode = self.mode.unwrap_or(Mode::Path);
        self.in_form = 0;
        self.reading = if mode == Mode::Path { 0 } else { r };
        self.frames = vec![(r, 0)];
        for t in tops {
            self.top(c, t);
        }
        self.walked += self.in_form;
    }

    /// The expressions of `top`, the next of the program's forms.
    pub fn top(&mut self, c: &Checker, top: &Top) {
        match top {
            Top::Define { exp, .. } => self.exp(c, *exp),
            Top::DefineRec { bindings, .. } => bindings.iter().for_each(|(_, _, e)| self.exp(c, *e)),
            Top::Exp(k) => self.exp(c, k.exp),
            _ => {}
        }
    }

    /// How many expressions have been walked.
    pub fn count(&self) -> u32 {
        self.seen
    }

    /// Whether `e` was walked: one of the forms' given.
    pub fn walked(&self, e: ExpId) -> bool {
        self.of.contains_key(&e)
    }

    /// `e`'s number: 0 if it was not walked.
    pub fn of(&self, e: ExpId) -> u32 {
        self.of.get(&e).copied().unwrap_or(0)
    }

    /// `e`'s key, its number and its reading: as the mode makes it, if the
    /// walk keys by one; else its place, of reading 0.
    pub fn key(&self, e: ExpId) -> (i64, i64) {
        self.keys.get(&e).copied().unwrap_or((self.of(e) as i64, 0))
    }

    fn exp(&mut self, c: &Checker, e: ExpId) {
        self.of.insert(e, self.seen);
        self.seen += 1;
        let deep = matches!(self.mode, Some(Mode::Full | Mode::Validate));
        if let Some(mode) = self.mode {
            let k = match mode {
                Mode::Path => self.walked + self.in_form,
                Mode::Digest => self.in_form,
                Mode::Full | Mode::Validate => {
                    let up = self.frames.last_mut().expect("a form's frame");
                    let z = fold1(up.0, up.1);
                    up.1 += 1;
                    self.frames.push((z, 0));
                    z
                }
            };
            self.keys.insert(e, (k, self.reading));
            self.in_form += 1;
        }
        for x in within(c, e) {
            self.exp(c, x);
        }
        if deep {
            self.frames.pop();
        }
    }
}

/// The files the hidden globals `hoisted` are, which a form loads first,
/// each by its key and its text, as [`form_reading`] takes them: a hidden
/// global is `%shared:` and its key, its value the file's module, which
/// the checker read (`Checker::loaded`).
pub fn form_loads(c: &Checker, hoisted: &[&Top]) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for t in hoisted {
        let Top::Define { name, exp, .. } = t else { continue };
        let Some(key) = c.interner.name(*name).strip_prefix("%shared:") else { continue };
        let inside = subtrees(c, &[*exp]);
        if let Some((_, text, _)) = inside.iter().find_map(|x| c.loaded.get(x)) {
            out.push((key.to_string(), text.clone()));
        }
    }
    out
}

/// `roots` and every expression in them: what is inside one, by the trees'
/// structure, not by where it is written (a template's parts share a use's
/// span, and an argument placed twice is one span at two places;
/// `docs/research/loads-and-places.md`, "Decided: identity by position").
pub(crate) fn subtrees(c: &Checker, roots: &[ExpId]) -> fixpt_hash::HashSet<ExpId> {
    let mut out = fixpt_hash::HashSet::default();
    let mut stack = roots.to_vec();
    while let Some(x) = stack.pop() {
        if out.insert(x) {
            stack.extend(within(c, x));
        }
    }
    out
}

/// Each expression's parent, the one it is directly in, of every
/// expression made: what is around one, by structure (`subtrees`).
pub(crate) fn parents(c: &Checker) -> crate::ast::IdMap<ExpId, ExpId> {
    let mut out = crate::ast::IdMap::default();
    for e in c.arena.exp_ids() {
        for x in within(c, e) {
            out.insert(x, e);
        }
    }
    out
}

/// The expressions in `e`, in the order the trees are written
/// (`sexp::show_top`, and the parser's datatypes in `parser-types.fx`).
fn within(c: &Checker, e: ExpId) -> Vec<ExpId> {
    match c.arena.exp_at(e) {
        Exp::Var(_) | Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Quote { .. } | Exp::Unit => Vec::new(),
        Exp::Lambda { body, .. } | Exp::PLambda { body, .. } | Exp::LetRegion { body, .. } | Exp::Proj { body, .. } => vec![*body],
        Exp::App { fun, args } => std::iter::once(*fun).chain(args.iter().copied()).collect(),
        Exp::RLambda { region, lambda } => vec![*region, *lambda],
        Exp::If { test, then, els } => vec![*test, *then, *els],
        Exp::Letrec { bindings, body } => bindings.iter().map(|(_, _, x)| *x).chain([*body]).collect(),
        Exp::Let { bindings, body } => bindings.iter().map(|(_, x)| *x).chain([*body]).collect(),
        Exp::Begin(items) => items.clone(),
        Exp::Prompt { tag, body, handler } => vec![*tag, *body, *handler],
        Exp::The { exp, .. } | Exp::Convention { exp, .. } => vec![*exp],
        Exp::Bloblet { args, .. } => args.clone(),
        Exp::Module(items) => items
            .iter()
            .flat_map(|item| match item {
                ModItem::Abs { up_fn, down_fn, .. } => vec![*up_fn, *down_fn],
                ModItem::Desc { .. } => Vec::new(),
                ModItem::Val { init, .. } => vec![*init],
                ModItem::Rec(group) => group.iter().map(|(_, _, x)| *x).collect(),
            })
            .collect(),
        Exp::With { body, .. } => vec![*body],
        Exp::Product(fields) => fields.iter().map(|(_, x)| *x).collect(),
        Exp::Extract(x, _) | Exp::Sum(_, x) => vec![*x],
        Exp::TagCase { scrutinee, arms, els } => {
            std::iter::once(*scrutinee).chain(arms.iter().map(|a| a.body)).chain(els.iter().map(|(_, x)| *x)).collect()
        }
    }
}
