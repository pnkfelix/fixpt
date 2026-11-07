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
use fixpt_read::{Datum, Interner, Num, Syntax};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::collections::HashMap;

/// A reading: a digest of the session's state before it, `s`, and the
/// trees `text` reads as, never 0; or none, if it does not read (the Rust
/// checker's facts are of reading 0 until the FX-26 compiler gives them its
/// trees'). Not a count, so that whoever reads the same in the same state
/// makes the same and needs to ask no one; of the trees, not the text, so
/// that no space, comment, spelling or position tells two readings apart
/// that mean the same: `readings.fx`'s `reading-of`, the same function.
pub fn reading_of(s: i64, text: &str) -> Option<i64> {
    let mut names = fixpt_read::Interner::new();
    let trees = fixpt_read::Reader::new(text, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX26, &mut names).read_all().ok()?;
    Some(trees_reading_of(s, &trees, &names))
}

/// The switches a driver set that change what a check finds, as text, as
/// the checker written in FX-26 writes its own (`checked-settings`): the
/// program's convention, then each switch on. Folded into each reading
/// ([`read_in`]), so that a text read under other switches is another.
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

/// What a text is read in: the session's state `at` (0 where it begins),
/// and the switches its checker is set to. Given to each entry that reads
/// (`syn.rs`), which leaves `at` the state after, the reading it made, if
/// the checker kept the text; else as it was: a text refused, or tried,
/// leaves the session as it was.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct State {
    pub at: i64,
    pub settings: Settings,
}

/// The reading of `text`, read in the session's state `s` under switches
/// `settings`, each file it loads (`loads`, each its key and its text, or
/// why it could not be read, in the order they were read) folded after it:
/// what the parser is given is all of them (`syn::supply_loaded_at`). None
/// if `text` does not read.
pub fn read_in(s: i64, settings: &Settings, text: &str, loads: &[(String, String)]) -> Option<i64> {
    let r = reading_of(text_reading_of(s, &settings.text()), text)?;
    Some(loads.iter().fold(r, |h, (key, file)| {
        let h = text_reading_of(h, key);
        reading_of(h, file).unwrap_or_else(|| text_reading_of(h, file))
    }))
}

/// The reading of `trees`, read in `s`, their names in `names`.
pub fn trees_reading_of(s: i64, trees: &[Syntax], names: &Interner) -> i64 {
    let h = trees.iter().fold(s & MASK, |h, t| fold_tree(h, t, names));
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

fn fold_tree(h: i64, t: &Syntax, names: &Interner) -> i64 {
    let all = |h: i64, xs: &[Syntax]| xs.iter().fold(h, |h, x| fold_tree(h, x, names));
    match &t.datum {
        Datum::List { items, tail: None } => fold1(all(fold1(h, mark(1)), items), mark(2)),
        Datum::List { items, tail: Some(tail) } => fold1(fold_tree(fold1(all(fold1(h, mark(3)), items), mark(4)), tail, names), mark(2)),
        Datum::Vector(items) => fold1(all(fold1(h, mark(5)), items), mark(2)),
        Datum::Nil => fold1(fold1(h, mark(1)), mark(2)),
        Datum::Symbol(n) => fold_run(h, 6, names.name(*n)),
        Datum::Keyword(n) => fold_run(h, 7, names.name(*n)),
        Datum::Str(s) => fold_run(h, 8, s),
        Datum::Char(c) => fold1(fold1(h, mark(9)), *c as i64),
        Datum::Number(n @ (Num::Int(_) | Num::Big { .. })) => fold_run(h, 10, &integer(n).to_string()),
        Datum::Number(Num::Real(x)) => fold_run(h, 11, &x.to_bits().to_string()),
        Datum::Bool(b) => fold1(h, mark(if *b { 12 } else { 13 })),
        Datum::Bytevector(bs) => fold1(bs.iter().fold(fold1(h, mark(14)), |h, b| fold1(h, *b as i64)), mark(0)),
        // In lowest terms, as the FX-26 reader reads it and the Rust reader
        // leaves it.
        Datum::Number(Num::Ratio(a, b)) => {
            let (a, b) = (integer(a), integer(b));
            if b == BigInt::default() {
                return fold1(h, mark(16));
            }
            let q = BigRational::new(a, b);
            fold_run(fold_run(h, 15, &q.numer().to_string()), 15, &q.denom().to_string())
        }
    }
}

/// A number of the reader's that is an integer, as one.
fn integer(n: &Num) -> BigInt {
    match n {
        Num::Int(n) => BigInt::from(*n),
        Num::Big { negative, digits, radix } => {
            let m = BigInt::parse_bytes(digits.as_bytes(), *radix).unwrap_or_default();
            if *negative { -m } else { m }
        }
        Num::Ratio(..) | Num::Real(_) => BigInt::default(),
    }
}

/// Each expression walked, its number.
#[derive(Default)]
pub struct Kth {
    /// How many have been walked.
    seen: u32,
    of: HashMap<ExpId, u32>,
}

impl Kth {
    pub fn new() -> Kth {
        Kth::default()
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

    /// Whether `e` was walked: one of the forms' given.
    pub fn walked(&self, e: ExpId) -> bool {
        self.of.contains_key(&e)
    }

    /// `e`'s number: 0 if it was not walked.
    pub fn of(&self, e: ExpId) -> u32 {
        self.of.get(&e).copied().unwrap_or(0)
    }

    fn exp(&mut self, c: &Checker, e: ExpId) {
        self.of.insert(e, self.seen);
        self.seen += 1;
        for x in within(c, e) {
            self.exp(c, x);
        }
    }
}

/// `roots` and every expression in them: what is inside one, by the trees'
/// structure, not by where it is written (a template's parts share a use's
/// span, and an argument placed twice is one span at two places;
/// `docs/research/loads-and-places.md`, "Decided: identity by position").
pub(crate) fn subtrees(c: &Checker, roots: &[ExpId]) -> std::collections::HashSet<ExpId> {
    let mut out = std::collections::HashSet::new();
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
pub(crate) fn parents(c: &Checker) -> HashMap<ExpId, ExpId> {
    let mut out = HashMap::new();
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
        Exp::Var(_) | Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => Vec::new(),
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
