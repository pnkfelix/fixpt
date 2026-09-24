//! `syntax-rules` (R7RS 4.3.2), hygienic by renaming.
//!
//! Matching and template instantiation work directly on [`Syntax`]; a rule is
//! interpreted at each use rather than compiled first, which is simpler and
//! costs the same order of work — both are a walk over the pattern and the
//! input. What makes the result hygienic is one step: every identifier the
//! *template* inserts becomes an alias ([`Expander::alias`]), resolving in the
//! scopes visible where the macro was defined. Identifiers that came from the
//! *use* are substituted unchanged. So a template's `if` is the `if` of the
//! definition site, and a template's `tmp` cannot capture a user's `tmp` —
//! Clinger & Rees, *Macros That Work*, as in Larceny's Twobit
//! (`src/Compiler/syntaxrules.sch`).
//!
//! Literals are compared as R7RS asks: an input identifier matches a literal
//! when both mean the same thing — the input where it was used, the literal
//! where the macro was defined. That is why `else` stops matching once a
//! program binds `else` locally.

use crate::env::{Binding, Special};
use crate::expand::{ExpandError, Expander};
use fixpt_read::{Datum, Span, Sym, Syntax};
use std::collections::HashMap;
use std::rc::Rc;

type R<T> = Result<T, ExpandError>;

/// How deeply macro uses may nest before the expander gives up. A macro whose
/// expansion always contains another use of itself would otherwise recurse
/// until the Rust stack ran out.
pub(crate) const MAX_EXPANSION_DEPTH: u32 = 2_000;

/// What a macro keyword is bound to.
#[derive(Clone)]
pub enum MacroDef {
    Rules(Rc<Macro>),
    Proc(Rc<crate::procmacro::ProcMacro>),
}

pub struct Macro {
    name: Sym,
    /// A custom ellipsis (`(syntax-rules ::: (…) …)`), or `None` for `...`.
    ellipsis: Option<Sym>,
    literals: Vec<Sym>,
    rules: Vec<(Syntax, Syntax)>,
    /// Scopes visible at the definition — see `expand::Alias::scope`.
    scope: u32,
}

/// What a pattern variable matched: one piece of syntax, or — under an
/// ellipsis — a sequence of them.
#[derive(Clone, Debug)]
enum M {
    One(Syntax),
    Seq(Vec<M>),
}

impl Macro {
    fn is_literal(&self, s: Sym) -> bool {
        self.literals.contains(&s)
    }
}

impl Expander<'_> {
    // ------------------------------------------------------------ definition
    /// Turn a transformer spec into a macro, defined in the outermost `scope`
    /// scopes.
    pub(crate) fn make_macro(&mut self, name: Sym, spec: &Syntax, scope: u32) -> R<u32> {
        let rules = spec.as_proper_list().filter(|it| {
            it.first()
                .and_then(|h| h.as_symbol())
                .is_some_and(|h| self.resolve(h) == Some(Binding::Special(Special::SyntaxRules)))
        });
        let Some(items) = rules else {
            // Anything else is a procedural transformer: an expression to run.
            let pm = self.make_proc_macro(name, spec, scope)?;
            self.macros.push(MacroDef::Proc(Rc::new(pm)));
            return Ok(self.macros.len() as u32 - 1);
        };
        let mut args = &items[1..];
        let ellipsis = match args.first().map(|a| &a.datum) {
            Some(Datum::Symbol(e)) => {
                let e = *e;
                args = &args[1..];
                Some(e)
            }
            _ => None,
        };
        let Some((lits, rules)) = args.split_first() else {
            return Err(ExpandError::at(spec.span, "`syntax-rules` needs a list of literals"));
        };
        let literals = match &lits.datum {
            Datum::Nil => Vec::new(),
            Datum::List { items, tail: None } => items
                .iter()
                .map(|l| {
                    l.as_symbol()
                        .ok_or_else(|| ExpandError::at(l.span, "a literal must be an identifier"))
                })
                .collect::<R<Vec<Sym>>>()?,
            _ => return Err(ExpandError::at(lits.span, "`syntax-rules` needs a list of literals")),
        };
        let mut m = Macro { name, ellipsis, literals, rules: Vec::new(), scope };
        for rule in rules {
            let parts = rule.as_proper_list().filter(|p| p.len() == 2).ok_or_else(|| {
                ExpandError::at(rule.span, "a `syntax-rules` rule is `(pattern template)`")
            })?;
            let pattern = &parts[0];
            if !matches!(pattern.datum, Datum::List { .. }) {
                return Err(ExpandError::at(
                    pattern.span,
                    "a `syntax-rules` pattern must be a list starting with the keyword",
                ));
            }
            self.check_pattern(&m, pattern, &mut Vec::new())?;
            m.rules.push((pattern.clone(), parts[1].clone()));
        }
        self.macros.push(MacroDef::Rules(Rc::new(m)));
        Ok(self.macros.len() as u32 - 1)
    }

    /// Reject what R7RS rules out at definition time, where the error can
    /// point at the rule rather than at some later use: a variable used twice,
    /// or two ellipses in one list.
    fn check_pattern(&self, m: &Macro, p: &Syntax, seen: &mut Vec<Sym>) -> R<()> {
        match &p.datum {
            Datum::Symbol(s) => {
                if !m.is_literal(*s) && !self.is_underscore(m, *s) && !self.is_ellipsis(m, *s) {
                    if seen.contains(s) {
                        let n = self.rt.interner.name(*s).to_string();
                        return Err(ExpandError::at(p.span, format!("pattern variable `{n}` appears twice")));
                    }
                    seen.push(*s);
                }
                Ok(())
            }
            Datum::List { items, tail } => {
                let mut ellipses = 0;
                for i in items {
                    if i.as_symbol().is_some_and(|s| self.is_ellipsis(m, s)) {
                        ellipses += 1;
                    } else {
                        self.check_pattern(m, i, seen)?;
                    }
                }
                if ellipses > 1 {
                    return Err(ExpandError::at(p.span, "a pattern list may contain only one ellipsis"));
                }
                if let Some(t) = tail {
                    self.check_pattern(m, t, seen)?;
                }
                Ok(())
            }
            Datum::Vector(items) => {
                for i in items {
                    if !i.as_symbol().is_some_and(|s| self.is_ellipsis(m, s)) {
                        self.check_pattern(m, i, seen)?;
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn is_ellipsis(&self, m: &Macro, s: Sym) -> bool {
        match m.ellipsis {
            Some(e) => s == e,
            // By name, so that `...` inserted by an outer macro's template —
            // and therefore renamed — still reads as an ellipsis inside a
            // `syntax-rules` that template builds.
            None => !m.is_literal(s) && self.rt.interner.name(s) == "...",
        }
    }

    fn is_underscore(&self, m: &Macro, s: Sym) -> bool {
        !m.is_literal(s) && self.rt.interner.name(s) == "_"
    }

    // ------------------------------------------------------------- expansion
    /// If `form` is a use of a macro, its expansion.
    pub(crate) fn expand_head_macro(&mut self, form: &Syntax) -> R<Option<Syntax>> {
        let Datum::List { items, .. } = &form.datum else { return Ok(None) };
        let Some(head) = items.first().and_then(|h| h.as_symbol()) else { return Ok(None) };
        match self.resolve(head) {
            Some(Binding::Macro(id)) => Ok(Some(self.expand_macro(id, form)?)),
            _ => Ok(None),
        }
    }

    pub(crate) fn expand_macro(&mut self, id: u32, form: &Syntax) -> R<Syntax> {
        let def = self.macros[id as usize].clone();
        let name = match &def {
            MacroDef::Rules(m) => m.name,
            MacroDef::Proc(p) => p.name,
        };
        if self.macro_depth >= MAX_EXPANSION_DEPTH {
            let n = self.rt.interner.name(name).to_string();
            return Err(ExpandError::at(
                form.span,
                format!("macro expansion nested more than {MAX_EXPANSION_DEPTH} deep, in `{n}`: does its expansion always contain another use of it?"),
            ));
        }
        let m = match def {
            MacroDef::Rules(m) => m,
            MacroDef::Proc(p) => return self.expand_proc_macro(&p, form),
        };
        for (pattern, template) in &m.rules {
            let mut binds = HashMap::new();
            if self.match_top(&m, pattern, form, &mut binds) {
                let mut renames = HashMap::new();
                let out = self.instantiate(&m, template, &binds, &HashMap::new(), &mut renames, false, form.span)?;
                return Ok(out);
            }
        }
        let n = self.rt.interner.name(m.name).to_string();
        let shown = fixpt_read::write_syntax(form, &self.rt.interner);
        let patterns: Vec<String> = m
            .rules
            .iter()
            .map(|(p, _)| fixpt_read::write_syntax(p, &self.rt.interner))
            .collect();
        Err(ExpandError::at(
            form.span,
            format!("no rule of `{n}` matches {shown}; its patterns are {}", patterns.join("  ")),
        ))
    }

    /// Increase the nesting count for the duration of `f` — the expansion of
    /// one macro use, including everything its output expands to.
    pub(crate) fn nested<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        self.macro_depth += 1;
        let r = f(self);
        self.macro_depth -= 1;
        r
    }

    // -------------------------------------------------------------- matching
    /// The keyword position is not matched: R7RS ignores it.
    fn match_top(&self, m: &Macro, pattern: &Syntax, form: &Syntax, out: &mut HashMap<Sym, M>) -> bool {
        let Datum::List { items: pitems, tail: ptail } = &pattern.datum else { return false };
        let Some((pi, it)) = list_parts(form) else { return false };
        if pitems.is_empty() || pi.is_empty() {
            return false;
        }
        self.match_seq(m, &pitems[1..], ptail.as_deref(), &pi[1..], it, out)
    }

    fn matches(&self, m: &Macro, p: &Syntax, input: &Syntax, out: &mut HashMap<Sym, M>) -> bool {
        match &p.datum {
            Datum::Symbol(s) => {
                if m.is_literal(*s) {
                    return matches!(input.datum, Datum::Symbol(x) if self.same_denotation(x, *s, m.scope));
                }
                if !self.is_underscore(m, *s) {
                    out.insert(*s, M::One(input.clone()));
                }
                true
            }
            Datum::Nil => matches!(&input.datum, Datum::Nil)
                || matches!(&input.datum, Datum::List { items, tail: None } if items.is_empty()),
            Datum::List { items, tail } => match list_parts(input) {
                Some((ii, it)) => self.match_seq(m, items, tail.as_deref(), ii, it, out),
                None => false,
            },
            Datum::Vector(items) => match &input.datum {
                Datum::Vector(ii) => self.match_seq(m, items, None, ii, None, out),
                _ => false,
            },
            _ => datum_equal(&p.datum, &input.datum),
        }
    }

    /// Match pattern elements (with at most one ellipsis) and an optional tail
    /// pattern against input elements and the input's final cdr.
    fn match_seq(
        &self,
        m: &Macro,
        pitems: &[Syntax],
        ptail: Option<&Syntax>,
        iitems: &[Syntax],
        itail: Option<&Syntax>,
        out: &mut HashMap<Sym, M>,
    ) -> bool {
        let ellipsis_at = (0..pitems.len().saturating_sub(1))
            .find(|&i| pitems[i + 1].as_symbol().is_some_and(|s| self.is_ellipsis(m, s)));
        let (before, rep, after) = match ellipsis_at {
            Some(e) => (&pitems[..e], Some(&pitems[e]), &pitems[e + 2..]),
            None => (pitems, None, &pitems[..0]),
        };
        let fixed = before.len() + after.len();
        if iitems.len() < fixed {
            return false;
        }
        for (p, i) in before.iter().zip(iitems) {
            if !self.matches(m, p, i, out) {
                return false;
            }
        }
        let (middle, rest) = match rep {
            Some(_) => {
                let end = iitems.len() - after.len();
                (&iitems[before.len()..end], &iitems[end..])
            }
            // Without an ellipsis, whatever follows the fixed elements is the
            // tail's to match, if there is a tail pattern.
            None => (&iitems[..0], &iitems[before.len()..]),
        };
        if let Some(rep) = rep {
            let vars = self.pattern_vars(m, rep);
            let mut seqs: Vec<Vec<M>> = vec![Vec::new(); vars.len()];
            for i in middle {
                let mut one = HashMap::new();
                if !self.matches(m, rep, i, &mut one) {
                    return false;
                }
                for (k, v) in vars.iter().enumerate() {
                    seqs[k].push(one.remove(v).expect("a matched pattern binds its variables"));
                }
            }
            for (v, seq) in vars.into_iter().zip(seqs) {
                out.insert(v, M::Seq(seq));
            }
            for (p, i) in after.iter().zip(rest) {
                if !self.matches(m, p, i, out) {
                    return false;
                }
            }
            return match ptail {
                Some(t) => self.matches(m, t, &tail_syntax(&[], itail), out),
                None => itail.is_none(),
            };
        }
        match ptail {
            Some(t) => self.matches(m, t, &tail_syntax(rest, itail), out),
            None => rest.is_empty() && itail.is_none(),
        }
    }

    fn pattern_vars(&self, m: &Macro, p: &Syntax) -> Vec<Sym> {
        let mut out = Vec::new();
        self.collect_pattern_vars(m, p, &mut out);
        out
    }

    fn collect_pattern_vars(&self, m: &Macro, p: &Syntax, out: &mut Vec<Sym>) {
        match &p.datum {
            Datum::Symbol(s)
                if !m.is_literal(*s) && !self.is_underscore(m, *s) && !self.is_ellipsis(m, *s) =>
            {
                out.push(*s);
            }
            Datum::List { items, tail } => {
                for i in items {
                    self.collect_pattern_vars(m, i, out);
                }
                if let Some(t) = tail {
                    self.collect_pattern_vars(m, t, out);
                }
            }
            Datum::Vector(items) => {
                for i in items {
                    self.collect_pattern_vars(m, i, out);
                }
            }
            _ => {}
        }
    }

    /// Do two identifiers, each resolved where it now stands, name the same
    /// binding? What a procedural macro's `compare` asks.
    pub(crate) fn same_binding(&self, a: Sym, b: Sym) -> bool {
        let same_name = || self.rt.interner.name(a) == self.rt.interner.name(b);
        match (self.resolve(a), self.resolve(b)) {
            (Some(x), Some(y)) if x == y => true,
            (None | Some(Binding::Global(_)), None | Some(Binding::Global(_))) => same_name(),
            _ => false,
        }
    }

    /// `free-identifier=?`: does the input identifier, where it was used, mean
    /// what the literal means where the macro was defined?
    fn same_denotation(&self, input: Sym, literal: Sym, scope: u32) -> bool {
        let a = self.resolve(input);
        let b = self.resolve_within(literal, scope as usize);
        let same_name = || self.rt.interner.name(input) == self.rt.interner.name(literal);
        match (a, b) {
            (Some(x), Some(y)) if x == y => true,
            // A global is bound in the expander's table the first time it is
            // referred to, so "unbound" and "global" are the same variable when
            // they have the same name.
            (None | Some(Binding::Global(_)), None | Some(Binding::Global(_))) => same_name(),
            _ => false,
        }
    }

    // ------------------------------------------------------------- templates
    #[allow(clippy::too_many_arguments)]
    fn instantiate(
        &mut self,
        m: &Macro,
        t: &Syntax,
        base: &HashMap<Sym, M>,
        over: &HashMap<Sym, M>,
        renames: &mut HashMap<Sym, Sym>,
        escaped: bool,
        span: Span,
    ) -> R<Syntax> {
        match &t.datum {
            Datum::Symbol(s) => match over.get(s).or_else(|| base.get(s)) {
                Some(M::One(x)) => Ok(x.clone()),
                Some(M::Seq(_)) => {
                    let n = self.rt.interner.name(*s).to_string();
                    Err(ExpandError::at(
                        t.span,
                        format!("pattern variable `{n}` matched a sequence, so it needs `...` after it here"),
                    ))
                }
                None => {
                    let a = match renames.get(s) {
                        Some(a) => *a,
                        None => {
                            let a = self.alias(*s, m.scope);
                            renames.insert(*s, a);
                            a
                        }
                    };
                    Ok(Syntax::symbol(span, a))
                }
            },
            Datum::List { items, tail } => {
                // `(... template)`: the ellipsis is an ordinary identifier
                // inside.
                if !escaped
                    && items.len() == 2
                    && tail.is_none()
                    && items[0].as_symbol().is_some_and(|s| self.is_ellipsis(m, s))
                {
                    return self.instantiate(m, &items[1], base, over, renames, true, span);
                }
                let mut out = Vec::with_capacity(items.len());
                self.instantiate_items(m, items, base, over, renames, escaped, span, &mut out)?;
                let tail = match tail {
                    Some(tl) => Some(self.instantiate(m, tl, base, over, renames, escaped, span)?),
                    None => None,
                };
                Ok(normalize_list(span, out, tail))
            }
            Datum::Vector(items) => {
                let mut out = Vec::with_capacity(items.len());
                self.instantiate_items(m, items, base, over, renames, escaped, span, &mut out)?;
                Ok(Syntax::new(span, Datum::Vector(out)))
            }
            _ => Ok(t.clone()),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn instantiate_items(
        &mut self,
        m: &Macro,
        items: &[Syntax],
        base: &HashMap<Sym, M>,
        over: &HashMap<Sym, M>,
        renames: &mut HashMap<Sym, Sym>,
        escaped: bool,
        span: Span,
        out: &mut Vec<Syntax>,
    ) -> R<()> {
        let mut i = 0;
        while i < items.len() {
            let mut depth = 0;
            if !escaped {
                while items
                    .get(i + 1 + depth)
                    .and_then(|x| x.as_symbol())
                    .is_some_and(|s| self.is_ellipsis(m, s))
                {
                    depth += 1;
                }
            }
            if depth == 0 {
                out.push(self.instantiate(m, &items[i], base, over, renames, escaped, span)?);
            } else {
                self.expand_ellipsis(m, &items[i], base, over, renames, depth, span, out)?;
            }
            i += 1 + depth;
        }
        Ok(())
    }

    /// `template ...` (repeated `depth` times): one copy of `template` per
    /// element of the sequences its pattern variables matched.
    #[allow(clippy::too_many_arguments)]
    fn expand_ellipsis(
        &mut self,
        m: &Macro,
        t: &Syntax,
        base: &HashMap<Sym, M>,
        over: &HashMap<Sym, M>,
        renames: &mut HashMap<Sym, Sym>,
        depth: usize,
        span: Span,
        out: &mut Vec<Syntax>,
    ) -> R<()> {
        let mut vars = Vec::new();
        self.sequence_vars(t, base, over, &mut vars);
        if vars.is_empty() {
            return Err(ExpandError::at(
                t.span,
                "no pattern variable that matched a sequence appears before this `...`",
            ));
        }
        let len_of = |v: &Sym| match over.get(v).or_else(|| base.get(v)) {
            Some(M::Seq(s)) => s.len(),
            _ => 0,
        };
        let n = len_of(&vars[0]);
        if let Some(bad) = vars.iter().find(|v| len_of(v) != n) {
            let a = self.rt.interner.name(vars[0]).to_string();
            let b = self.rt.interner.name(*bad).to_string();
            return Err(ExpandError::at(
                t.span,
                format!("`{a}` and `{b}` matched sequences of different lengths, so `...` cannot pair them"),
            ));
        }
        for k in 0..n {
            let mut inner = over.clone();
            for v in &vars {
                let Some(M::Seq(s)) = over.get(v).or_else(|| base.get(v)) else { unreachable!() };
                inner.insert(*v, s[k].clone());
            }
            if depth == 1 {
                out.push(self.instantiate(m, t, base, &inner, renames, false, span)?);
            } else {
                self.expand_ellipsis(m, t, base, &inner, renames, depth - 1, span, out)?;
            }
        }
        Ok(())
    }

    /// Pattern variables in `t` currently bound to sequences.
    fn sequence_vars(&self, t: &Syntax, base: &HashMap<Sym, M>, over: &HashMap<Sym, M>, out: &mut Vec<Sym>) {
        match &t.datum {
            Datum::Symbol(s)
                if matches!(over.get(s).or_else(|| base.get(s)), Some(M::Seq(_))) && !out.contains(s) =>
            {
                out.push(*s);
            }
            Datum::List { items, tail } => {
                for i in items {
                    self.sequence_vars(i, base, over, out);
                }
                if let Some(tl) = tail {
                    self.sequence_vars(tl, base, over, out);
                }
            }
            Datum::Vector(items) => {
                for i in items {
                    self.sequence_vars(i, base, over, out);
                }
            }
            _ => {}
        }
    }
}

/// A list's elements and final cdr, or `None` if it is not a list.
fn list_parts(s: &Syntax) -> Option<(&[Syntax], Option<&Syntax>)> {
    match &s.datum {
        Datum::Nil => Some((&[], None)),
        Datum::List { items, tail } => Some((items, tail.as_deref())),
        _ => None,
    }
}

/// The syntax for what is left of a list: its remaining elements and cdr.
fn tail_syntax(rest: &[Syntax], tail: Option<&Syntax>) -> Syntax {
    let span = rest
        .first()
        .map(|s| s.span)
        .or(tail.map(|t| t.span))
        .unwrap_or(Span::new(fixpt_read::FileId(0), 0, 0));
    normalize_list(span, rest.to_vec(), tail.cloned())
}

/// Build a list, flattening a tail that is itself a list so that
/// `(a . (b c))` comes out as the proper list `(a b c)` the expander expects.
fn normalize_list(span: Span, mut items: Vec<Syntax>, mut tail: Option<Syntax>) -> Syntax {
    loop {
        match tail {
            Some(Syntax { datum: Datum::Nil, .. }) => tail = None,
            Some(Syntax { datum: Datum::List { items: more, tail: t }, .. }) => {
                items.extend(more);
                tail = t.map(|b| *b);
            }
            _ => break,
        }
    }
    if items.is_empty() {
        return tail.unwrap_or_else(|| Syntax::new(span, Datum::Nil));
    }
    Syntax::new(span, Datum::List { items, tail: tail.map(Box::new) })
}

/// `equal?` on the self-evaluating data a pattern may contain.
fn datum_equal(a: &Datum, b: &Datum) -> bool {
    match (a, b) {
        (Datum::Bool(x), Datum::Bool(y)) => x == y,
        (Datum::Char(x), Datum::Char(y)) => x == y,
        (Datum::Str(x), Datum::Str(y)) => x == y,
        (Datum::Number(x), Datum::Number(y)) => x == y,
        (Datum::Bytevector(x), Datum::Bytevector(y)) => x == y,
        _ => false,
    }
}
