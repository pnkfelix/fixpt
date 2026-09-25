//! Parsing FX-91 source into the abstract syntax — `token.scm`.
//!
//! Alpha-renaming happens here: every binder gets a fresh identity, so the
//! type checker can use flat, mutable environments keyed by that identity
//! rather than threading scopes. `token.scm` says the parser "performs no
//! syntax check"; this one reports structural problems rather than reading
//! past the end of a list, which is strictly more informative and cannot
//! change the result for well-formed input.

use crate::ast::{AlphaId, Arena, Domain, Fx, FxId, Kind, LiteralValue};
use crate::error::{FxError, R};
use crate::syms::{Syms, KEYWORD_FIELDS};
use fixpt_read::{Datum, Interner, Num, Span, Sym, Syntax};
use std::collections::HashSet;

pub struct Parser {
    pub arena: Arena,
    pub interner: Interner,
    pub syms: Syms,
    keywords: HashSet<Sym>,
    /// The environment the built-in `fx` module's names live in.
    pub init_alpha: AlphaId,
    /// While the `fx` module itself is being built, its own names must be
    /// allowed as binders. `token.scm` guards the keyword check the same way.
    pub initializing: bool,
}

impl Default for Parser {
    fn default() -> Parser {
        Parser::new()
    }
}

impl Parser {
    pub fn new() -> Parser {
        let mut interner = Interner::new();
        let mut arena = Arena::new();
        let syms = Syms::new(&mut interner);
        let keywords: HashSet<Sym> =
            KEYWORD_FIELDS.iter().map(|n| interner.intern(n)).collect();
        let init_alpha = arena.empty_alpha();
        Parser { arena, interner, syms, keywords, init_alpha, initializing: false }
    }

    /// The reserved words.
    pub fn keywords(&self) -> impl Iterator<Item = Sym> + '_ {
        self.keywords.iter().copied()
    }

    // ----------------------------------------------------------- utilities
    fn items<'s>(&self, s: &'s Syntax) -> R<&'s [Syntax]> {
        s.as_proper_list()
            .ok_or_else(|| FxError::user(s.span, "expected a list"))
    }

    fn expect_len(&self, s: &Syntax, items: &[Syntax], n: usize, what: &str) -> R<()> {
        if items.len() == n {
            Ok(())
        } else {
            Err(FxError::user(
                s.span,
                format!("{what} needs {} subform(s), found {}", n - 1, items.len() - 1),
            ))
        }
    }

    fn symbol(&self, s: &Syntax, what: &str) -> R<Sym> {
        s.as_symbol().ok_or_else(|| FxError::user(s.span, format!("{what} must be a symbol")))
    }

    fn name(&self, sym: Sym) -> &str {
        self.interner.name(sym)
    }

    fn glue(&mut self, prefix: Sym, rest: Sym) -> Sym {
        let text = format!("{}{}", self.interner.name(prefix), self.interner.name(rest));
        self.interner.intern(&text)
    }

    /// `new-identifier`: a fresh, printable name with its own counter. The
    /// counter is deliberately separate from the alpha counter — the
    /// conformance normaliser relies on the two namespaces staying apart.
    pub fn new_identifier(&mut self, base: &str) -> Sym {
        self.arena.gensym_counter += 1;
        let text = format!("{base}-{}", self.arena.gensym_counter);
        self.interner.intern(&text)
    }

    // ------------------------------------------------------------- symbols
    fn parse_symbol(&mut self, alpha: AlphaId, domain: Domain, sym: Sym, span: Span) -> FxId {
        let name = self.arena.alpha_lookup(alpha, sym);
        self.arena.identifier_variable(span, sym, name, domain)
    }

    /// A symbol in binding position, which may not be a reserved word.
    fn parse_binding_symbol(
        &mut self,
        alpha: AlphaId,
        domain: Domain,
        sym: Sym,
        span: Span,
    ) -> R<FxId> {
        if !self.initializing && self.keywords.contains(&sym) {
            return Err(FxError::user(
                span,
                format!("trying to redefine FX keyword: {}", self.name(sym)),
            ));
        }
        Ok(self.parse_symbol(alpha, domain, sym, span))
    }

    fn extend(&mut self, alpha: AlphaId, names: &[Sym]) -> AlphaId {
        let bindings: Vec<(Sym, u32)> =
            names.iter().map(|n| (*n, self.arena.fresh_name())).collect();
        self.arena.extend_alpha(alpha, bindings)
    }

    // --------------------------------------------------------------- kinds
    pub fn parse_kexp(&mut self, s: &Syntax) -> R<Kind> {
        if let Some(sym) = s.as_symbol() {
            if sym == self.syms.type_ {
                return Ok(Kind::Type);
            }
            if sym == self.syms.effect {
                return Ok(Kind::Effect);
            }
        }
        // `(dfunc k…)`. token.scm takes the cdr without checking the head, so
        // `(anything k…)` is a dfunc; that is reproduced here.
        if let Some(items) = s.as_proper_list()
            && !items.is_empty()
        {
            let kinds = items[1..].iter().map(|k| self.parse_kexp(k)).collect::<R<Vec<_>>>()?;
            return Ok(Kind::DFunc(kinds));
        }
        Err(FxError::user(s.span, "incorrect kind expression"))
    }

    // -------------------------------------------------------- descriptions
    pub fn parse_dexp(&mut self, alpha: AlphaId, s: &Syntax) -> R<FxId> {
        if self.is_sugar(s) {
            return self.parse_sugar_dexp(alpha, s);
        }
        if let Some(sym) = s.as_symbol() {
            return Ok(self.parse_symbol(alpha, Domain::Description, sym, s.span));
        }
        let items = self.items(s)?;
        if items.is_empty() {
            return Err(FxError::user(s.span, "illegal () as description"));
        }
        let head = items[0].as_symbol();
        let sy = self.syms.clone();
        match head {
            Some(h) if h == sy.dlambda => self.parse_dlambda(alpha, s, items),
            Some(h) if h == sy.select => self.parse_select(alpha, s, items),
            Some(h) if h == sy.maxeff => self.parse_maxeff(alpha, s, items),
            Some(h) if h == sy.subr || h == sy.arrow => self.parse_subr(alpha, s, items),
            Some(h) if h == sy.poly => self.parse_poly(alpha, s, items),
            Some(h) if h == sy.moduleof => self.parse_moduleof(alpha, s, items),
            Some(h) if h == sy.sumof => self.parse_sum_or_product(alpha, s, items, true),
            Some(h) if h == sy.productof => self.parse_sum_or_product(alpha, s, items, false),
            _ => self.parse_dapp(alpha, s, items),
        }
    }

    /// `((id kind) …)` binder lists, shared by dlambda, poly and plambda.
    fn parse_kind_bindings(
        &mut self,
        alpha: AlphaId,
        s: &Syntax,
        domain: Domain,
    ) -> R<(AlphaId, Vec<FxId>, Vec<Kind>)> {
        let bindings = self.items(s)?;
        let mut names = Vec::with_capacity(bindings.len());
        let mut kind_syntax = Vec::with_capacity(bindings.len());
        for b in bindings {
            let parts = self.items(b)?;
            if parts.len() != 2 {
                return Err(FxError::user(b.span, "a binding must be `(name kind)`"));
            }
            names.push(self.symbol(&parts[0], "a binder")?);
            kind_syntax.push(parts[1].clone());
        }
        let new_alpha = self.extend(alpha, &names);
        let mut ids = Vec::with_capacity(names.len());
        for (n, b) in names.iter().zip(bindings) {
            ids.push(self.parse_binding_symbol(new_alpha, domain, *n, b.span)?);
        }
        let kinds = kind_syntax.iter().map(|k| self.parse_kexp(k)).collect::<R<Vec<_>>>()?;
        Ok((new_alpha, ids, kinds))
    }

    fn parse_dlambda(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 3, "dlambda")?;
        let (new_alpha, ids, kinds) =
            self.parse_kind_bindings(alpha, &items[1], Domain::Description)?;
        let body = self.parse_dexp(new_alpha, &items[2])?;
        Ok(self.arena.add(s.span, Fx::DLambda { ids, kinds, body }))
    }

    fn parse_poly(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 3, "poly")?;
        let (new_alpha, ids, kinds) =
            self.parse_kind_bindings(alpha, &items[1], Domain::Description)?;
        let body = self.parse_dexp(new_alpha, &items[2])?;
        Ok(self.arena.add(s.span, Fx::Poly { ids, kinds, body }))
    }

    fn parse_select(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 3, "select")?;
        let module = self.parse_exp(alpha, &items[1])?;
        let id = self.symbol(&items[2], "a select field")?;
        Ok(self.arena.add(s.span, Fx::Select { module, id }))
    }

    fn parse_maxeff(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        let effects =
            items[1..].iter().map(|e| self.parse_dexp(alpha, e)).collect::<R<Vec<_>>>()?;
        Ok(self.arena.add(s.span, Fx::MaxEff(effects)))
    }

    /// `(subr effect ((id type)…) body)`.
    ///
    /// The bindings are *dependent*: each type is parsed in the environment
    /// before its own binder but after all earlier ones, so a later parameter's
    /// type may mention an earlier parameter. The effect is parsed in the
    /// original environment, the body in the final one.
    fn parse_subr(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 4, "subr")?;
        let effect = self.parse_dexp(alpha, &items[1])?;
        let bindings = self.items(&items[2])?;
        let mut env = alpha;
        let mut ids = Vec::with_capacity(bindings.len());
        let mut types = Vec::with_capacity(bindings.len());
        for b in bindings {
            let parts = self.items(b)?;
            if parts.len() != 2 {
                return Err(FxError::user(b.span, "a subr binding must be `(name type)`"));
            }
            let name = self.symbol(&parts[0], "a parameter")?;
            let old_env = env;
            env = self.extend(old_env, &[name]);
            ids.push(self.parse_binding_symbol(env, Domain::Value, name, parts[0].span)?);
            types.push(self.parse_dexp(old_env, &parts[1])?);
        }
        let body = self.parse_dexp(env, &items[3])?;
        Ok(self.arena.add(s.span, Fx::Subr { effect, ids, types, body }))
    }

    fn parse_moduleof(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        let sy = self.syms.clone();
        let abss = self.expand_group_sugar(&items[1..], sy.abs)?;
        let descs = self.expand_group_sugar(&items[1..], sy.desc)?;
        let vals = self.expand_group_sugar(&items[1..], sy.val)?;

        let abs_names: Vec<Sym> = abss.iter().map(|(n, _)| *n).collect();
        let abs_alpha = self.extend(alpha, &abs_names);
        let desc_names: Vec<Sym> = descs.iter().map(|(n, _)| *n).collect();
        let desc_alpha = self.extend(abs_alpha, &desc_names);
        let val_names: Vec<Sym> = vals.iter().map(|(n, _)| *n).collect();
        let new_alpha = self.extend(desc_alpha, &val_names);

        let mut abs_ids = Vec::new();
        let mut abs_kinds = Vec::new();
        for (n, k) in &abss {
            abs_ids.push(self.parse_binding_symbol(abs_alpha, Domain::Description, *n, k.span)?);
            abs_kinds.push(self.parse_kexp(k)?);
        }
        let mut desc_ids = Vec::new();
        let mut desc_descs = Vec::new();
        for (n, d) in &descs {
            desc_ids.push(self.parse_binding_symbol(desc_alpha, Domain::Description, *n, d.span)?);
            desc_descs.push(self.parse_dexp(abs_alpha, d)?);
        }
        let mut val_ids = Vec::new();
        let mut val_types = Vec::new();
        for (n, t) in &vals {
            val_ids.push(self.parse_binding_symbol(new_alpha, Domain::Value, *n, t.span)?);
            val_types.push(self.parse_dexp(new_alpha, t)?);
        }
        Ok(self.arena.add(
            s.span,
            Fx::ModuleOf { abs_ids, abs_kinds, desc_ids, desc_descs, val_ids, val_types },
        ))
    }

    /// `(val (a b c) type)` abbreviates three `val` clauses sharing one type.
    /// The same sugar serves `abs` and `desc`.
    fn expand_group_sugar(&mut self, clauses: &[Syntax], keyword: Sym) -> R<Vec<(Sym, Syntax)>> {
        let mut out = Vec::new();
        for clause in clauses {
            let Some(parts) = clause.as_proper_list() else { continue };
            if parts.len() != 3 || parts[0].as_symbol() != Some(keyword) {
                continue;
            }
            match parts[1].as_proper_list() {
                Some(names) => {
                    for n in names {
                        out.push((self.symbol(n, "a name")?, parts[2].clone()));
                    }
                }
                None => out.push((self.symbol(&parts[1], "a name")?, parts[2].clone())),
            }
        }
        Ok(out)
    }

    fn parse_sum_or_product(
        &mut self,
        alpha: AlphaId,
        s: &Syntax,
        items: &[Syntax],
        is_sum: bool,
    ) -> R<FxId> {
        let mut tags = Vec::new();
        let mut types = Vec::new();
        for clause in &items[1..] {
            let parts = self.items(clause)?;
            if parts.len() != 2 {
                return Err(FxError::user(clause.span, "expected `(tag type)`"));
            }
            tags.push(self.symbol(&parts[0], "a tag")?);
            types.push(self.parse_dexp(alpha, &parts[1])?);
        }
        Ok(self.arena.add(
            s.span,
            if is_sum { Fx::SumOf { tags, types } } else { Fx::ProductOf { tags, types } },
        ))
    }

    fn parse_dapp(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        let rator = self.parse_dexp(alpha, &items[0])?;
        let rands =
            items[1..].iter().map(|r| self.parse_dexp(alpha, r)).collect::<R<Vec<_>>>()?;
        Ok(self.arena.add(s.span, Fx::DApp { rator, rands }))
    }

    // --------------------------------------------------------- expressions
    pub fn parse_exp(&mut self, alpha: AlphaId, s: &Syntax) -> R<FxId> {
        if let Some(kind) = self.literal_kind(s) {
            return self.parse_literal(s, kind);
        }
        if self.is_sugar(s) {
            return self.parse_sugar_exp(alpha, s);
        }
        if let Some(sym) = s.as_symbol() {
            return Ok(self.parse_symbol(alpha, Domain::Value, sym, s.span));
        }
        let items = self.items(s)?;
        if items.is_empty() {
            return Err(FxError::user(s.span, "illegal () as expression"));
        }
        let head = items[0].as_symbol();
        let sy = self.syms.clone();
        match head {
            Some(h) if h == sy.lambda => self.parse_lambda(alpha, s, items),
            Some(h) if h == sy.let_ => self.parse_let(alpha, s, items),
            Some(h) if h == sy.plambda => self.parse_plambda(alpha, s, items),
            Some(h) if h == sy.proj => self.parse_proj(alpha, s, items),
            Some(h) if h == sy.module => self.parse_module(alpha, s, items),
            Some(h) if h == sy.with => self.parse_with_extend(alpha, s, items, true),
            Some(h) if h == sy.extend => self.parse_with_extend(alpha, s, items, false),
            Some(h) if h == sy.if_ => self.parse_if(alpha, s, items),
            Some(h) if h == sy.open => self.parse_open_close(alpha, s, items, true),
            Some(h) if h == sy.close => self.parse_open_close(alpha, s, items, false),
            Some(h) if h == sy.begin => self.parse_begin(alpha, s, items),
            Some(h) if h == sy.load => self.parse_load(alpha, s, items),
            Some(h) if h == sy.the => self.parse_the(alpha, s, items),
            Some(h) if h == sy.does => self.parse_does(alpha, s, items),
            Some(h) if h == sy.sum => self.parse_sum(alpha, s, items),
            Some(h) if h == sy.product => self.parse_product(alpha, s, items),
            Some(h) if h == sy.tagcase => self.parse_tagcase(alpha, s, items),
            Some(h) if h == sy.extract => self.parse_extract(alpha, s, items),
            _ => self.parse_app(alpha, s, items),
        }
    }

    // ------------------------------------------------------------ literals
    /// The literal table from `standard.scm`, in registration order — which is
    /// the order `literal?` tests them in, and so is load-bearing.
    ///
    /// Note that `integer?` is tested before the float case, and the float case
    /// itself excludes integers: `(and (real? e) (not (integer? e)))`. So `1.0`
    /// is an `int`, deliberately. FX-87 reaches the same outcome by accident,
    /// through ordering alone; here it is written down.
    fn literal_kind(&self, s: &Syntax) -> Option<LiteralKind> {
        match &s.datum {
            Datum::Bool(_) => Some(LiteralKind::Bool),
            Datum::Symbol(sym) if *sym == self.syms.unit_value => Some(LiteralKind::Unit),
            Datum::Number(n) if is_scheme_integer(n) => Some(LiteralKind::Int),
            Datum::Number(_) => Some(LiteralKind::Float),
            Datum::Char(_) => Some(LiteralKind::Char),
            Datum::Str(_) => Some(LiteralKind::Str),
            Datum::Symbol(sym) if *sym == self.syms.nil => Some(LiteralKind::Nil),
            Datum::List { items, .. } => match items.first().and_then(|h| h.as_symbol()) {
                Some(h) if h == self.syms.symbol => Some(LiteralKind::SymLit),
                Some(h) if h == self.syms.quote => Some(LiteralKind::Sexp),
                _ => None,
            },
            _ => None,
        }
    }

    /// A literal parses as a *reference to the `fx` module's witness variable*
    /// for its type — `an-int`, `a-string` and so on — with the value cached on
    /// the node. That is how a literal gets its type without the checker
    /// knowing anything about literals.
    fn parse_literal(&mut self, s: &Syntax, kind: LiteralKind) -> R<FxId> {
        let name = match kind {
            LiteralKind::Bool => self.syms.a_bool,
            LiteralKind::Unit => self.syms.an_unit,
            LiteralKind::Int => self.syms.an_int,
            LiteralKind::Float => self.syms.a_float,
            LiteralKind::Char => self.syms.a_char,
            LiteralKind::Str => self.syms.a_string,
            LiteralKind::SymLit => self.syms.a_sym,
            LiteralKind::Nil => self.syms.a_listof,
            LiteralKind::Sexp => self.syms.a_sexp,
        };
        let init = self.init_alpha;
        let node = self.parse_symbol(init, Domain::Value, name, s.span);
        let value = match kind {
            // `(symbol foo)` caches `(quote foo)`.
            LiteralKind::SymLit => {
                let items = self.items(s)?;
                if items.len() != 2 {
                    return Err(FxError::user(s.span, "expected `(symbol name)`"));
                }
                LiteralValue::SelfEvaluating(Syntax::list(
                    s.span,
                    vec![Syntax::symbol(s.span, self.syms.quote), items[1].clone()],
                ))
            }
            // `'datum` caches the datum converted into sexp's sum shape.
            LiteralKind::Sexp => {
                let items = self.items(s)?;
                if items.len() != 2 {
                    return Err(FxError::user(s.span, "expected `(quote datum)`"));
                }
                LiteralValue::Sexp(items[1].clone())
            }
            _ => LiteralValue::SelfEvaluating(s.clone()),
        };
        self.arena.exp_info_mut(node).literal = Some(value);
        Ok(node)
    }

    // ------------------------------------------------------- kernel forms
    /// `(lambda ((x t) … | x …) body)`. A bare parameter with no type gets a
    /// fresh weak unification variable, which is what makes declaration-free
    /// programs inferable. Bindings are dependent, as in `subr`.
    fn parse_lambda(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 3, "lambda")?;
        let bindings = self.items(&items[1])?;
        let mut env = alpha;
        let mut ids = Vec::with_capacity(bindings.len());
        let mut types = Vec::with_capacity(bindings.len());
        let mut user_types = Vec::with_capacity(bindings.len());
        for b in bindings {
            let (name, ty_syntax) = match &b.datum {
                Datum::Symbol(sym) => (*sym, None),
                _ => {
                    let parts = self.items(b)?;
                    if parts.len() != 2 {
                        return Err(FxError::user(b.span, "a parameter is `name` or `(name type)`"));
                    }
                    (self.symbol(&parts[0], "a parameter")?, Some(parts[1].clone()))
                }
            };
            let old_env = env;
            env = self.extend(old_env, &[name]);
            ids.push(self.parse_binding_symbol(env, Domain::Value, name, b.span)?);
            match &ty_syntax {
                Some(t) => {
                    types.push(self.parse_dexp(old_env, t)?);
                    user_types.push(true);
                }
                None => {
                    // Named after its own alpha number, as
                    // `make-unification-variable` does: the name becomes
                    // visible if generalisation later turns it into a binder.
                    let next = self.arena.alpha_counter;
                    let user_name = self.interner.intern(&next.to_string());
                    types.push(self.arena.unification_variable(b.span, user_name, true, Kind::Type));
                    user_types.push(false);
                }
            }
        }
        let body = self.parse_exp(env, &items[2])?;
        Ok(self.arena.add(s.span, Fx::Lambda { ids, types, user_types, body }))
    }

    fn parse_let(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 3, "let")?;
        let bindings = self.items(&items[1])?;
        let mut names = Vec::with_capacity(bindings.len());
        let mut exps = Vec::with_capacity(bindings.len());
        for b in bindings {
            let parts = self.items(b)?;
            if parts.len() != 2 {
                return Err(FxError::user(b.span, "a let binding is `(name expression)`"));
            }
            names.push(self.symbol(&parts[0], "a binder")?);
            exps.push(self.parse_exp(alpha, &parts[1])?);
        }
        let new_alpha = self.extend(alpha, &names);
        let mut ids = Vec::with_capacity(names.len());
        for (n, b) in names.iter().zip(bindings) {
            ids.push(self.parse_binding_symbol(new_alpha, Domain::Value, *n, b.span)?);
        }
        let body = self.parse_exp(new_alpha, &items[2])?;
        Ok(self.arena.add(s.span, Fx::Let { ids, exps, body }))
    }

    fn parse_plambda(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 3, "plambda")?;
        let (new_alpha, ids, kinds) =
            self.parse_kind_bindings(alpha, &items[1], Domain::Description)?;
        let body = self.parse_exp(new_alpha, &items[2])?;
        Ok(self.arena.add(s.span, Fx::PLambda { ids, kinds, body }))
    }

    fn parse_proj(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        if items.len() < 2 {
            return Err(FxError::user(s.span, "proj needs an expression"));
        }
        let exp = self.parse_exp(alpha, &items[1])?;
        let descs =
            items[2..].iter().map(|d| self.parse_dexp(alpha, d)).collect::<R<Vec<_>>>()?;
        Ok(self.arena.add(s.span, Fx::Proj { exp, descs }))
    }

    fn parse_if(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 4, "if")?;
        let test = self.parse_exp(alpha, &items[1])?;
        let then = self.parse_exp(alpha, &items[2])?;
        let els = self.parse_exp(alpha, &items[3])?;
        Ok(self.arena.add(s.span, Fx::If { test, then, els }))
    }

    fn parse_open_close(
        &mut self,
        alpha: AlphaId,
        s: &Syntax,
        items: &[Syntax],
        is_open: bool,
    ) -> R<FxId> {
        // `close` is not on *fx-keywords*, and `*allow-close-special-form*`
        // gates it; when off it is an ordinary application. It defaults on.
        self.expect_len(s, items, 2, if is_open { "open" } else { "close" })?;
        let inner = self.parse_exp(alpha, &items[1])?;
        Ok(self.arena.add(s.span, if is_open { Fx::Open(inner) } else { Fx::Close(inner) }))
    }

    fn parse_begin(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        let exps = items[1..].iter().map(|e| self.parse_exp(alpha, e)).collect::<R<Vec<_>>>()?;
        Ok(self.arena.add(s.span, Fx::Begin(exps)))
    }

    fn parse_load(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 2, "load")?;
        let path = items[1]
            .as_str()
            .ok_or_else(|| FxError::user(items[1].span, "load only accepts strings"))?;
        Ok(self.arena.add(
            s.span,
            Fx::Load { path: path.to_string(), alpha, parsed: None },
        ))
    }

    fn parse_the(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 3, "the")?;
        let ty = self.parse_dexp(alpha, &items[1])?;
        let exp = self.parse_exp(alpha, &items[2])?;
        Ok(self.arena.add(s.span, Fx::The { ty, exp }))
    }

    fn parse_does(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        // `*allow-does-special-form*` defaults to #f, so under the reference's
        // own settings `(does x y)` is an ordinary application. Matching that
        // is what makes the conformance corpus agree.
        self.parse_app(alpha, s, items)
    }

    fn parse_sum(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 4, "sum")?;
        let ty = self.parse_dexp(alpha, &items[1])?;
        let tag = self.symbol(&items[2], "a tag")?;
        let exp = self.parse_exp(alpha, &items[3])?;
        Ok(self.arena.add(s.span, Fx::Sum { ty, tag, exp }))
    }

    fn parse_product(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        if items.len() < 2 {
            return Err(FxError::user(s.span, "product needs a type"));
        }
        let ty = self.parse_dexp(alpha, &items[1])?;
        let exps = items[2..].iter().map(|e| self.parse_exp(alpha, e)).collect::<R<Vec<_>>>()?;
        Ok(self.arena.add(s.span, Fx::Product { ty, exps }))
    }

    fn parse_tagcase(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 6, "tagcase")?;
        let ty = self.parse_dexp(alpha, &items[1])?;
        let exp = self.parse_exp(alpha, &items[2])?;
        let tag = self.symbol(&items[3], "a tag")?;
        let success = self.parse_exp(alpha, &items[4])?;
        let failure = self.parse_exp(alpha, &items[5])?;
        Ok(self.arena.add(s.span, Fx::TagCase { ty, exp, tag, success, failure }))
    }

    fn parse_extract(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        self.expect_len(s, items, 4, "extract")?;
        let ty = self.parse_dexp(alpha, &items[1])?;
        let exp = self.parse_exp(alpha, &items[2])?;
        let tag = self.symbol(&items[3], "a tag")?;
        Ok(self.arena.add(s.span, Fx::Extract { ty, exp, tag }))
    }

    fn parse_app(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        let rator = self.parse_exp(alpha, &items[0])?;
        let rands = items[1..].iter().map(|r| self.parse_exp(alpha, r)).collect::<R<Vec<_>>>()?;
        Ok(self.arena.add(s.span, Fx::App { rator, rands }))
    }

    /// `with` and `extend` keep their bodies unparsed: alpha-renaming the body
    /// needs the module's *type*, which is not known until checking time.
    fn parse_with_extend(
        &mut self,
        alpha: AlphaId,
        s: &Syntax,
        items: &[Syntax],
        is_with: bool,
    ) -> R<FxId> {
        self.expect_len(s, items, 3, if is_with { "with" } else { "extend" })?;
        let module = self.parse_exp(alpha, &items[1])?;
        let body =
            self.arena.add(items[2].span, Fx::Unparsed { alpha, syntax: items[2].clone() });
        let text = items[1].clone();
        Ok(self.arena.add(
            s.span,
            if is_with {
                Fx::With { module, body, text }
            } else {
                Fx::Extend { module, body, text }
            },
        ))
    }

    // ----------------------------------------------------------- modules
    fn parse_module(&mut self, alpha: AlphaId, s: &Syntax, items: &[Syntax]) -> R<FxId> {
        let sy = self.syms.clone();
        // `define-datatype` stands for several definitions, so it is expanded
        // before anything is scanned.
        let mut clauses: Vec<Syntax> = Vec::new();
        for c in &items[1..] {
            match self.expand_define_datatype(c)? {
                Some(expanded) => clauses.extend(expanded),
                None => clauses.push(c.clone()),
            }
        }

        let abss = self.clauses_with(&clauses, sy.define_abstraction);
        let descs = self.clauses_with(&clauses, sy.define_description);
        let mut vals = Vec::new();
        for d in self.clauses_with(&clauses, sy.define) {
            vals.push(self.expand_define_sugar(&d)?);
        }
        let typeds = self.clauses_with(&clauses, sy.define_typed);

        let abs_names: Vec<Sym> = abss
            .iter()
            .map(|c| self.symbol(&self.items(c)?[1], "an abstraction name"))
            .collect::<R<Vec<_>>>()?;
        let ups: Vec<Sym> =
            abs_names.iter().map(|n| self.glue(sy.up_prefix, *n)).collect();
        let downs: Vec<Sym> =
            abs_names.iter().map(|n| self.glue(sy.down_prefix, *n)).collect();
        let desc_names: Vec<Sym> = descs
            .iter()
            .map(|c| self.symbol(&self.items(c)?[1], "a description name"))
            .collect::<R<Vec<_>>>()?;
        let val_names: Vec<Sym> =
            vals.iter().map(|c| self.symbol(&self.items(c)?[1], "a name")).collect::<R<Vec<_>>>()?;
        let typed_names: Vec<Sym> = typeds
            .iter()
            .map(|c| self.symbol(&self.items(c)?[1], "a name"))
            .collect::<R<Vec<_>>>()?;

        let desc_alpha = self.extend(alpha, &abs_names);
        let mut rest: Vec<Sym> = Vec::new();
        rest.extend_from_slice(&ups);
        rest.extend_from_slice(&downs);
        rest.extend_from_slice(&desc_names);
        rest.extend_from_slice(&val_names);
        rest.extend_from_slice(&typed_names);
        let new_alpha = self.extend(desc_alpha, &rest);

        let mut abs_ids = Vec::new();
        let mut abs_kinds = Vec::new();
        let mut abs_descs = Vec::new();
        for (n, c) in abs_names.iter().zip(&abss) {
            let parts = self.items(c)?.to_vec();
            if parts.len() != 4 {
                return Err(FxError::user(
                    c.span,
                    "`define-abstraction` is `(define-abstraction name kind description)`",
                ));
            }
            abs_ids.push(self.parse_binding_symbol(
                desc_alpha,
                Domain::Description,
                *n,
                c.span,
            )?);
            abs_kinds.push(self.parse_kexp(&parts[2])?);
            abs_descs.push(self.parse_dexp(desc_alpha, &parts[3])?);
        }
        let up_ids = ups
            .iter()
            .map(|n| self.parse_binding_symbol(new_alpha, Domain::Value, *n, s.span))
            .collect::<R<Vec<_>>>()?;
        let down_ids = downs
            .iter()
            .map(|n| self.parse_binding_symbol(new_alpha, Domain::Value, *n, s.span))
            .collect::<R<Vec<_>>>()?;

        let mut desc_ids = Vec::new();
        let mut desc_descs = Vec::new();
        for (n, c) in desc_names.iter().zip(&descs) {
            let parts = self.items(c)?.to_vec();
            desc_ids.push(self.parse_binding_symbol(
                new_alpha,
                Domain::Description,
                *n,
                c.span,
            )?);
            desc_descs.push(self.parse_dexp(desc_alpha, &parts[2])?);
        }
        let mut define_ids = Vec::new();
        let mut define_exps = Vec::new();
        for (n, c) in val_names.iter().zip(&vals) {
            let parts = self.items(c)?.to_vec();
            define_ids.push(self.parse_binding_symbol(new_alpha, Domain::Value, *n, c.span)?);
            define_exps.push(self.parse_exp(new_alpha, &parts[2])?);
        }
        let mut typed_ids = Vec::new();
        let mut typed_types = Vec::new();
        let mut typed_exps = Vec::new();
        for (n, c) in typed_names.iter().zip(&typeds) {
            let parts = self.items(c)?.to_vec();
            if parts.len() != 4 {
                return Err(FxError::user(
                    c.span,
                    "`define-typed` is `(define-typed name type expression)`",
                ));
            }
            typed_ids.push(self.parse_binding_symbol(new_alpha, Domain::Value, *n, c.span)?);
            typed_types.push(self.parse_dexp(new_alpha, &parts[2])?);
            typed_exps.push(self.parse_exp(new_alpha, &parts[3])?);
        }

        Ok(self.arena.add(
            s.span,
            Fx::Module {
                abs_ids,
                up_ids,
                down_ids,
                abs_kinds,
                abs_descs,
                desc_ids,
                desc_descs,
                define_ids,
                define_exps,
                typed_ids,
                typed_types,
                typed_exps,
                text: Some(s.clone()),
            },
        ))
    }

    fn clauses_with(&self, clauses: &[Syntax], keyword: Sym) -> Vec<Syntax> {
        clauses
            .iter()
            .filter(|c| {
                c.as_proper_list()
                    .and_then(|p| p.first())
                    .and_then(|h| h.as_symbol())
                    .is_some_and(|h| h == keyword)
            })
            .cloned()
            .collect()
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum LiteralKind {
    Bool,
    Unit,
    Int,
    Float,
    Char,
    Str,
    SymLit,
    Nil,
    Sexp,
}

/// Exposed for the pattern matcher, which needs the same classification.
pub(crate) fn is_scheme_integer_pub(n: &Num) -> bool {
    is_scheme_integer(n)
}

/// Scheme's `integer?`: true of exact integers *and* of inexact reals with no
/// fractional part, which is why `1.0` is not a float here.
fn is_scheme_integer(n: &Num) -> bool {
    match n {
        Num::Int(_) | Num::Big { .. } => true,
        Num::Real(x) => x.fract() == 0.0 && x.is_finite(),
        Num::Ratio(a, b) => {
            // Exact only when it divides evenly; the reader leaves it unreduced.
            matches!((a.as_ref(), b.as_ref()), (Num::Int(x), Num::Int(y)) if *y != 0 && x % y == 0)
        }
    }
}
