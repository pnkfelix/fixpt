//! The module system — `module`, `with`, `extend`, and `load`.
//!
//! FX-91's modules are first-class values with abstract types, which is what
//! makes the language its own configuration language. Three pieces carry the
//! weight:
//!
//! * `define-abstraction t k d` introduces an opaque `t` standing for the
//!   representation `d`, plus coercions `up-t` and `down-t`. Inside the module
//!   they are the identity; outside, `t` is abstract.
//! * `with m e` opens a module's bindings in `e`. The body cannot be
//!   alpha-renamed until `m`'s *type* is known, which is why it was kept
//!   unparsed until now.
//! * `extend m e` evaluates `e` as a `with` over `m` and then inherits
//!   whatever `m` exported that `e` did not shadow.

use crate::ast::{Fx, FxId, Kind};
use crate::check::{kind_eq, Checker};
use crate::env::TkEntry;
use crate::error::{FxError, R};
use fixpt_read::{Reader, SourceMap, SyntaxProfile};

/// A `moduleof`'s three groups, unpacked: abstractions with their kinds,
/// descriptions with their definitions, and values with their types.
type ModuleOfParts = (Vec<FxId>, Vec<Kind>, Vec<FxId>, Vec<FxId>, Vec<FxId>, Vec<FxId>);

impl Checker {
    pub(crate) fn type_of_module(&mut self, id: FxId) -> R<(FxId, FxId)> {
        let span = self.p.arena.span(id);
        let Fx::Module {
            abs_ids,
            abs_kinds,
            abs_descs,
            desc_ids,
            desc_descs,
            define_ids,
            define_exps,
            typed_ids,
            typed_types,
            typed_exps,
            up_ids,
            down_ids,
            ..
        } = self.p.arena.get(id).clone()
        else {
            unreachable!()
        };

        // Kinds first, so that later descriptions can be kind-checked.
        for (i, k) in abs_ids.iter().zip(&abs_kinds) {
            self.tk_set(*i, TkEntry::Kind(k.clone()));
        }
        for (k, d) in abs_kinds.iter().zip(&abs_descs) {
            let got = self.kind_of_dexp(*d)?;
            self.require(kind_eq(k, &got), span, "Incompatible DEFABS kinds")?;
        }
        for (i, d) in desc_ids.iter().zip(&desc_descs) {
            let k = self.kind_of_dexp(*d)?;
            self.tk_set(*i, TkEntry::Kind(k));
        }
        for t in &typed_types {
            let k = self.kind_of_dexp(*t)?;
            self.require(kind_eq(&k, &Kind::Type), span, "DEFTYPED expects types")?;
        }

        // Then the value environment: a placeholder type per plain `define`,
        // the coercions, and the declared types of `define-typed`.
        let mut evaluated_abs = Vec::with_capacity(abs_descs.len());
        for d in &abs_descs {
            evaluated_abs.push(self.evaluate(*d)?);
        }
        for (((i, up), k), d) in
            abs_ids.iter().zip(&up_ids).zip(&abs_kinds).zip(&evaluated_abs)
        {
            if Self::finally_type(k) {
                let ty = self.make_ups(*i, k, *d)?;
                self.tk_set(*up, TkEntry::Type(ty));
            }
        }
        for (((d, down), k), i) in
            evaluated_abs.iter().zip(&down_ids).zip(&abs_kinds).zip(&abs_ids)
        {
            if Self::finally_type(k) {
                let ty = self.make_ups(*d, k, *i)?;
                self.tk_set(*down, TkEntry::Type(ty));
            }
        }
        for i in &define_ids {
            // Strong, not weak: a weak variable here clashes with the final
            // unification below, as `create-tk2-env`'s own comment notes.
            let fresh = self.fresh_unification(span, false, Kind::Type);
            self.tk_set(*i, TkEntry::Type(fresh));
        }
        for (i, d) in desc_ids.iter().zip(&desc_descs) {
            let norm = self.evaluate(*d)?;
            self.store_set(*i, norm);
        }
        for (i, t) in typed_ids.iter().zip(&typed_types) {
            let norm = self.evaluate(*t)?;
            self.tk_set(*i, TkEntry::Type(norm));
        }

        let mut def_ids = define_ids.clone();
        def_ids.extend(typed_ids.iter().copied());
        let mut defs = define_exps.clone();
        defs.extend(typed_exps.iter().copied());

        let mut types = Vec::with_capacity(defs.len());
        let mut effects = Vec::with_capacity(defs.len());
        for e in &defs {
            let (t, ef) = self.type_effect_of_exp(*e)?;
            types.push(t);
            effects.push(ef);
        }
        for (i, t) in def_ids.iter().zip(&types) {
            let declared = self
                .tk_get(*i)
                .and_then(|e| e.as_type())
                .ok_or_else(|| FxError::fatal(span, "a module binding lost its type"))?;
            let ok = self.unify(declared, *t)?;
            if !ok {
                let name = self.render_exp(*i);
                return Err(FxError::user(
                    span,
                    format!("incompatible definition in module: {name}"),
                ));
            }
        }
        let mut val_types = Vec::with_capacity(types.len());
        for t in &types {
            val_types.push(self.evaluate(*t)?);
        }
        let module_type = self.p.arena.add(
            span,
            Fx::ModuleOf {
                abs_ids,
                abs_kinds,
                desc_ids,
                desc_descs,
                val_ids: def_ids,
                val_types,
            },
        );
        let effect = self.p.arena.add(span, Fx::MaxEff(effects));
        let effect = self.evaluate(effect)?;
        Ok((module_type, effect))
    }

    /// A kind that ultimately classifies types, so a coercion can be built.
    fn finally_type(k: &Kind) -> bool {
        matches!(k, Kind::Type | Kind::DFunc(_))
    }

    /// The type of an `up-`/`down-` coercion: `(-> pure ((x d2)) d1)`, wrapped
    /// in a `poly` when the abstraction takes description arguments.
    fn make_ups(&mut self, d1: FxId, kind: &Kind, d2: FxId) -> R<FxId> {
        let span = self.p.arena.span(d1);
        match kind {
            Kind::Type => {
                let name = self.p.interner.intern("up1");
                let n = self.p.arena.fresh_name();
                let param =
                    self.p.arena.identifier_variable(span, name, n, crate::ast::Domain::Value);
                let pure = self.pure(span);
                Ok(self.p.arena.add(
                    span,
                    Fx::Subr { effect: pure, ids: vec![param], types: vec![d2], body: d1 },
                ))
            }
            Kind::DFunc(kinds) => {
                let ids: Vec<FxId> = kinds
                    .iter()
                    .map(|_| {
                        let name = self.p.interner.intern("poly1");
                        let n = self.p.arena.fresh_name();
                        self.p.arena.identifier_variable(
                            span,
                            name,
                            n,
                            crate::ast::Domain::Description,
                        )
                    })
                    .collect();
                let applied1 =
                    self.p.arena.add(span, Fx::DApp { rator: d1, rands: ids.clone() });
                let applied2 =
                    self.p.arena.add(span, Fx::DApp { rator: d2, rands: ids.clone() });
                let inner = self.make_ups(applied1, &Kind::Type, applied2)?;
                Ok(self.p.arena.add(
                    span,
                    Fx::Poly { ids, kinds: kinds.clone(), body: inner },
                ))
            }
            Kind::Effect => Err(FxError::fatal(span, "unknown description in make-ups")),
        }
    }

    pub(crate) fn type_of_with(&mut self, id: FxId) -> R<(FxId, FxId)> {
        let span = self.p.arena.span(id);
        let Fx::With { module, body, .. } = self.p.arena.get(id).clone() else { unreachable!() };
        let mark = self.constraint_mark();
        let (mod_type, mod_effect) = self.type_effect_of_exp(module)?;
        let new_constraints = self.diff_constraints(mark);
        self.require(
            matches!(self.p.arena.get(mod_type), Fx::ModuleOf { .. }),
            span,
            "with requires a module",
        )?;
        let mod_type = if self.dont_alpha_rename_and_eval {
            mod_type
        } else {
            self.rename_moduleof(module, mod_type)?
        };
        let pure = self.pure(span);
        let ok = if self.algebraic {
            self.add_constraint(pure, mod_effect)?
        } else {
            self.unify(mod_effect, pure)?
        };
        self.require(ok, span, "non pure module in WITH")?;

        let (abs_ids, abs_kinds, desc_ids, desc_descs, val_ids, val_types) =
            self.moduleof_parts(mod_type)?;

        // Now that the module's identifiers are known, the body can be
        // alpha-renamed against them and parsed.
        let body = self.parse_unparsed_body(body, &abs_ids, &desc_ids, &val_ids)?;
        self.p.arena.set_body(id, body);

        for (i, k) in abs_ids.iter().zip(&abs_kinds) {
            self.tk_set(*i, TkEntry::Kind(k.clone()));
        }
        for (i, d) in desc_ids.iter().zip(&desc_descs) {
            let k = self.kind_of_dexp(*d)?;
            self.tk_set(*i, TkEntry::Kind(k));
            let norm = self.evaluate(*d)?;
            self.store_set(*i, norm);
        }
        let body_is_variable = self.p.arena.is_variable(body);
        for (i, t) in val_ids.iter().zip(&val_types) {
            let entry = if body_is_variable {
                *t
            } else {
                // Generalise as if the module were a thunk's body: a lambda is
                // non-expansive, so the value restriction does not block it.
                let wrapper = self.p.arena.add(
                    span,
                    Fx::Lambda {
                        ids: Vec::new(),
                        types: Vec::new(),
                        user_types: Vec::new(),
                        body: module,
                    },
                );
                let pure = self.pure(span);
                self.generalize_over(&new_constraints, wrapper, pure, *t)?
            };
            self.tk_set(*i, TkEntry::Type(entry));
        }
        for i in &abs_ids {
            let user = self.p.arena.var(*i).expect("a variable").user_name;
            let sel = self.p.arena.add(span, Fx::Select { module, id: user });
            if let Some(v) = self.p.arena.var(*i).cloned() {
                self.select_env.set(&v, sel);
            }
        }

        let (body_type, body_effect) = self.type_effect_of_exp(body)?;
        let exported = self.export_from_with(module, mod_type, &[body_type])?;
        let effect = self.evaluate(body_effect)?;
        Ok((exported[0], effect))
    }

    /// Re-express a type in terms the caller can see: an identifier the module
    /// bound becomes `(with m id)`, and an abstraction becomes `(select m t)`.
    fn export_from_with(
        &mut self,
        module: FxId,
        mod_type: FxId,
        dexps: &[FxId],
    ) -> R<Vec<FxId>> {
        let span = self.p.arena.span(module);
        let (abs_ids, _, _, _, val_ids, _) = self.moduleof_parts(mod_type)?;
        for i in &val_ids {
            let user = self.p.arena.var(*i).expect("a variable").user_name;
            // The reconstructed reference must keep the module identifier's
            // own alpha name. `export-from-with` gets that by re-parsing the
            // user name in an environment bound to exactly these identifiers;
            // handing it a *fresh* name instead produces a variable that no
            // environment knows, which surfaces much later as an "unbound
            // value variable" from inside a type.
            let text = fixpt_read::Syntax::symbol(span, user);
            let w = self.p.arena.add(span, Fx::With { module, body: *i, text });
            self.store_set(*i, w);
        }
        let mut news = Vec::with_capacity(dexps.len());
        for d in dexps {
            news.push(self.evaluate(*d)?);
        }
        for i in &abs_ids {
            let user = self.p.arena.var(*i).expect("a variable").user_name;
            let sel = self.p.arena.add(span, Fx::Select { module, id: user });
            self.store_set(*i, sel);
        }
        let mut out = Vec::with_capacity(news.len());
        for n in &news {
            out.push(self.evaluate(*n)?);
        }
        for i in val_ids.iter().chain(&abs_ids) {
            self.store_remove(*i);
        }
        Ok(out)
    }

    pub(crate) fn type_of_extend(&mut self, id: FxId) -> R<(FxId, FxId)> {
        let span = self.p.arena.span(id);
        let Fx::Extend { module, body, text } = self.p.arena.get(id).clone() else {
            unreachable!()
        };
        let (mod_type, mod_effect) = self.type_effect_of_exp(module)?;
        self.require(
            matches!(self.p.arena.get(mod_type), Fx::ModuleOf { .. }),
            span,
            "extend requires a module",
        )?;
        let pure = self.pure(span);
        let ok = if self.algebraic {
            self.add_constraint(mod_effect, pure)?
        } else {
            self.unify(mod_effect, pure)?
        };
        self.require(ok, span, "extend module should be pure")?;

        // The extension is checked as an ordinary `with` over the same module.
        let as_with = self.p.arena.add(span, Fx::With { module, body, text });
        let (body_type, body_effect) = self.type_effect_of_exp(as_with)?;
        // `with` parses its body in place; copy the parsed form back onto the
        // `extend` node, as `set-extend-body!` does. Without this the code
        // generator meets an unparsed body and has nothing to emit.
        if let Fx::With { body: parsed, .. } = self.p.arena.get(as_with).clone() {
            self.p.arena.set_body(id, parsed);
        }
        self.require(
            matches!(self.p.arena.get(body_type), Fx::ModuleOf { .. }),
            span,
            "extend requires a module extension",
        )?;

        let (abs1, kinds1, desc1, descs1, val1, _types1) = self.moduleof_parts(mod_type)?;
        let (abs2, kinds2, desc2, descs2, val2, types2) = self.moduleof_parts(body_type)?;

        // Anything the extension did not redefine is inherited. Shadowing is
        // by *user* name, since the two signatures have distinct identities.
        let keep = |me: &Self, ids: &[FxId], shadow: &[FxId]| -> Vec<usize> {
            ids.iter()
                .enumerate()
                .filter(|(_, i)| {
                    let name = me.p.arena.var(**i).map(|v| v.user_name);
                    !shadow.iter().any(|s| me.p.arena.var(*s).map(|v| v.user_name) == name)
                })
                .map(|(n, _)| n)
                .collect()
        };
        let abs_keep = keep(self, &abs1, &abs2);
        let desc_keep = keep(self, &desc1, &desc2);
        let val_keep = keep(self, &val1, &val2);

        let mut out_abs = abs2.clone();
        let mut out_abs_kinds = kinds2.clone();
        for n in &abs_keep {
            out_abs.push(abs1[*n]);
            out_abs_kinds.push(kinds1[*n].clone());
        }
        let mut out_desc = desc2.clone();
        let mut out_descs = descs2.clone();
        for n in &desc_keep {
            out_desc.push(desc1[*n]);
            out_descs.push(descs1[*n]);
        }
        let mut out_val = val2.clone();
        let mut out_types = types2.clone();
        for n in &val_keep {
            out_val.push(val1[*n]);
            let t = self.type_of_exp(val1[*n])?;
            out_types.push(t);
        }

        let module_type = self.p.arena.add(
            span,
            Fx::ModuleOf {
                abs_ids: out_abs,
                abs_kinds: out_abs_kinds,
                desc_ids: out_desc,
                desc_descs: out_descs,
                val_ids: out_val,
                val_types: out_types,
            },
        );
        Ok((module_type, body_effect))
    }

    /// `(load "file")`: read, parse and check another source file.
    ///
    /// Only the in-memory cache is kept. The reference also writes a `.fxt`
    /// file beside the source; that is skipped deliberately, because a stale
    /// cache would let a source change go unnoticed and it litters the corpus
    /// directory with derived files.
    pub(crate) fn type_of_load(&mut self, id: FxId) -> R<(FxId, FxId)> {
        let span = self.p.arena.span(id);
        let Fx::Load { path, alpha, parsed } = self.p.arena.get(id).clone() else {
            unreachable!()
        };
        if let Some(node) = parsed {
            return self.type_effect_of_exp(node);
        }
        let full = self.load_base.join(&path);
        let text = std::fs::read_to_string(&full).map_err(|e| {
            FxError::user(span, format!("cannot load {}: {e}", full.display()))
        })?;
        let form = {
            let mut sources = SourceMap::new();
            let file = sources.add(path.clone(), text.as_str());
            let mut interner = std::mem::take(&mut self.p.interner);
            let result = Reader::new(&text, file, SyntaxProfile::FX91, &mut interner).read();
            self.p.interner = interner;
            result
                .map_err(|e| FxError::user(e.span, format!("{}: {}", path, e.message)))?
                .ok_or_else(|| FxError::user(span, format!("{path} is empty")))?
        };
        // The loaded file is parsed in the *initial* environment: it is a
        // separate compilation unit, not an inclusion into this scope.
        let _ = alpha;
        let init = self.p.init_alpha;
        let node = self.p.parse_exp(init, &form)?;
        self.p.arena.set_load_parsed(id, node);
        self.type_effect_of_exp(node)
    }

    fn moduleof_parts(&self, ty: FxId) -> R<ModuleOfParts> {
        match self.p.arena.get(ty) {
            Fx::ModuleOf { abs_ids, abs_kinds, desc_ids, desc_descs, val_ids, val_types } => Ok((
                abs_ids.clone(),
                abs_kinds.clone(),
                desc_ids.clone(),
                desc_descs.clone(),
                val_ids.clone(),
                val_types.clone(),
            )),
            _ => Err(FxError::fatal(self.p.arena.span(ty), "expected a moduleof")),
        }
    }

    /// Parse a `with`/`extend` body now that the module's bindings are known.
    fn parse_unparsed_body(
        &mut self,
        body: FxId,
        abs_ids: &[FxId],
        desc_ids: &[FxId],
        val_ids: &[FxId],
    ) -> R<FxId> {
        let Fx::Unparsed { alpha, syntax } = self.p.arena.get(body).clone() else {
            return Ok(body);
        };
        let mut bindings = Vec::new();
        for i in abs_ids.iter().chain(desc_ids).chain(val_ids) {
            let v = self.p.arena.var(*i).expect("a variable");
            bindings.push((v.user_name, v.name));
        }
        let env = self.p.arena.extend_alpha(alpha, bindings);
        self.p.parse_exp(env, &syntax)
    }
}
