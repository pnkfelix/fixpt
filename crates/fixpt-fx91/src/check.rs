//! The checker's state, and the bootstrap that builds the built-in `fx` module.
//!
//! `top.scm`'s `create-initial-envs` is a small chicken-and-egg problem: the
//! initial environments are produced by *type-checking* `(with fx (module))`,
//! which needs those environments to exist. The reference resolves it with a
//! flag, `*dont-alpha-rename-and-eval*`, that makes `with` skip the renaming
//! and generalisation it would normally do. The same flag is here, and
//! [`Checker::bootstrap`] performs the equivalent bindings directly — which is
//! what `with` reduces to once that flag is set.

use crate::ast::{Arena, Constraint, Fx, FxId, Kind};
use crate::env::{TkEntry, VarEnv};
use crate::error::{FxError, R};
use crate::parse::Parser;
use fixpt_read::{Reader, SourceMap, Span, SyntaxProfile};

/// The built-in `fx` module's signature, extracted from `standard.scm` rather
/// than transcribed. See `reference/fx91-stdmodule.rkt`.
pub const FX_MODULE: &str = include_str!("fx-module.fx");

pub struct Checker {
    pub p: Parser,

    /// Description variables to kinds, value variables to types.
    pub tk_env: VarEnv<TkEntry>,
    /// Description variables to their normal forms; value variables to the
    /// closed expressions `select` needs when a module-based type escapes the
    /// scope of one of its value variables.
    pub store: VarEnv<FxId>,
    /// Abstraction identifiers to the `select` that reaches them.
    pub select_env: VarEnv<FxId>,
    /// Effect constraints awaiting the ACUI solver.
    pub constraints: Vec<Constraint>,
    /// Pairs bound variables of the two descriptions being unified, so that
    /// alpha-equivalent binders compare equal.
    pub unify_env: VarEnv<FxId>,

    init_tk_env: VarEnv<TkEntry>,
    init_store: VarEnv<FxId>,
    init_select_env: VarEnv<FxId>,
    init_alpha_counter: u32,

    /// `bool`, for checking `if` tests.
    pub bool_type: FxId,
    /// The `fx` variable itself.
    pub fx_var: FxId,

    // ---- the reference's own switches, with its defaults ----
    /// `*algebraic-reconstruction*`: solve effects as ACUI constraints rather
    /// than by direct unification.
    pub algebraic: bool,
    /// `*cache-type/effect*`
    pub cache: bool,
    /// `*dont-alpha-rename-and-eval*`, used only by the bootstrap.
    pub dont_alpha_rename_and_eval: bool,
    /// `*forget-about-inferability*`
    pub forget_inferability: bool,
    /// Directory `(load "…")` resolves against.
    pub load_base: std::path::PathBuf,
}

impl Checker {
    /// Build a checker with the `fx` module installed.
    pub fn new() -> R<Checker> {
        let p = Parser::new();
        let mut c = Checker {
            p,
            tk_env: VarEnv::new(),
            store: VarEnv::new(),
            select_env: VarEnv::new(),
            constraints: Vec::new(),
            unify_env: VarEnv::new(),
            init_tk_env: VarEnv::new(),
            init_store: VarEnv::new(),
            init_select_env: VarEnv::new(),
            init_alpha_counter: 0,
            bool_type: FxId(0),
            fx_var: FxId(0),
            algebraic: true,
            cache: true,
            dont_alpha_rename_and_eval: false,
            forget_inferability: true,
            load_base: std::path::PathBuf::from("."),
        };
        c.bootstrap()?;
        Ok(c)
    }

    fn bootstrap(&mut self) -> R<()> {
        self.p.initializing = true;

        // `fx` itself, and the signature, are parsed in *empty* environments,
        // so the module's own names get fresh identities that the initial
        // alpha environment then publishes.
        let empty = self.p.arena.empty_alpha();
        let fx_sym = self.p.syms.fx;
        let span = Span::new(fixpt_read::FileId(0), 0, 0);
        let fx_name = self.p.arena.alpha_lookup(empty, fx_sym);
        self.fx_var = self.p.arena.identifier_variable(
            span,
            fx_sym,
            fx_name,
            crate::ast::Domain::Value,
        );

        let signature = {
            let mut sources = SourceMap::new();
            let file = sources.add("fx-module.fx", FX_MODULE);
            let mut interner = std::mem::take(&mut self.p.interner);
            let forms = Reader::new(FX_MODULE, file, SyntaxProfile::FX91, &mut interner)
                .read_all()
                .map_err(|e| FxError::fatal(e.span, format!("fx module: {}", e.message)));
            self.p.interner = interner;
            let forms = forms?;
            if forms.len() != 1 {
                return Err(FxError::fatal(span, "fx-module.fx must hold exactly one form"));
            }
            forms.into_iter().next().expect("length checked")
        };
        let empty2 = self.p.arena.empty_alpha();
        let fx_module = self.p.parse_dexp(empty2, &signature)?;

        // Publish `fx` and every identifier the signature binds.
        let mut bindings = vec![(fx_sym, fx_name)];
        let (abs_ids, desc_ids, val_ids) = match self.p.arena.get(fx_module) {
            Fx::ModuleOf { abs_ids, desc_ids, val_ids, .. } => {
                (abs_ids.clone(), desc_ids.clone(), val_ids.clone())
            }
            _ => return Err(FxError::fatal(span, "the fx signature must be a moduleof")),
        };
        for id in abs_ids.iter().chain(&desc_ids).chain(&val_ids) {
            let v = self.p.arena.var(*id).expect("moduleof binds variables");
            bindings.push((v.user_name, v.name));
        }
        self.p.init_alpha = self.p.arena.extend_alpha(empty, bindings);

        // `fx : <signature>`, and each abstraction stands for itself.
        {
            let v = self.p.arena.var(self.fx_var).expect("a variable").clone();
            self.tk_env.set(&v, TkEntry::Type(fx_module));
        }
        for id in &abs_ids {
            let v = self.p.arena.var(*id).expect("a variable").clone();
            self.store.set(&v, *id);
        }

        // What `(with fx (module))` amounts to once the bootstrap flag is set:
        // publish the abstractions' kinds, the descriptions' kinds and normal
        // forms, and the values' types. Generalisation is a no-op here because
        // a written-out signature contains no unification variables.
        self.dont_alpha_rename_and_eval = true;
        let (abs_kinds, desc_descs, val_types) = match self.p.arena.get(fx_module) {
            Fx::ModuleOf { abs_kinds, desc_descs, val_types, .. } => {
                (abs_kinds.clone(), desc_descs.clone(), val_types.clone())
            }
            _ => unreachable!("checked above"),
        };
        for (id, kind) in abs_ids.iter().zip(&abs_kinds) {
            let v = self.p.arena.var(*id).expect("a variable").clone();
            self.tk_env.set(&v, TkEntry::Kind(kind.clone()));
        }
        for (id, desc) in desc_ids.iter().zip(&desc_descs) {
            let kind = self.kind_of_dexp(*desc)?;
            let v = self.p.arena.var(*id).expect("a variable").clone();
            self.tk_env.set(&v, TkEntry::Kind(kind));
            let norm = self.evaluate(*desc)?;
            self.store.set(&v, norm);
        }
        for (id, ty) in val_ids.iter().zip(&val_types) {
            let v = self.p.arena.var(*id).expect("a variable").clone();
            self.tk_env.set(&v, TkEntry::Type(*ty));
            self.p.arena.exp_info_mut(*id).ty = Some(*ty);
        }
        for id in &abs_ids {
            let v = self.p.arena.var(*id).expect("a variable").clone();
            let sel =
                self.p.arena.add(span, Fx::Select { module: self.fx_var, id: v.user_name });
            self.select_env.set(&v, sel);
        }
        self.dont_alpha_rename_and_eval = false;

        let init_alpha = self.p.init_alpha;
        let bool_sym = self.p.interner.intern("bool");
        self.bool_type = {
            let s = fixpt_read::Syntax::symbol(span, bool_sym);
            self.p.parse_dexp(init_alpha, &s)?
        };

        self.init_tk_env = self.tk_env.clone();
        self.init_store = self.store.clone();
        self.init_select_env = self.select_env.clone();
        self.init_alpha_counter = self.p.arena.alpha_counter;
        self.p.initializing = false;
        Ok(())
    }

    /// Return to the state just after the bootstrap, as the REPL loop does
    /// between top-level forms.
    pub fn reset(&mut self) {
        self.tk_env.restore(&self.init_tk_env);
        self.store.restore(&self.init_store);
        self.select_env.restore(&self.init_select_env);
        self.constraints.clear();
        self.p.arena.alpha_counter = self.init_alpha_counter;
    }

    // ------------------------------------------------------------ shortcuts
    pub fn arena(&mut self) -> &mut Arena {
        &mut self.p.arena
    }

    /// A fresh unification variable, named after its own alpha number.
    ///
    /// The name is not cosmetic: `generalize_over` and `close` turn these into
    /// `poly` binders that keep the same user name, so it appears in printed
    /// types and therefore in the conformance goldens.
    pub fn fresh_unification(&mut self, span: Span, weak: bool, kind: crate::ast::Kind) -> FxId {
        let next = self.p.arena.alpha_counter;
        let sym = self.p.interner.intern(&next.to_string());
        self.p.arena.unification_variable(span, sym, weak, kind)
    }

    pub fn pure(&mut self, span: Span) -> FxId {
        self.p.arena.add(span, Fx::MaxEff(Vec::new()))
    }

    pub fn store_set(&mut self, var: FxId, value: FxId) {
        if let Some(v) = self.p.arena.var(var).cloned() {
            self.store.set(&v, value);
        }
    }
    pub fn store_get(&self, var: FxId) -> Option<FxId> {
        self.p.arena.var(var).and_then(|v| self.store.get(v)).copied()
    }
    pub fn store_remove(&mut self, var: FxId) {
        if let Some(v) = self.p.arena.var(var).cloned() {
            self.store.remove(&v);
        }
    }
    pub fn tk_set(&mut self, var: FxId, entry: TkEntry) {
        if let Some(v) = self.p.arena.var(var).cloned() {
            self.tk_env.set(&v, entry);
        }
    }
    pub fn tk_get(&self, var: FxId) -> Option<&TkEntry> {
        self.p.arena.var(var).and_then(|v| self.tk_env.get(v))
    }

    /// `check`: a user error unless the condition holds.
    pub fn require(&self, ok: bool, span: Span, message: &str) -> R<()> {
        if ok { Ok(()) } else { Err(FxError::user(span, message.to_string())) }
    }

    /// Render a description the way the conformance goldens do.
    pub fn render_dexp(&self, id: FxId) -> String {
        let u = crate::unparse::Unparser::new(&self.p.arena, &self.p.interner);
        u.render(&u.dexp(id))
    }
    pub fn render_exp(&self, id: FxId) -> String {
        let u = crate::unparse::Unparser::new(&self.p.arena, &self.p.interner);
        u.render(&u.exp(id))
    }
}

/// `kind=?`
pub fn kind_eq(a: &Kind, b: &Kind) -> bool {
    a == b
}
