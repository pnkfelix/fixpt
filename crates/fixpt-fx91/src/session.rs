//! Running FX-91 programs: check, lower, evaluate.
//!
//! The checked expression is lowered to Scheme *text* and re-read by the
//! Scheme session. That round trip through text is deliberate: the FX-91
//! checker and the Scheme session intern symbols separately, so handing syntax
//! across directly would silently mix two symbol spaces. Writing and re-reading
//! also makes the generated code inspectable, which is most of debugging a code
//! generator.
//!
//! FX-91 folds symbol case at read time, so its symbols are already lower-case
//! and survive being re-read by the case-sensitive Scheme profile unchanged.

use crate::check::Checker;
use crate::error::{FxError, R};
use fixpt_read::Syntax;
use fixpt_scheme::Session;

/// The FX-91 runtime environment, as Scheme.
pub const RUNTIME: &str = include_str!("runtime.scm");

pub struct Fx91Session {
    pub checker: Checker,
    pub scheme: Session,
    /// Whatever the last form printed while it ran.
    pub printed: String,
}

/// Default evaluation budget for one form.
///
/// FX-91 is Turing-complete and its test suite contains genuinely
/// non-terminating values — `(define f (lambda () (f)))` is the third form in
/// it. Those are never *called* there, but a code-generator bug that turns a
/// value into a call would otherwise hang the suite instead of failing one
/// case. A budget turns that into a diagnosis.
pub const DEFAULT_STEP_LIMIT: u64 = 20_000_000;

/// What checking and running one form produced.
pub struct Outcome {
    /// The unparsed type, as the goldens print it.
    pub ty: String,
    /// The unparsed effect.
    pub effect: String,
    /// The generated Scheme, kept for inspection.
    pub code: String,
    /// The printed value, or the error that prevented one.
    pub value: Result<String, String>,
}

/// A form that has been checked and lowered, but not run.
pub struct Checked {
    pub ty: String,
    pub effect: String,
    pub code: String,
    /// Whether running this form early would be undetectable — see
    /// [`Fx91Session::speculation_safe`].
    pub safe: bool,
}

impl Fx91Session {
    pub fn new() -> R<Fx91Session> {
        Fx91Session::with_backend(fixpt_engine::Backend::Ast)
    }

    /// An FX-91 session on a chosen Scheme engine.
    ///
    /// FX-91 is a front end onto the Core IR, so it inherits whichever engine
    /// the Scheme session runs — which is what lets the conformance suite be
    /// replayed against the compiler without a second code generator.
    pub fn with_backend(backend: fixpt_engine::Backend) -> R<Fx91Session> {
        let checker = Checker::new()?;
        let mut scheme = Session::with_backend(backend);
        scheme
            .eval_str("<fx91-runtime>", RUNTIME)
            .map_err(|e| FxError::fatal(fx91_span(), format!("fx91 runtime: {e}")))?;
        scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        Ok(Fx91Session {
            checker,
            scheme,
            printed: String::new(),
        })
    }

    /// Where `(load "…")` and `open-input-stream` resolve from. Both need it:
    /// `load` is a *checking*-time inclusion and streams are a run-time one.
    pub fn set_load_base(&mut self, base: impl Into<std::path::PathBuf>) {
        let base = base.into();
        self.checker.load_base = base.clone();
        self.scheme.set_file_base(base);
    }

    /// Check a form, lower it, and run it.
    ///
    /// The checker is reset first, matching the reference's REPL loop: each
    /// top-level form is checked in the initial environment.
    pub fn run(&mut self, form: &Syntax) -> R<Outcome> {
        let checked = self.check(form)?;
        let value = self.run_code(&checked.code);
        Ok(Outcome {
            ty: checked.ty,
            effect: checked.effect,
            code: checked.code,
            value,
        })
    }

    /// Check and lower a form without running it.
    ///
    /// Separate from [`run`](Self::run) because the effect is known here and
    /// the decision to run can depend on it. The REPL's `,help` hole uses
    /// that: to show what a sibling argument evaluates to it must evaluate it,
    /// and evaluating something the user did not ask to evaluate is only
    /// defensible when the effect system says it cannot be noticed.
    pub fn check(&mut self, form: &Syntax) -> R<Checked> {
        self.checker.reset();
        let alpha = self.checker.p.init_alpha;
        let node = self.checker.p.parse_exp(alpha, form)?;
        let (ty, effect) = self.checker.type_effect_of_exp(node)?;
        let safe = self.speculation_safe(effect);
        let ty = self.checker.render_dexp(ty);
        let effect = self.checker.render_dexp(effect);
        let generated = self.checker.code_of_exp(node)?;
        let code = fixpt_read::write_syntax(&generated, &self.checker.p.interner);
        Ok(Checked { ty, effect, code, safe })
    }

    /// May this form be evaluated when the user only asked *about* it?
    ///
    /// The effect system answers. `read` and `init` leave nothing behind that
    /// a later run could notice — a read changes no store, and an allocation
    /// in a fresh region produces garbage and nothing else. `write` does, so
    /// an expression that may write is described rather than run. Anything
    /// whose effect is not one of those constants, including an effect
    /// variable that inference left open, is treated as unsafe: the point of
    /// asking is to be sure, and an unknown effect is not a guarantee.
    ///
    /// `read`, `write` and `init` are the abstract effects the standard module
    /// declares (`fx-module.fx:7`), so this is a check on the effect term's
    /// structure and not on how it happens to print.
    fn speculation_safe(&self, effect: crate::ast::FxId) -> bool {
        let p = &self.checker.p;
        p.arena.effect_list(effect).into_iter().all(|c| {
            p.arena
                .var(c)
                .map(|v| matches!(p.interner.name(v.user_name), "read" | "init"))
                .unwrap_or(false)
        })
    }

    /// Run already-lowered Scheme, capturing what it printed.
    pub fn run_code(&mut self, code: &str) -> Result<String, String> {
        // A program's own output is captured rather than let loose: the value
        // is what is being compared, and the reference's driver discards
        // printed output the same way.
        let (printed, result) = self.scheme.scope(|s| {
            let (printed, result) = s.eval_capturing("<fx91>", code);
            (printed, result.map(|v| s.display(v)))
        });
        self.printed = printed;
        match result {
            // `display`, not `write`: the reference prints a result with
            // Racket's `~a`, so a character shows as `c` rather than `#\c`.
            Ok(v) => Ok(v),
            Err(e) => Err(e.to_string()),
        }
    }
}

fn fx91_span() -> fixpt_read::Span {
    fixpt_read::Span::new(fixpt_read::FileId(0), 0, 0)
}
