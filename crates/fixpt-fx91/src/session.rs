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
use fixpt_runtime::display_value;
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
        self.scheme.rt.file_base = base;
    }

    /// Check a form, lower it, and run it.
    ///
    /// The checker is reset first, matching the reference's REPL loop: each
    /// top-level form is checked in the initial environment.
    pub fn run(&mut self, form: &Syntax) -> R<Outcome> {
        self.checker.reset();
        let alpha = self.checker.p.init_alpha;
        let node = self.checker.p.parse_exp(alpha, form)?;
        let (ty, effect) = self.checker.type_effect_of_exp(node)?;
        let ty = self.checker.render_dexp(ty);
        let effect = self.checker.render_dexp(effect);

        let generated = self.checker.code_of_exp(node)?;
        let code = fixpt_read::write_syntax(&generated, &self.checker.p.interner);
        // A program's own output is captured rather than let loose: the value
        // is what is being compared, and the reference's driver discards
        // printed output the same way.
        let saved = self.scheme.rt.capture();
        let result = self.scheme.eval_str("<fx91>", &code);
        self.printed = self.scheme.rt.restore(saved);
        let value = match result {
            // `display`, not `write`: the reference prints a result with
            // Racket's `~a`, so a character shows as `c` rather than `#\c`.
            Ok(v) => Ok(display_value(&self.scheme.rt.heap, v)),
            Err(e) => Err(e.to_string()),
        };
        Ok(Outcome {
            ty,
            effect,
            code,
            value,
        })
    }
}

fn fx91_span() -> fixpt_read::Span {
    fixpt_read::Span::new(fixpt_read::FileId(0), 0, 0)
}
