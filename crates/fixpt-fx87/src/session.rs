//! Running FX-87 programs: check, erase, evaluate.
//!
//! `type-and-eval` in the reference is `desc-of-exp` followed by
//! `(fx-eval (erase-type node))`, and this is the same two steps onto this
//! project's engines. Nothing about FX-87 reaches the evaluator: by the time
//! the Scheme session sees anything, the types have been erased and what is
//! left is a Scheme program.
//!
//! The erased form goes across as *text* and is re-read, for the reason FX-91's
//! does: the FX-87 checker and the Scheme session intern symbols separately, so
//! passing syntax directly would mix two symbol spaces silently. Writing and
//! re-reading also makes the generated code inspectable, which is most of
//! debugging a code generator.

use crate::check::Checker;
use crate::erase::Purity;
use crate::erase::erase_with;
use crate::error::{FxError, R};
use crate::unparse::unparse;
use fixpt_read::Syntax;
use fixpt_runtime::write_value;
use fixpt_scheme::Session;

/// The FX-87 run-time environment, as Scheme.
pub const RUNTIME: &str = include_str!("runtime.scm");

/// Default evaluation budget for one form.
///
/// FX-87 is Turing-complete, and a corpus written to exercise the *type* system
/// has no reason to avoid a loop. A budget turns a non-terminating case into
/// one reported failure rather than a wedged test run — a lesson this project
/// has now learned in three places.
pub const DEFAULT_STEP_LIMIT: u64 = 20_000_000;

pub struct Fx87Session {
    pub checker: Checker,
    pub scheme: Session,
    /// Whatever the last form printed while it ran.
    pub printed: String,
    /// The names the initial environment bound. They live in the immutable
    /// region, so an application of one can be annotated as integrable.
    standard: std::collections::HashSet<fixpt_read::Sym>,
}

/// What checking and running one form produced.
pub struct Outcome {
    pub ty: String,
    pub effect: String,
    /// The erased Scheme, kept for inspection.
    pub code: String,
    pub value: Result<String, String>,
}

impl Fx87Session {
    pub fn new() -> R<Fx87Session> {
        Fx87Session::with_backend(fixpt_engine::Backend::Ast)
    }

    pub fn with_backend(backend: fixpt_engine::Backend) -> R<Fx87Session> {
        let checker = Checker::new()?;
        let mut scheme = Session::with_backend(backend);
        scheme.eval_str("<fx87-runtime>", RUNTIME).map_err(|e| {
            FxError::internal(
                fixpt_read::Span::new(fixpt_read::FileId(0), 0, 0),
                format!("fx87 runtime: {e}"),
            )
        })?;
        scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        let standard = checker.env.value_names().collect();
        Ok(Fx87Session { checker, scheme, printed: String::new(), standard })
    }

    /// Check a form, erase it, and run it.
    ///
    /// The checker is reset to the initial environment each time, matching the
    /// reference's own top level.
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

    /// Check and erase a form without running it.
    ///
    /// Separate from [`run`](Self::run) so that a caller can decide whether to
    /// run it *after* seeing the effect. The REPL's `,help` hole is the caller
    /// that needs this: showing what the arguments beside a hole evaluate to
    /// means evaluating them, which is only defensible when the effect system
    /// says the evaluation cannot be noticed.
    pub fn check(&mut self, form: &Syntax) -> R<Checked> {
        let env = self.checker.env.clone();
        let exp = self.checker.p.parse_exp(form, &Default::default())?;
        let desc = self.checker.check(exp, &env)?;
        let ty = unparse(&self.checker.p.arena, &self.checker.p.interner, desc.ty);
        let effect = unparse(&self.checker.p.arena, &self.checker.p.interner, desc.effect);
        // FX-87's own notion, not a new one: `purify` already collapses any
        // effect confined to a private (`@=`) region to `pure`, which is
        // exactly the question being asked — can anyone outside tell that this
        // ran?
        let safe = self.checker.is_pure(exp);

        // The checker's own per-node descriptions become the justification the
        // emitted metadata carries.
        let purity = PurityOf(&self.checker);
        let code = erase_with(
            &self.checker.p.arena,
            &self.checker.p.interner,
            exp,
            &self.standard,
            Some(&purity),
        );
        Ok(Checked { ty, effect, code, safe })
    }

    /// Run already-erased Scheme, capturing what it printed.
    pub fn run_code(&mut self, code: &str) -> Result<String, String> {
        // A program's own output is captured rather than let loose: the value
        // is what is being compared.
        let saved = self.scheme.rt.capture();
        let result = self.scheme.eval_str("<fx87>", code);
        self.printed = self.scheme.rt.restore(saved);
        match result {
            // `write`, not `display`: the archive's evaluating path prints a
            // result with Racket's `print`, so a character comes out `#\a` and
            // a string keeps its quotes. (FX-91's driver uses `~a` and so
            // needs `display` — the two references differ here.)
            Ok(v) => Ok(write_value(&self.scheme.rt.heap, v)),
            Err(e) => Err(e.to_string()),
        }
    }
}

/// A form that has been checked and erased, but not run.
pub struct Checked {
    pub ty: String,
    pub effect: String,
    pub code: String,
    /// Whether running this form early would be undetectable.
    pub safe: bool,
}

/// Adapts the checker's recorded descriptions to what erasure asks for.
struct PurityOf<'a>(&'a Checker);

impl Purity for PurityOf<'_> {
    fn is_pure(&self, exp: crate::ast::ExpId) -> bool {
        self.0.is_pure(exp)
    }
    fn effect_text(&self, exp: crate::ast::ExpId) -> Option<String> {
        self.0.effect_text(exp)
    }
}
