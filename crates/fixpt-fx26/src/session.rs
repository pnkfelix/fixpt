//! Running FX-26: check, lower, evaluate.
//!
//! One top-level form at a time, in one environment: a definition stays
//! defined, for the checker (`Checker::top`) and for the Scheme session
//! (`lower::Globals`) alike. The lowered code goes across as text and is
//! re-read, as FX-87's and FX-91's does, because the checker and the Scheme
//! session intern symbols separately — and so that `,code` can show it.
//!
//! Running goes through `Session::eval_capturing`, which is the whole of what
//! the three FX front ends' sessions had in common: evaluate, and keep what the
//! program printed apart from its value.

use crate::check::Checker;
use crate::error::{FxError, R};
use crate::lower::{Globals, lower};
use crate::top::Top;
use fixpt_read::{FileId, Span, Syntax};
use fixpt_runtime::write_value;
use fixpt_scheme::Session;

/// The FX-26 run-time environment, as Scheme.
pub const RUNTIME: &str = include_str!("runtime.scm");

/// Default evaluation budget for one form, as FX-87's.
pub const DEFAULT_STEP_LIMIT: u64 = 20_000_000;

pub struct Fx26Session {
    pub checker: Checker,
    pub scheme: Session,
    pub globals: Globals,
}

/// What one form did.
pub struct Outcome {
    /// What checking found, as the REPL prints it after the value.
    pub top: Top,
    /// The Scheme it was lowered to, empty for a `define-type`.
    pub code: String,
    /// What it printed while it ran.
    pub printed: String,
    /// Its value, written; `None` for a definition. An error when running
    /// failed — which checking does not rule out: `(car nil)` is well typed.
    pub value: Result<Option<String>, String>,
}

impl Fx26Session {
    pub fn with_backend(backend: fixpt_engine::Backend) -> R<Fx26Session> {
        let mut scheme = Session::with_backend(backend);
        scheme
            .eval_str("<fx26-runtime>", RUNTIME)
            .map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), format!("the FX-26 runtime failed to load: {e}")))?;
        scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        Ok(Fx26Session { checker: Checker::new(), scheme, globals: Globals::default() })
    }

    /// Check one top-level form and lower it, without running it.
    pub fn compile(&mut self, form: &Syntax) -> R<(Top, String)> {
        let top = self.checker.top(form)?;
        let code = match &top {
            Top::DefineType { .. } | Top::DefineEffect { .. } => String::new(),
            Top::Define { name, exp, recursive, .. } => {
                // A recursive definition refers to itself; a plain one to
                // whatever the name meant before it.
                let (global, body) = if *recursive {
                    let g = self.globals.define(&self.checker, *name);
                    (g, lower(&self.checker, &self.globals, *exp))
                } else {
                    let body = lower(&self.checker, &self.globals, *exp);
                    (self.globals.define(&self.checker, *name), body)
                };
                format!("(define {global} {body})")
            }
            Top::Exp(k) => lower(&self.checker, &self.globals, k.exp),
        };
        Ok((top, code))
    }

    /// Run the forms of a whole program, declaring its definitions first.
    /// One outcome per form still to run; the abbreviations are done in the
    /// first pass and have none.
    pub fn run_forms(&mut self, forms: &[Syntax]) -> R<Vec<R<Outcome>>> {
        let done = self.checker.declare_ahead(forms)?;
        for (f, _) in forms.iter().zip(&done) {
            if let Some([_, name, _, _]) = f.as_proper_list()
                && let Some(name) = name.as_symbol()
                && f.as_proper_list().and_then(|i| i[0].as_symbol()).is_some_and(|h| self.checker.interner.name(h) == "define")
            {
                self.globals.declare(&self.checker, name);
            }
        }
        let mut outs = Vec::new();
        for (f, done) in forms.iter().zip(done) {
            if !done {
                let out = self.run(f);
                let failed = out.is_err();
                outs.push(out);
                if failed {
                    break;
                }
            }
        }
        Ok(outs)
    }

    /// Check, lower and run one top-level form.
    pub fn run(&mut self, form: &Syntax) -> R<Outcome> {
        let (top, code) = self.compile(form)?;
        if code.is_empty() {
            return Ok(Outcome { top, code, printed: String::new(), value: Ok(None) });
        }
        let (printed, result) = self.scheme.eval_capturing("<fx26>", &code);
        let value = match result {
            Ok(_) if matches!(top, Top::Define { .. }) => Ok(None),
            Ok(v) => Ok(Some(write_value(&self.scheme.rt.heap, v))),
            Err(e) => Err(e.to_string()),
        };
        Ok(Outcome { top, code, printed, value })
    }

    /// Run a whole program, and the value of its last expression. Its
    /// definitions may refer to each other in any order: see
    /// `Checker::declare_ahead`.
    pub fn run_program(&mut self, text: &str) -> R<Result<String, String>> {
        let forms = self.checker.read_in(FileId(0), text)?;
        let mut last = Ok(String::new());
        for out in self.run_forms(&forms)? {
            let out = out?;
            match out.value {
                Ok(Some(v)) => last = Ok(v),
                Ok(None) => {}
                Err(e) => return Ok(Err(e)),
            }
        }
        Ok(last)
    }
}
