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
use fixpt_scheme::Session;

/// The FX-26 run-time environment, as Scheme.
pub const RUNTIME: &str = include_str!("runtime.scm");

/// Default evaluation budget for one form, as FX-87's.
pub const DEFAULT_STEP_LIMIT: u64 = 20_000_000;

pub struct Fx26Session {
    pub checker: Checker,
    pub scheme: Session,
    pub globals: Globals,
    /// How checked forms run.
    pub strategy: Strategy,
    /// The initial environment as the FX-26 reader read it, for the checker
    /// written in FX-26: read once, as it takes the reader a while.
    standard26: Option<fixpt_scheme::Handle>,
    /// Under a strategy other than `Lower`, the definitions run so far, as
    /// text: each form is given to the pieces written in FX-26 as a whole
    /// program, so these go before it, and what it says can use them.
    defined26: String,
}

/// The budget for one speculative run: enough for a REPL-sized
/// computation, small enough that a loop costs a keystroke nothing noticeable.
pub const SPECULATION_STEP_LIMIT: u64 = 200_000;

/// What running a form early came to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Speculation {
    /// It ran, to this value.
    Value(String),
    /// It ran, and failed — `(car nil)` is well typed.
    Failed(String),
    /// It does not check.
    Rejected(String),
    /// It was not run: its effect has this atom, which the licence does not
    /// cover.
    NotLicensed(String),
    /// A definition: running one early would define it.
    NotAnExpression,
}

/// Check and lower one top-level form, keeping what it defines.
pub fn compile_form(checker: &mut Checker, globals: &mut Globals, form: &Syntax) -> R<(Top, String)> {
    let top = checker.top(form)?;
    let code = match &top {
        Top::DefineType { .. } | Top::DefineTypeFamily { .. } | Top::DefineEffect { .. } | Top::PrivateRegions { .. } => {
            String::new()
        }
        Top::Define { name, exp, recursive, .. } => {
            // A recursive definition refers to itself; a plain one to
            // whatever the name meant before it.
            let (global, body) = if *recursive {
                let g = globals.define(checker, *name);
                (g, lower(checker, globals, *exp))
            } else {
                let body = lower(checker, globals, *exp);
                (globals.define(checker, *name), body)
            };
            format!("(define {global} {body})")
        }
        Top::DefineRec { bindings } => {
            // Every name first: each lambda refers to the group's globals.
            let names: Vec<String> = bindings.iter().map(|(n, _, _)| globals.define(checker, *n)).collect();
            let defs: Vec<String> =
                bindings.iter().zip(&names).map(|((_, _, e), g)| format!("(define {g} {})", lower(checker, globals, *e))).collect();
            format!("(begin {})", defs.join(" "))
        }
        Top::Exp(k) => lower(checker, globals, k.exp),
    };
    Ok((top, code))
}

/// A whole program, checked and lowered but not run: the checker that
/// checked it, and the Scheme for each form, in order.
pub struct Compiled {
    pub checker: Checker,
    pub code: Vec<String>,
}

/// Check and lower the program `text`, whose definitions may come in any
/// order.
pub fn compile_program(text: &str) -> R<Compiled> {
    compile_program_as(text, "fx:")
}

/// The same, with every global the program defines named `<prefix><name>`,
/// so that it can share a Scheme session with another FX-26 program.
pub fn compile_program_as(text: &str, prefix: &str) -> R<Compiled> {
    let mut checker = Checker::new();
    let mut globals = Globals::with_prefix(prefix);
    let forms = checker.read_in(FileId(0), text)?;
    let done = checker.declare_ahead(&forms)?;
    let mut code = Vec::new();
    for (f, done) in forms.iter().zip(done) {
        if !done {
            let (_, c) = compile_form(&mut checker, &mut globals, f)?;
            if !c.is_empty() {
                code.push(c);
            }
        }
    }
    Ok(Compiled { checker, code })
}

/// The global prefix the eager reader is loaded under when it shares a
/// Scheme session with other code, so that a user's `(define need …)` —
/// `fx:need` — cannot replace the reader's `need`.
pub const READER_PREFIX: &str = "fx26-reader:";

/// Check the eager reader written in FX-26, check its licence, and only
/// then load it into `scheme`, under [`READER_PREFIX`]. It runs on every
/// keystroke, so nothing of it may run before the licence says it can.
pub fn load_eager_reader(scheme: &mut Session) -> Result<(), String> {
    let mut compiled = compile_program_as(&crate::front_end(), READER_PREFIX).map_err(|e| e.to_string())?;
    compiled.checker.reader_licence()?;
    compiled.load_into(scheme)
}

/// The global prefix the bootstrap program is loaded under.
pub const BOOTSTRAP_PREFIX: &str = "fx26-boot:";

/// The bootstrap program ([`crate::bootstrap_program`]: the front end and
/// its driver) lowered to Scheme and loaded into `scheme` under
/// [`BOOTSTRAP_PREFIX`], so that each piece can be run and timed lowered,
/// as the compiled ones are.
pub fn load_bootstrap_program(scheme: &mut Session) -> Result<(), String> {
    let compiled = compile_program_as(&crate::bootstrap_program(), BOOTSTRAP_PREFIX).map_err(|e| e.to_string())?;
    compiled.load_into(scheme)
}

impl Compiled {
    /// Load into `scheme`: the FX-26 runtime, then the program.
    pub fn load_into(&self, scheme: &mut Session) -> Result<(), String> {
        if !scheme.is_bound("%fx26-unit") {
            scheme.eval_str("<fx26-runtime>", RUNTIME).map_err(|e| e.to_string())?;
        }
        for c in &self.code {
            scheme.eval_str("<fx26>", c).map_err(|e| e.to_string())?;
        }
        Ok(())
    }
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

/// How a checked form is run.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub enum Strategy {
    /// Lowered to annotated Scheme and run on the session's engine.
    #[default]
    Lower,
    /// Run by the evaluator written in FX-26 (`evaluator.fx`).
    Evaluate,
    /// Compiled to a threaded word by the compiler written in FX-26
    /// (`compile.fx`) and run on the threaded machine.
    Threaded,
}

impl Fx26Session {
    pub fn with_backend(backend: fixpt_engine::Backend) -> R<Fx26Session> {
        let mut scheme = Session::with_backend(backend);
        scheme
            .eval_str("<fx26-runtime>", RUNTIME)
            .map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), format!("the FX-26 runtime failed to load: {e}")))?;
        scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        Ok(Fx26Session { checker: Checker::new(), scheme, globals: Globals::default(), strategy: Strategy::Lower, standard26: None, defined26: String::new() })
    }

    /// Check one top-level form and lower it, without running it.
    pub fn compile(&mut self, form: &Syntax) -> R<(Top, String)> {
        compile_form(&mut self.checker, &mut self.globals, form)
    }

    /// Run `form` early, if the licence allows: check it without keeping
    /// anything, and run it only if it is an expression whose effect is
    /// licensed for a driver that owns no region of the program's. That
    /// leaves allocation, and effects on regions inference made fresh for
    /// this form alone, which masking has already removed. The run has a
    /// budget of its own, since speculation must not hang the editor.
    pub fn speculate(&mut self, form: &Syntax) -> Speculation {
        let code = self.checker.try_top(form, |c, r| match r {
            Err(e) => Err(Speculation::Rejected(e.message)),
            Ok(Top::Exp(k)) => match crate::licence::unlicensed(&k.effect, &[]) {
                Some(a) => Err(Speculation::NotLicensed(c.show_atom(a))),
                None => Ok(lower(c, &self.globals, k.exp)),
            },
            Ok(_) => Err(Speculation::NotAnExpression),
        });
        let code = match code {
            Ok(code) => code,
            Err(s) => return s,
        };
        self.scheme.engine.set_step_limit(Some(SPECULATION_STEP_LIMIT));
        let result = self.scheme.scope(|s| {
            let (_, result) = s.eval_capturing("<fx26-speculative>", &code);
            result.map(|v| s.write(v))
        });
        self.scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        match result {
            Ok(v) => Speculation::Value(v),
            Err(e) => Speculation::Failed(e.to_string()),
        }
    }

    /// Run the forms of a whole program, its type abbreviations first. One
    /// outcome per form still to run; the abbreviations are done in the
    /// first pass and have none.
    pub fn run_forms(&mut self, forms: &[Syntax]) -> R<Vec<R<Outcome>>> {
        let done = self.checker.declare_ahead(forms)?;
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

    /// Check one top-level form, and run it as `strategy` says: lowered to
    /// Scheme, or through the evaluator or the compiler written in FX-26,
    /// which are given the form as text and read and parse it themselves.
    /// Checking comes first either way, so a form that does not check does
    /// not run.
    pub fn run(&mut self, form: &Syntax) -> R<Outcome> {
        let (top, code) = self.compile(form)?;
        if self.strategy != Strategy::Lower {
            let form_text = fixpt_read::write_syntax(form, &self.checker.interner);
            let text = format!("{}{form_text}\n", self.defined26);
            let out = match self.strategy {
                Strategy::Evaluate => self.eval_with_own_evaluator(&text)?,
                _ => self.compile_with_own_compiler(&text)?,
            };
            if !matches!(top, Top::Exp(_)) && !out.starts_with("!! ") {
                self.defined26.push_str(&form_text);
                self.defined26.push('\n');
            }
            let value = match out.strip_prefix("!! ") {
                Some(e) => Err(e.to_string()),
                None if matches!(top, Top::Exp(_)) => Ok(Some(out)),
                None => Ok(None),
            };
            return Ok(Outcome { top, code, printed: String::new(), value });
        }
        if code.is_empty() {
            return Ok(Outcome { top, code, printed: String::new(), value: Ok(None) });
        }
        let is_define = matches!(top, Top::Define { .. } | Top::DefineRec { .. });
        let (printed, value) = self.scheme.scope(|s| {
            let (printed, result) = s.eval_capturing("<fx26>", &code);
            let value = match result {
                Ok(_) if is_define => Ok(None),
                Ok(v) => Ok(Some(s.write(v))),
                Err(e) => Err(e.to_string()),
            };
            (printed, value)
        });
        Ok(Outcome { top, code, printed, value })
    }

    /// Read `text` with the reader written in FX-26, loading it into this
    /// session the first time, rather than with the Rust reader. Reading a
    /// whole file is long work for it, so it reads with no step limit: it
    /// is licensed code, and a text ends.
    pub fn read_with_own_reader(&mut self, text: &str) -> R<Vec<Syntax>> {
        if !self.scheme.is_bound(&format!("{READER_PREFIX}eager-start-fx26")) {
            load_eager_reader(&mut self.scheme).map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), e))?;
        }
        self.scheme.engine.set_step_limit(None);
        let forms = crate::syn::read_with_fx26_reader(&mut self.scheme, &mut self.checker.interner, FileId(0), text);
        self.scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        self.checker.expand_forms(forms?)
    }

    /// Parse `text` with the parser written in FX-26 (and its reader),
    /// loading them the first time: each form's tree, as text.
    pub fn parse_with_own_parser(&mut self, text: &str) -> R<Vec<String>> {
        if !self.scheme.is_bound(&format!("{READER_PREFIX}parse-program")) {
            load_eager_reader(&mut self.scheme).map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), e))?;
        }
        self.scheme.engine.set_step_limit(None);
        let r = crate::syn::parse_with_fx26_parser(&mut self.scheme, FileId(0), text);
        self.scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        r
    }

    /// Run `text` with the evaluator written in FX-26, reading and parsing
    /// it with the reader and the parser written in FX-26: its value as
    /// Scheme would write it, or `!! ` and its error.
    pub fn eval_with_own_evaluator(&mut self, text: &str) -> R<String> {
        if !self.scheme.is_bound(&format!("{READER_PREFIX}run-program")) {
            load_eager_reader(&mut self.scheme).map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), e))?;
        }
        self.scheme.engine.set_step_limit(None);
        let r = crate::syn::eval_with_fx26_evaluator(&mut self.scheme, FileId(0), text);
        self.scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        r
    }

    /// The initial environment as the FX-26 reader reads it, read once.
    fn standard26(&mut self) -> R<fixpt_scheme::Handle> {
        if let Some(h) = self.standard26 {
            return Ok(h);
        }
        // Outside any scope, so it lasts as the session does.
        let h = crate::syn::read_standard(&mut self.scheme)?;
        self.standard26 = Some(h);
        Ok(h)
    }

    /// Check `text` with the checker written in FX-26 (read and parsed in
    /// FX-26 too): see [`crate::syn::check_with_fx26_checker`].
    pub fn check_with_own_checker(&mut self, text: &str) -> R<crate::syn::Checked26> {
        if !self.scheme.is_bound(&format!("{READER_PREFIX}check-program")) {
            load_eager_reader(&mut self.scheme).map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), e))?;
        }
        // Generous, but a checker that loops is an error, not a hang.
        self.scheme.engine.set_step_limit(Some(2_000_000_000));
        let standard = self.standard26()?;
        let r = crate::syn::check_with_fx26_checker(&mut self.scheme, standard, FileId(0), text);
        self.scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        r
    }

    /// Compile `text` to a threaded word with the compiler written in FX-26
    /// (read and parsed in FX-26 too), and run it on the threaded machine:
    /// its value as Scheme would write it, or `!! ` and why not.
    pub fn compile_with_own_compiler(&mut self, text: &str) -> R<String> {
        if !self.scheme.is_bound(&format!("{READER_PREFIX}compile-program")) {
            load_eager_reader(&mut self.scheme).map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), e))?;
        }
        self.scheme.engine.set_step_limit(None);
        let standard = self.standard26()?;
        let r = crate::syn::compile_with_fx26_compiler(&mut self.scheme, standard, FileId(0), text);
        self.scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        r
    }

    /// [`run_program`](Self::run_program), reading with the reader written
    /// in FX-26: nothing of the Rust reader on the way.
    pub fn run_program_read_by_fx26(&mut self, text: &str) -> R<Result<String, String>> {
        let forms = self.read_with_own_reader(text)?;
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
