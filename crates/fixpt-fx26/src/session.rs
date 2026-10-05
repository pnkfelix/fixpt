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
use fixpt_read::{FileId, Span, Sym, Syntax};
use fixpt_scheme::Session;

/// The FX-26 run-time environment, as Scheme.
pub const RUNTIME: &str = include_str!("runtime.scm");

/// Default evaluation budget for one form, as FX-87's.
pub const DEFAULT_STEP_LIMIT: u64 = 20_000_000;

pub struct Fx26Session {
    pub checker: Checker,
    /// REPL entries of type definitions that name types not defined yet:
    /// held, unrun, until those are (`Fx26Session::consider`).
    pub pending: Vec<Pending>,
    pub scheme: Session,
    pub globals: Globals,
    /// How checked forms run.
    pub strategy: Strategy,
    /// Under `Strategy::Cellular`: whether the compiler written in FX-26
    /// makes each lambda's register code too, for a machine that runs it.
    pub register_code: bool,
    /// Whether the FX-26 front end's checker and compilers run as register
    /// code (`front_end_as_register_code`), made so when first loaded; the
    /// runtime's `front_end_run_word` must be a machine for register code.
    pub front_end_compiled: bool,
    /// Whether the program's convention is native (`--calling-convention`;
    /// set by [`set_native_convention`](Fx26Session::set_native_convention)).
    native_convention: bool,
    /// Whether naming a global reads it (`set_globals_effects`).
    globals_effects: bool,
    /// Whether re-runs wait (`set_defer_reruns`).
    defer_reruns: bool,
    /// Whether the form running is one the pieces written in FX-26 made
    /// already (`run_forms`).
    own_made: bool,
    /// Under `Strategy::Cellular` with the native convention: how an
    /// expression form is run, in place of the cellular machine.
    pub native_runner: Option<NativeRunner>,
    /// And how a definition's procedure, made by cellular code, is compiled
    /// to a native closure of the same code: for the definitions the native
    /// runner declines, and `define-rec`'s.
    pub native_compiler: Option<NativeCompiler>,
    /// Under `Strategy::Cellular`: whether the checker written in FX-26 has
    /// begun this session's program, so that each form is checked after the
    /// ones before (`check-more`), and compiled alone against the globals
    /// they made, which the compiler keeps.
    own_begun: bool,
    /// How a redefinition that would break definitions is decided: asked of
    /// the driver, or, with none, `Redefine::Break`.
    pub redefine: Option<fn(&Redefinition) -> Redefine>,
    /// What the next such redefinition does, said ahead of it (the REPL's
    /// `,redefine`), in place of asking.
    pub next_redefine: Option<Redefine>,
    /// Under `Strategy::Cellular`: whether each form's [`Outcome::code`] is
    /// the words the compiler written in FX-26 made for it, those not shown
    /// for an earlier form, rather than its lowering to Scheme.
    pub show_words: bool,
    /// The words shown so far, each as its disassembly.
    words_shown: std::collections::HashSet<String>,
    /// The initial environment as the FX-26 reader read it, for the checker
    /// written in FX-26: read once, as it takes the reader a while.
    standard26: Option<fixpt_scheme::Handle>,
    /// Under a strategy other than `Lower`, the definitions run so far, as
    /// text: each form is given to the pieces written in FX-26 as a whole
    /// program, so these go before it, and what it says can use them.
    defined26: String,
    /// How many steps a form may take when run, or no limit: see
    /// [`set_step_limit`](Fx26Session::set_step_limit).
    step_limit: Option<u64>,
    /// The same for a form run early, as it is typed ([`speculate`]
    /// (Fx26Session::speculate)): small, so that a loop costs a keystroke
    /// nothing noticeable. No limit lets a loop being typed hang the editor.
    pub speculation_limit: Option<u64>,
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

/// A REPL entry that defines types naming types not defined yet: held as
/// it was read, and run with the entries that complete it.
#[derive(Debug, Clone)]
pub struct Pending {
    pub forms: Vec<Syntax>,
    /// What it defines: types, and values (a datatype's constructors).
    pub defines: Vec<String>,
}

/// What entering a REPL entry does, given the entries pending.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Consider {
    /// It runs as any entry does.
    Run,
    /// It completes the pending entries: they and it run together.
    Completes(Vec<String>),
    /// It waits too: these types are not defined yet.
    Pends(Vec<String>),
}

/// Check and lower one top-level form, keeping what it defines, alone: not
/// under redefinition (`compile_form_defining` is).
pub fn compile_form(checker: &mut Checker, globals: &mut Globals, form: &Syntax) -> R<(Top, String)> {
    let top = checker.top(form)?;
    let code = lower_top(checker, globals, &top);
    Ok((top, code))
}

/// Check and lower one top-level form, under redefinition
/// (`Checker::top_defining`): the Scheme for everything it makes run, in
/// order, and what it broke.
pub fn compile_form_defining(checker: &mut Checker, globals: &mut Globals, form: &Syntax) -> R<(crate::top::Defining, Vec<String>)> {
    let done = checker.top_defining(form)?;
    let code = done.run.iter().map(|(top, _)| lower_top(checker, globals, top)).collect();
    Ok((done, code))
}

/// A checked top-level form, lowered: a definition that assigns keeps the
/// global its name has (`Globals::keep_next`).
pub fn lower_top(checker: &Checker, globals: &mut Globals, top: &Top) -> String {
    match top {
        Top::Define { name, assigns: true, .. } => globals.keep_next(*name),
        Top::DefineRec { bindings, assigns: true } => bindings.iter().for_each(|(n, _, _)| globals.keep_next(*n)),
        _ => {}
    }
    match top {
        Top::DefineType { .. } | Top::DefineTypeFamily { .. } | Top::DefineGenerative { .. } | Top::DefineEffect { .. } | Top::PrivateRegions { .. } => {
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
        Top::DefineRec { bindings, .. } => {
            // Every name first: each lambda refers to the group's globals.
            let names: Vec<String> = bindings.iter().map(|(n, _, _)| globals.define(checker, *n)).collect();
            let defs: Vec<String> =
                bindings.iter().zip(&names).map(|((_, _, e), g)| format!("(define {g} {})", lower(checker, globals, *e))).collect();
            format!("(begin {})", defs.join(" "))
        }
        Top::Exp(k) => lower(checker, globals, k.exp),
    }
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
            let (_, cs) = compile_form_defining(&mut checker, &mut globals, f)?;
            code.extend(cs.into_iter().filter(|c| !c.is_empty()));
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
    load_lowered(scheme, &crate::front_end())
}

/// The reader and parser alone (the front end's first files, which need
/// none after them), lowered and loaded: all a session whose checker and
/// compilers run as register code runs lowered. A tenth of the front end,
/// and of its loading, which is most of a session's start.
fn load_reader_alone(scheme: &mut Session) -> Result<(), String> {
    let text = crate::FRONT_END_FILES[..3].iter().map(|(_, t)| *t).collect::<Vec<_>>().join("\n");
    load_lowered(scheme, &text)
}

/// `text`, the front end or its first files, checked, licensed as the
/// reader, lowered and loaded.
fn load_lowered(scheme: &mut Session, text: &str) -> Result<(), String> {
    // An error in the front end says where in its files.
    let mut compiled = compile_program_as(text, READER_PREFIX)
        .map_err(|e| format!("the front end, {}: {}", crate::front_end_location(e.span.start as usize), e.message))?;
    compiled.checker.reader_licence()?;
    compiled.load_into(scheme)
}

/// Where the front end's register code is cached, if anywhere, and the key
/// its file must start with: a heap image in the user's cache directory, one
/// file for each executable, named by a hash of its path, and the key a hash
/// of the front end's text and of the executable's size and time, so that a
/// rebuilt compiler never reads what an older one made, but replaces it.
/// `FIXPT_NO_CACHE` turns it off.
fn front_end_cache(text: &str) -> Option<(std::path::PathBuf, u64)> {
    use std::hash::{Hash, Hasher};
    if std::env::var_os("FIXPT_NO_CACHE").is_some() {
        return None;
    }
    let exe = std::env::current_exe().ok()?;
    let meta = std::fs::metadata(&exe).ok()?;
    let mut name = std::collections::hash_map::DefaultHasher::new();
    exe.hash(&mut name);
    let mut key = std::collections::hash_map::DefaultHasher::new();
    (text, meta.len(), meta.modified().ok()).hash(&mut key);
    let home = std::env::var_os("HOME")?;
    let dir = match std::env::var_os("XDG_CACHE_HOME") {
        Some(d) => std::path::PathBuf::from(d),
        None if cfg!(target_os = "macos") => std::path::Path::new(&home).join("Library/Caches"),
        None => std::path::Path::new(&home).join(".cache"),
    }
    .join("fixpt");
    Some((dir.join(format!("front-end-{:016x}.img", name.finish())), key.finish()))
}

/// The front end's compiled word `w`, copied out of `heap` into a heap of
/// its own and written to `path` as an image after `key`: by a temporary
/// file renamed, so that a reader never sees half of one. Caches not used
/// for a month (their executables gone, most likely) are removed. Any
/// failure only means no cache.
fn save_front_end(heap: &fixpt_heap::Heap, w: fixpt_heap::Value, path: &std::path::Path, key: u64) {
    let mut alone = fixpt_heap::Heap::new();
    let copy = alone.copy_graph_from(heap, w);
    alone.push_root(copy);
    let mut bytes = key.to_le_bytes().to_vec();
    bytes.extend(fixpt_heap::image::dump(&alone));
    let Some(dir) = path.parent() else { return };
    if std::fs::create_dir_all(dir).is_err() {
        return;
    }
    let tmp = path.with_extension(format!("tmp{}", std::process::id()));
    if std::fs::write(&tmp, &bytes).is_ok() && std::fs::rename(&tmp, path).is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
    let month = std::time::Duration::from_secs(30 * 24 * 3600);
    for e in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let age = e.metadata().and_then(|m| m.accessed().or(m.modified())).ok().and_then(|t| t.elapsed().ok());
        if age.is_some_and(|a| a > month) && e.file_name().to_string_lossy().starts_with("front-end-") {
            let _ = std::fs::remove_file(e.path());
        }
    }
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
        // All in one evaluation: each recompiles the whole of the session's
        // program so far (`Prepared::update`), so one per form made loading
        // the front end quadratic in its forms.
        let all: String = self.code.iter().flat_map(|c| [c.as_str(), "\n"]).collect();
        scheme.eval_str("<fx26>", &all).map_err(|e| e.to_string())?;
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

/// What running an expression in the native convention did: ran, to a
/// value (written) or a trap; or was declined, and why (the compiler cannot
/// do something in it yet).
pub enum NativeRun {
    /// The value, as it is now: for the caller to write or keep at once,
    /// before anything allocates.
    Ran(Result<fixpt_heap::Value, String>),
    Declined(String),
}

/// How a driver runs an expression in the native convention: the closure
/// of a procedure of no arguments that computes it (made by the compiler
/// written in FX-26, with register code), in the runtime, with at most so
/// much fuel. The CLI's is `fixpt_native::direct`'s.
pub type NativeRunner = fn(&mut fixpt_runtime::Runtime, fixpt_heap::Value, u64) -> NativeRun;

/// A cellular closure compiled in the native convention: a native closure
/// of the same code over the same values, or why not.
pub type NativeCompiler = fn(&mut fixpt_heap::Heap, fixpt_heap::Value) -> Result<fixpt_heap::Value, String>;

/// Whether a redefinition goes ahead that would break definitions (those
/// that use the name and would no longer check). To keep a value as it was
/// instead, a program binds it: `(define d (let ((g g)) …))`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Redefine {
    /// Those that still check run again; the rest are broken, unusable
    /// until they are defined again. What a REPL does unless told otherwise.
    Break,
    /// The redefinition is refused, and nothing changes.
    Refuse,
}

/// A redefinition that would break definitions, for a driver to decide
/// (`Fx26Session::redefine`): the names redefined, each definition that
/// would no longer check and why, and those that would run again.
pub struct Redefinition {
    pub names: Vec<String>,
    pub breaking: Vec<(String, String)>,
    pub rerun: Vec<String>,
}

/// How a checked form is run.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub enum Strategy {
    /// Lowered to annotated Scheme and run on the session's engine.
    #[default]
    Lower,
    /// Run by the evaluator written in FX-26 (`evaluator.fx`).
    Evaluate,
    /// Compiled to a cellular word by the compiler written in FX-26
    /// (`compile.fx`) and run on the cellular machine.
    Cellular,
}

impl Fx26Session {
    pub fn with_backend(backend: fixpt_engine::Backend) -> R<Fx26Session> {
        let mut scheme = Session::with_backend(backend);
        scheme
            .eval_str("<fx26-runtime>", RUNTIME)
            .map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), format!("the FX-26 runtime failed to load: {e}")))?;
        scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        Ok(Fx26Session {
            checker: Checker::new(),
            scheme,
            globals: Globals::default(),
            strategy: Strategy::Lower,
            register_code: false,
            front_end_compiled: false,
            native_convention: false,
            native_runner: None,
            native_compiler: None,
            globals_effects: true,
            defer_reruns: false,
            own_made: false,
            own_begun: false,
            redefine: None,
            next_redefine: None,
            show_words: false,
            words_shown: Default::default(),
            standard26: None,
            defined26: String::new(),
            step_limit: Some(DEFAULT_STEP_LIMIT),
            speculation_limit: Some(SPECULATION_STEP_LIMIT),
            pending: Vec::new(),
        })
    }

    /// How many steps a form may take when run (`DEFAULT_STEP_LIMIT` to
    /// start with), or `None` for no limit.
    pub fn set_step_limit(&mut self, limit: Option<u64>) {
        self.step_limit = limit;
        self.scheme.engine.set_step_limit(limit);
    }

    pub fn step_limit(&self) -> Option<u64> {
        self.step_limit
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
        // Run as the session runs forms: the definitions before it are where
        // its strategy put them, not in the lowered program's globals.
        if self.strategy != Strategy::Lower {
            return self.speculate_own(&fixpt_read::write_syntax(form, &self.checker.interner));
        }
        self.scheme.engine.set_step_limit(self.speculation_limit);
        let result = self.scheme.scope(|s| {
            let (_, result) = s.eval_capturing("<fx26-speculative>", &code);
            result.map(|v| s.write(v))
        });
        self.scheme.engine.set_step_limit(self.step_limit);
        match result {
            Ok(v) => Speculation::Value(v),
            Err(e) => Speculation::Failed(e.to_string()),
        }
    }

    /// What entering `forms`, a REPL entry, would do with the entries
    /// pending: run alone if it checks alone, or if it defines no type; with
    /// them, if together they lack nothing; else wait, if it defines a type
    /// and only types are missing. Nothing is kept.
    pub fn consider(&mut self, forms: &[Syntax]) -> Consider {
        let c = &mut self.checker;
        let defines_type = forms.iter().any(|f| f.as_proper_list().and_then(|l| l.first()?.as_symbol()).is_some_and(|h| c.interner.name(h) == "define-type"));
        if !defines_type {
            return Consider::Run;
        }
        let alone = c.missing_types(forms);
        if alone.as_ref().is_some_and(|m| m.is_empty()) {
            return Consider::Run;
        }
        let names = |c: &Checker, ms: Vec<Sym>| ms.into_iter().map(|m| c.interner.name(m).to_string()).collect::<Vec<_>>();
        if !self.pending.is_empty() {
            let group: Vec<Syntax> = self.pending.iter().flat_map(|p| p.forms.iter().cloned()).chain(forms.iter().cloned()).collect();
            match self.checker.missing_types(&group) {
                Some(m) if m.is_empty() => return Consider::Completes(self.pending.iter().flat_map(|p| p.defines.iter().cloned()).collect()),
                Some(m) => return Consider::Pends(names(&self.checker, m)),
                None => {}
            }
        }
        match alone {
            Some(m) if !m.is_empty() => Consider::Pends(names(&self.checker, m)),
            _ => Consider::Run,
        }
    }

    /// `forms`, an entry `consider` said waits, held.
    pub fn hold(&mut self, forms: &[Syntax]) {
        let c = &self.checker;
        let mut defines = Vec::new();
        for f in forms {
            let l = f.as_proper_list().unwrap_or(&[]);
            match (l.first().and_then(|h| h.as_symbol()).map(|h| c.interner.name(h)), l.get(1).and_then(|n| n.as_symbol())) {
                (Some("define-type"), Some(n)) => defines.push(c.interner.name(n).to_string()),
                _ => defines.extend(c.defined_names(f).into_iter().map(|n| c.interner.name(n).to_string())),
            }
        }
        self.pending.push(Pending { forms: forms.to_vec(), defines });
    }

    /// The pending entries, and `forms` after them, run as a program's
    /// forms are; none pending after.
    pub fn complete(&mut self, forms: &[Syntax]) -> R<Vec<R<Outcome>>> {
        let group: Vec<Syntax> = std::mem::take(&mut self.pending).into_iter().flat_map(|p| p.forms).chain(forms.iter().cloned()).collect();
        self.run_forms(&group)
    }

    /// What the pending entries still lack, as `consider` would find it.
    pub fn awaiting(&mut self) -> Vec<String> {
        let group: Vec<Syntax> = self.pending.iter().flat_map(|p| p.forms.iter().cloned()).collect();
        if group.is_empty() {
            return Vec::new();
        }
        let m = self.checker.missing_types(&group).unwrap_or_default();
        m.into_iter().map(|m| self.checker.interner.name(m).to_string()).collect()
    }

    /// An expression (text), licensed, run early by the pieces written in
    /// FX-26 as `run_checked` runs one, on the speculation budget: natively
    /// if it can be, else as cellular code, or by the evaluator.
    fn speculate_own(&mut self, text: &str) -> Speculation {
        let saved = self.step_limit;
        self.step_limit = self.speculation_limit;
        let r = self.run_expression_own(text);
        self.step_limit = saved;
        self.scheme.engine.set_step_limit(saved);
        self.scheme.scope(|s| s.runtime_unrooted().heap.region_exit(0));
        match r {
            Ok(Ok(v)) => Speculation::Value(v),
            Ok(Err(e)) | Err(FxError { message: e, .. }) => Speculation::Failed(e),
        }
    }

    fn run_expression_own(&mut self, text: &str) -> R<Result<String, String>> {
        if let (Some(run), Strategy::Cellular) = (self.native_runner, self.strategy) {
            let fuel = self.step_limit.unwrap_or(u64::MAX >> 1);
            let written = |rt: &mut fixpt_runtime::Runtime, clo| match run(rt, clo, fuel) {
                NativeRun::Ran(v) => Ok(v.map(|v| fixpt_runtime::write_value(&rt.heap, v))),
                NativeRun::Declined(why) => Err(why),
            };
            if let Ok(Ok(value)) = self.with_thunk(text, written)? {
                return Ok(value);
            }
        }
        let out = match self.strategy {
            Strategy::Evaluate => self.eval_with_own_evaluator(&format!("{}{text}\n", self.defined26))?,
            _ => self.compile_form_showing(&format!("{text}\n"), false)?.0,
        };
        Ok(match out.strip_prefix("!! ") {
            Some(e) => Err(e.to_string()),
            None => Ok(out),
        })
    }

    /// Run the forms of a whole program, its type abbreviations first. One
    /// outcome per form still to run; the abbreviations are done in the
    /// first pass and have none. Redefinition is as at the REPL.
    pub fn run_forms(&mut self, forms: &[Syntax]) -> R<Vec<R<Outcome>>> {
        let done = self.checker.declare_ahead(forms)?;
        // The type definitions, declared ahead, are the pieces written in
        // FX-26's too, first: all in one text, so that its checker declares
        // them ahead as well, and they may name each other.
        if self.strategy != Strategy::Lower {
            let ahead: Vec<&Syntax> = forms.iter().zip(&done).filter(|(_, d)| **d).map(|(f, _)| f).collect();
            let text: String = ahead.iter().map(|f| format!("{}\n", fixpt_read::write_syntax(f, &self.checker.interner))).collect();
            if self.strategy == Strategy::Evaluate {
                self.defined26.push_str(&text);
            } else if let (Some(first), false) = (ahead.first(), text.is_empty())
                && let Some(e) = self.compile_form_showing(&text, false)?.0.strip_prefix("!! ")
            {
                return Err(FxError::at(first.span, e.to_string()));
            }
        }
        // What the reader made of a `define-generative` declared ahead (its
        // `up-` and `down-`, which have its span) the pieces written in
        // FX-26 made of it themselves, above, in its context. (A datatype's
        // constructors they are given as the reader made them.)
        let generative = |f: &Syntax| {
            f.as_proper_list().and_then(|l| l.first()?.as_symbol()).is_some_and(|h| self.checker.interner.name(h) == "define-generative")
        };
        let ahead: Vec<Span> = forms.iter().zip(&done).filter(|(f, d)| **d && generative(f)).map(|(f, _)| f.span).collect();
        let mut outs = Vec::new();
        for (f, done) in forms.iter().zip(done) {
            if !done {
                self.own_made = self.strategy != Strategy::Lower && ahead.contains(&f.span);
                let out = self.run(f);
                self.own_made = false;
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
        let out = self.run_defining(form);
        // No body of a region runs once a form is done: any region still
        // live was left by an error, or an escape no prompt ended.
        self.scheme.scope(|s| s.runtime_unrooted().heap.region_exit(0));
        out
    }

    /// `form`, run under redefinition (`Checker::top_defining`), as the
    /// language says for files and the REPL alike. Only whether a
    /// redefinition that would break definitions goes ahead is the driver's
    /// to decide (`Redefine`): asked, or said ahead, before anything changes.
    fn run_defining(&mut self, form: &Syntax) -> R<Outcome> {
        let names = self.checker.defined_names(form);
        let shown = |c: &Checker, ns: &[Sym]| ns.iter().map(|n| format!("`{}`", c.interner.name(*n))).collect::<Vec<_>>().join(", ");
        if names.iter().any(|n| self.checker.global_type(*n).is_some())
            && let Ok(trial) = self.checker.try_defining(form)
            && !trial.broken.is_empty()
        {
            let choice = self.next_redefine.take().unwrap_or_else(|| {
                let q = Redefinition {
                    names: names.iter().map(|n| self.checker.interner.name(*n).to_string()).collect(),
                    breaking: trial.broken.iter().map(|(ns, why)| (shown(&self.checker, ns), why.clone())).collect(),
                    rerun: trial.run[1..].iter().map(|(_, f)| shown(&self.checker, &self.checker.defined_names(f))).collect(),
                };
                self.redefine.map_or(Redefine::Break, |ask| ask(&q))
            });
            if choice == Redefine::Refuse {
                let list: Vec<String> = trial.broken.iter().map(|(ns, why)| format!("{}: {why}", shown(&self.checker, ns))).collect();
                return Err(FxError::at(form.span, format!("{} not redefined: it would break {}", shown(&self.checker, &names), list.join("; "))));
            }
        }
        let redefined = names.iter().any(|n| self.checker.global_type(*n).is_some());
        let done = self.checker.top_defining(form)?;
        let reran: Vec<Sym> = done.run[1..].iter().flat_map(|(_, f)| self.checker.defined_names(f)).collect();
        let mut notes = String::new();
        let mut out = None;
        for (i, (top, f)) in done.run.into_iter().enumerate() {
            let o = self.run_checked(top, &f, i > 0)?;
            if i == 0 {
                out = Some(o);
            } else if let Err(e) = &o.value {
                notes.push_str(&format!("; {} failed as it ran again: {e}\n", shown(&self.checker, &self.checker.defined_names(&f))));
            }
        }
        let mut out = out.expect("the form itself runs first");
        match &out.top {
            Top::Define { assigns: true, .. } | Top::DefineRec { assigns: true, .. } => {
                out.printed.push_str(&format!("; {} redefined: every use sees the new one\n", shown(&self.checker, &names)));
            }
            _ if redefined => {
                out.printed.push_str(&format!("; {} redefined", shown(&self.checker, &names)));
                if !reran.is_empty() {
                    out.printed.push_str(&format!("; run again, as they use it: {}", shown(&self.checker, &reran)));
                }
                out.printed.push('\n');
            }
            _ => {}
        }
        if !done.broken.is_empty() {
            let list: Vec<String> = done.broken.iter().map(|(ns, why)| format!("{} ({why})", shown(&self.checker, ns))).collect();
            out.printed.push_str(&format!("; broken until defined again: {}\n", list.join("; ")));
        }
        out.printed.push_str(&notes);
        Ok(out)
    }

    /// The next definition of `name` the compiler written in FX-26 makes a
    /// global for keeps the one it has: for a definition run in the native
    /// convention, which makes its global so (`native_define`).
    fn keep_global(&mut self, name: Sym) -> R<()> {
        if self.own_begun {
            let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
            let text = self.checker.interner.name(name).to_string();
            let mark = self.scheme.root_mark();
            let sym = self.scheme.make(|m| m.heap().intern(&text));
            let r = self.scheme.call_global(&format!("{READER_PREFIX}compile-keep-global!"), &[sym]).map_err(fail);
            self.scheme.release_to(mark);
            r?;
        }
        Ok(())
    }

    /// `top`, checked from `form`, run as `strategy` says; `again` when it
    /// is a definition run again for a redefinition, which the pieces
    /// written in FX-26 do themselves as they compile the redefinition,
    /// but which the native convention's definitions and the lowering do
    /// here.
    fn run_checked(&mut self, top: Top, form: &Syntax, again: bool) -> R<Outcome> {
        let code = lower_top(&self.checker, &mut self.globals, &top);
        if self.strategy != Strategy::Lower {
            if self.own_made {
                // What the native compiler declines runs as cellular code,
                // which is slower: said, with why.
                let mut printed = String::new();
                if let (Top::Define { name, .. }, Some(compile)) = (&top, self.native_compiler)
                    && let Err(why) = self.compile_global_natively(*name, compile)?
                {
                    let name = self.checker.interner.name(*name);
                    printed = format!("; `{name}` is not in the native convention yet, so it runs as cellular code: {why}\n");
                }
                return Ok(Outcome { top, code: String::new(), printed, value: Ok(None) });
            }
            if again && self.native_runner.is_none() {
                return Ok(Outcome { top, code: String::new(), printed: String::new(), value: Ok(None) });
            }
            let form_text = fixpt_read::write_syntax(form, &self.checker.interner);
            // An expression, in the native convention: as a procedure of no
            // arguments, compiled and called; what the compiler declines
            // runs as cellular code, saying why.
            let mut note = String::new();
            if let (Some(run), Top::Exp(_), Strategy::Cellular) = (self.native_runner, &top, self.strategy) {
                let fuel = self.step_limit.unwrap_or(u64::MAX >> 1);
                let written = |rt: &mut fixpt_runtime::Runtime, clo| {
                    // The runner compiles to machine code first, and counts
                    // that as compiling; the rest is the run.
                    let (start, compiled) = (std::time::Instant::now(), rt.compile_nanos);
                    let ran = run(rt, clo, fuel);
                    rt.run_nanos += (start.elapsed().as_nanos() as u64).saturating_sub(rt.compile_nanos - compiled);
                    match ran {
                        NativeRun::Ran(v) => Ok(v.map(|v| fixpt_runtime::write_value(&rt.heap, v))),
                        NativeRun::Declined(why) => Err(why),
                    }
                };
                match self.with_thunk(&form_text, written)? {
                    Ok(Ok(value)) => {
                        return Ok(Outcome { top, code: String::new(), printed: String::new(), value: value.map(Some) });
                    }
                    Ok(Err(why)) => note = format!("; not in the native convention yet, so run as cellular code: {why}\n"),
                    Err(why) => note = format!("; not compiled as a procedure: {why}\n"),
                }
            }
            // A definition, in the native convention: its global made, and
            // filled with its value, computed as an expression is.
            if let (Some(run), Top::Define { name, assigns, .. }, Strategy::Cellular) = (self.native_runner, &top, self.strategy)
                && let Some((ty, init)) = definition_init(form, &self.checker, *name)
            {
                if *assigns {
                    self.keep_global(*name)?;
                }
                let name = self.checker.interner.name(*name).to_string();
                // Checked against the type the definition says, if it says
                // one: a `lambda`'s parameters may be typed only by it.
                let w = |s: &Syntax| fixpt_read::write_syntax(s, &self.checker.interner);
                let init = match ty {
                    Some(t) => format!("(the {} {})", w(t), w(init)),
                    None => w(init),
                };
                match self.native_define(&name, &format!("{form_text}\n"), &init, run)? {
                    Ok(()) => return Ok(Outcome { top, code: String::new(), printed: String::new(), value: Ok(None) }),
                    Err(NativeRun::Ran(Err(e))) => return Ok(Outcome { top, code: String::new(), printed: String::new(), value: Err(e) }),
                    Err(NativeRun::Declined(why)) => note = format!("; not in the native convention yet, so `{name}` runs as cellular code: {why}\n"),
                    Err(NativeRun::Ran(Ok(_))) => unreachable!("a value is stored"),
                }
            }
            let (out, words) = match self.strategy {
                Strategy::Evaluate => (self.eval_with_own_evaluator(&format!("{}{form_text}\n", self.defined26))?, None),
                _ => self.compile_form_showing(&format!("{form_text}\n"), self.show_words)?,
            };
            // A form is compiled with every definition before it, so only
            // the words not shown before are this form's.
            let code = match words {
                Some(w) => w
                    .split_inclusive('\n')
                    .fold(Vec::<String>::new(), |mut blocks, line| {
                        match blocks.last_mut() {
                            Some(b) if !line.starts_with("word ") => b.push_str(line),
                            _ => blocks.push(line.to_string()),
                        }
                        blocks
                    })
                    .into_iter()
                    .filter(|b| self.words_shown.insert(b.clone()))
                    .collect::<String>()
                    .trim_matches('\n')
                    .to_string(),
                None => code,
            };
            // What the next form's run starts from (the evaluator keeps no
            // state between forms): every definition, and every expression
            // that writes, whose write a later form may see. It has no I/O,
            // so a write replayed does just what it did.
            let writes = |c: &crate::check::Checked| c.effect.0.iter().any(|a| matches!(a, crate::ast::Atom::Write(_)));
            let replay = match &top {
                Top::Exp(c) => writes(c),
                _ => true,
            };
            if replay && !out.starts_with("!! ") {
                self.defined26.push_str(&form_text);
                self.defined26.push('\n');
            }
            let value = match out.strip_prefix("!! ") {
                Some(e) => Err(e.to_string()),
                None if matches!(top, Top::Exp(_)) => Ok(Some(out)),
                None => Ok(None),
            };
            // In the native convention, a definition run so has its
            // procedures compiled after, as it made them: each global that
            // holds a cellular closure then holds a native one.
            let names = match &top {
                Top::Define { name, .. } => vec![*name],
                Top::DefineRec { bindings, .. } => bindings.iter().map(|b| b.0).collect(),
                _ => Vec::new(),
            };
            if let (Some(compile), Ok(_), false) = (self.native_compiler, &value, names.is_empty()) {
                let mut why = Vec::new();
                for n in names {
                    if let Err(w) = self.compile_global_natively(n, compile)? {
                        why.push(format!("`{}` runs as cellular code: {w}", self.checker.interner.name(n)));
                    }
                }
                note = if why.is_empty() { String::new() } else { format!("; not in the native convention yet, so {}\n", why.join("; ")) };
            }
            return Ok(Outcome { top, code, printed: note, value });
        }
        if code.is_empty() {
            return Ok(Outcome { top, code, printed: String::new(), value: Ok(None) });
        }
        let is_define = matches!(top, Top::Define { .. } | Top::DefineRec { .. });
        let (printed, value) = self.scheme.scope(|s| {
            // The lowered Scheme's own compiling, quick, is counted as run.
            let start = std::time::Instant::now();
            let (printed, result) = s.eval_capturing("<fx26>", &code);
            s.runtime_unrooted().run_nanos += start.elapsed().as_nanos() as u64;
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
        self.scheme.engine.set_step_limit(self.step_limit);
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
        self.scheme.engine.set_step_limit(self.step_limit);
        r
    }

    /// Run `text` with the evaluator written in FX-26, reading and parsing
    /// it with the reader and the parser written in FX-26: its value as
    /// Scheme would write it, or `!! ` and its error.
    pub fn eval_with_own_evaluator(&mut self, text: &str) -> R<String> {
        self.own_pieces()?;
        let standard = self.standard26()?;
        // A whole program: the checker begins again.
        self.own_begun = false;
        self.scheme.engine.set_step_limit(None);
        let r = crate::syn::eval_with_fx26_evaluator(&mut self.scheme, standard, FileId(0), text);
        self.scheme.engine.set_step_limit(self.step_limit);
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

    /// Make the program's convention native, or cellular: what every
    /// subroutine type that names none has, the standard environment's
    /// included, in both checkers. Before any form is checked.
    pub fn set_native_convention(&mut self, on: bool) {
        self.native_convention = on;
        self.checker = Checker::with_convention(if on { crate::ast::Conv::Native } else { crate::ast::Conv::Cellular });
        self.checker.globals_effects = self.globals_effects;
        self.checker.defer_reruns = self.defer_reruns;
    }

    /// Whether a redefinition that makes a new global leaves the
    /// definitions that use the name out of date, as they were, for
    /// [`rerun_outdated`](Self::rerun_outdated) to run again when asked,
    /// rather than running them again at once: in both checkers
    /// (`Checker::defer_reruns`). What the REPL does, so that a load does
    /// not run again what it is about to define again.
    pub fn set_defer_reruns(&mut self, on: bool) {
        self.defer_reruns = on;
        self.checker.defer_reruns = on;
    }

    /// The definitions out of date (`set_defer_reruns`), oldest first: the
    /// names each defines, and those it uses that were defined again since.
    pub fn outdated(&self) -> Vec<(Vec<String>, Vec<String>)> {
        let names = |ns: &[Sym]| ns.iter().map(|n| self.checker.interner.name(*n).to_string()).collect();
        self.checker.outdated().iter().map(|(ns, since, _)| (names(ns), names(since))).collect()
    }

    /// Each definition out of date run again, oldest first, as though
    /// written again, until none is left that has not been tried: one may
    /// leave others out of date in its turn. Each one's names, and what
    /// running it did; one that does not check stays out of date.
    pub fn rerun_outdated(&mut self) -> Vec<(Vec<String>, R<Outcome>)> {
        let mut tried: Vec<Vec<Sym>> = Vec::new();
        let mut outs = Vec::new();
        while let Some((ns, _, form)) = self.checker.outdated().into_iter().find(|(ns, _, _)| !tried.contains(ns)) {
            let out = self.run(&form);
            outs.push((ns.iter().map(|n| self.checker.interner.name(*n).to_string()).collect(), out));
            tried.push(ns);
        }
        outs
    }

    /// Whether naming a global reads it, `(read (globals g))`, in both
    /// checkers (`Checker::globals_effects`).
    pub fn set_globals_effects(&mut self, on: bool) {
        self.globals_effects = on;
        self.checker.globals_effects = on;
    }

    /// A checker with no program in it yet, set as this session's is.
    pub fn fresh_checker(&self) -> Checker {
        let mut c = Checker::with_convention(if self.native_convention { crate::ast::Conv::Native } else { crate::ast::Conv::Cellular });
        c.globals_effects = self.globals_effects;
        c.base_dir = self.checker.base_dir.clone();
        c
    }

    /// The front end's entry points the Rust side calls by name
    /// (`READER_PREFIX`), each rebound by [`Self::front_end_as_register_code`].
    pub const FRONT_ENTRIES: [&'static str; 24] = [
        "read-text", "check-program", "check-more", "checked-tops", "checked-extracts", "checked-effects", "check-conv-native!", "checked-withs!", "checked-reshapes!",
        "check-globals-effects!", "check-defer-reruns!", "parse-program", "loaded-files!", "run-checked", "compile-program", "compile-checked", "compile-registers!",
        "compile-global-cell", "compile-new-global", "compile-keep-global!", "compile-note-inline!", "native-assemble",
        "arm-ret", "arm-mov-imm64",
    ];

    /// The front end's checker and compilers run as register code, not as
    /// lowered Scheme on the engine (about 28 times as fast): the front
    /// end compiled by the Rust compiler, with register code, and run once
    /// to give its entry points; each `READER_PREFIX` global the Rust side
    /// calls then calls its entry point by `%run-front-end` (the runtime's
    /// `front_end_run_word`, which the caller installs: a machine that
    /// runs register code). The reader stays lowered, and loaded as ever.
    fn front_end_as_register_code(&mut self) -> R<()> {
        let fail = |m: String| FxError::at(Span::new(FileId(0), 0, 0), m);
        let fields: Vec<String> = Self::FRONT_ENTRIES.iter().enumerate().map(|(i, n)| format!("({} {n})", i + 1)).collect();
        let text = format!("{}\n(product {})\n", crate::front_end(), fields.join(" "));
        // Checked and compiled once for this executable and this front end,
        // then kept (`front_end_cache`); read back from there after.
        let cache = front_end_cache(&text);
        let cached = cache.as_ref().and_then(|(p, key)| {
            let b = std::fs::read(p).ok()?;
            (b.get(..8)? == key.to_le_bytes()).then(|| fixpt_heap::image::load(&b[8..]).ok())?
        });
        let mut checked = None;
        if cached.is_none() {
            let mut c = Checker::new();
            let forms = c.read_in(FileId(0), &text)?;
            let done = c.declare_ahead(&forms)?;
            let mut tops = Vec::new();
            for (f, done) in forms.iter().zip(done) {
                if !done {
                    tops.extend(c.top_all(f)?);
                }
            }
            checked = Some((c, tops));
        }
        let limit = self.step_limit();
        self.scheme.engine.set_step_limit(None);
        let pieces = self.scheme.scope(|sc| {
            let mut compiled = Err(String::new());
            let word = sc.make(|m| {
                if let Some(from) = &cached {
                    compiled = Ok(m.heap().copy_graph_from(from, from.roots_slice()[0]));
                } else if let Some((c, tops)) = &checked {
                    let mut comp = crate::cellular::Compiler::new(m.heap(), c, &text);
                    comp.registers = true;
                    compiled = comp.program(tops);
                    if let (Ok(w), Some((path, key))) = (&compiled, &cache) {
                        save_front_end(m.heap(), *w, path, *key);
                    }
                }
                compiled.clone().unwrap_or(fixpt_heap::Value::FALSE)
            });
            compiled.map_err(|e| format!("the front end as register code: {e}"))?;
            let none = sc.make(|_| fixpt_heap::Value::NULL);
            let pieces = sc.call_global("%run-front-end", &[word, none]).map_err(|e| e.to_string())?;
            // Each entry point in a global of its own, and the name the Rust
            // side calls made to call it.
            sc.make(|m| {
                let p = m.get(pieces);
                for (i, name) in Self::FRONT_ENTRIES.iter().enumerate() {
                    // Field `i + 1` of the product, its slot `i + 2`.
                    let piece = m.heap().bloblet_slot(p, 2 + i);
                    let sym = m.heap().intern(&format!("fx26-native:{name}"));
                    let slot = m.heap().symbol_global_slot(sym);
                    m.heap().set_global(slot, piece);
                }
                fixpt_heap::Value::NULL
            });
            Ok(())
        });
        self.scheme.engine.set_step_limit(limit);
        pieces.map_err(fail)?;
        for name in Self::FRONT_ENTRIES {
            let define = format!("(define (fx26-reader:{name} . args) (%run-front-end fx26-native:{name} args))");
            self.scheme.eval_str("<front end>", &define).map_err(|e| fail(e.to_string()))?;
        }
        Ok(())
    }

    /// The pieces written in FX-26 (reader, checker, compilers), loaded if
    /// they are not yet.
    pub fn load_own_pieces(&mut self) -> R<()> {
        self.own_pieces()
    }

    /// The pieces written in FX-26, loaded if they are not yet, and told the
    /// program's convention.
    fn own_pieces(&mut self) -> R<()> {
        let fail = |m: String| FxError::at(Span::new(FileId(0), 0, 0), m);
        // A `load-module`'s path is from where the Rust checker's is.
        crate::syn::set_load_base(self.checker.base_dir.clone());
        if self.front_end_compiled {
            if !self.scheme.is_bound(&format!("{READER_PREFIX}eager-start-fx26")) {
                load_reader_alone(&mut self.scheme).map_err(fail)?;
            }
            if !self.scheme.is_bound("fx26-native:check-program") {
                self.front_end_as_register_code()?;
            }
        } else if !self.scheme.is_bound(&format!("{READER_PREFIX}check-program")) {
            load_eager_reader(&mut self.scheme).map_err(fail)?;
        }
        // The handles below are this call's: released at its end (what
        // was loaded above stays, made before the mark).
        let mark = self.scheme.root_mark();
        let r = (|| {
            let on = self.scheme.make(|_| fixpt_heap::Value::boolean(self.native_convention));
            self.scheme.call_global(&format!("{READER_PREFIX}check-conv-native!"), &[on]).map_err(|e| fail(e.to_string()))?;
            let on = self.scheme.make(|_| fixpt_heap::Value::boolean(self.globals_effects));
            self.scheme.call_global(&format!("{READER_PREFIX}check-globals-effects!"), &[on]).map_err(|e| fail(e.to_string()))?;
            let on = self.scheme.make(|_| fixpt_heap::Value::boolean(self.defer_reruns));
            self.scheme.call_global(&format!("{READER_PREFIX}check-defer-reruns!"), &[on]).map_err(|e| fail(e.to_string()))?;
            Ok(())
        })();
        self.scheme.release_to(mark);
        r
    }

    /// The value of the global `name`, as the forms defined so far make it,
    /// compiled by the compiler written in FX-26 with register code: given
    /// to `f`, with the runtime (see [`crate::syn::with_last_value`]).
    pub fn with_global_value<T>(&mut self, name: &str, f: impl FnOnce(&mut fixpt_runtime::Runtime, fixpt_heap::Value) -> T) -> R<Result<T, String>> {
        self.with_last_value(&format!("{name}\n"), f)
    }

    /// The same for the value of expression `exp` (text) as a procedure of
    /// no arguments that computes it.
    pub fn with_thunk<T>(&mut self, exp: &str, f: impl FnOnce(&mut fixpt_runtime::Runtime, fixpt_heap::Value) -> T) -> R<Result<T, String>> {
        self.with_last_value(&format!("(lambda () {exp})\n"), f)
    }

    /// `form` (text), a definition of `name` whose value is `init` (text),
    /// in the native convention: checked, as the next form; `name`'s global
    /// made by the compiler written in FX-26; `init` run as a procedure of
    /// no arguments, by `run`; and its value put in the global. What `run`
    /// did instead, if anything else.
    fn native_define(&mut self, name: &str, form: &str, init: &str, run: NativeRunner) -> R<Result<(), NativeRun>> {
        self.own_pieces()?;
        let standard = self.next_standard()?;
        // What is loaded is loaded, above; the handles below are this
        // definition's, released at its end: kept, the global's cell would
        // keep each old definition alive, its code with it.
        let mark = self.scheme.root_mark();
        let r = self.native_define_in(standard, name, form, init, run);
        self.scheme.release_to(mark);
        r
    }

    fn native_define_in(
        &mut self,
        standard: Option<fixpt_scheme::Handle>,
        name: &str,
        form: &str,
        init: &str,
        run: NativeRunner,
    ) -> R<Result<(), NativeRun>> {
        if let Err(why) = crate::syn::check_only(&mut self.scheme, standard, FileId(0), form)? {
            return Ok(Err(NativeRun::Declined(format!("check: {why}"))));
        }
        self.own_begun = true;
        let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
        let sym = self.scheme.make(|m| m.heap().intern(name));
        let cell = self.scheme.call_global(&format!("{READER_PREFIX}compile-new-global"), &[sym]).map_err(fail)?;
        // The global, kept where a collection updates it while `init` runs.
        let mut at = 0;
        self.scheme.make(|m| {
            let c = m.get(cell);
            at = m.heap().push_root(c);
            c
        });
        let fuel = self.step_limit.unwrap_or(u64::MAX >> 1);
        let r = self.with_thunk(init, |rt, clo| match {
            let (start, compiled) = (std::time::Instant::now(), rt.compile_nanos);
            let ran = run(rt, clo, fuel);
            rt.run_nanos += (start.elapsed().as_nanos() as u64).saturating_sub(rt.compile_nanos - compiled);
            ran
        } {
            NativeRun::Ran(Ok(v)) => {
                let g = rt.heap.root_at(at);
                rt.heap.set_bloblet_slot(g, 2, v);
                Ok(())
            }
            other => Err(other),
        });
        self.scheme.runtime_unrooted().heap.pop_roots_to(at);
        if matches!(r, Ok(Ok(Ok(())))) {
            // A lambda, noted for inlining, as a definition compiled is.
            let sym = self.scheme.make(|m| m.heap().intern(name));
            self.scheme.call_global(&format!("{READER_PREFIX}compile-note-inline!"), &[sym]).map_err(fail)?;
        }
        Ok(match r? {
            Ok(done) => done,
            Err(why) => Err(NativeRun::Declined(why)),
        })
    }

    /// Global `name`'s value, if a cellular closure, compiled by `compile`
    /// to a native closure, which the global then holds; or why not.
    /// The globals whose code has a call of global `name` inlined, behind
    /// a guard that `name` still holds what it held when they were
    /// compiled (`,inliners`): what a redefinition of `name` sends back to
    /// calling it. Nothing need be compiled again; it is for knowing.
    pub fn inliners(&mut self, name: &str) -> R<Result<Vec<String>, String>> {
        if self.strategy != Strategy::Cellular {
            return Ok(Err("only compiled code inlines: `--fx26-run cellular`".into()));
        }
        self.own_pieces()?;
        let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
        let cell_of = |s: &mut Self, n: &str| -> R<Option<fixpt_scheme::Handle>> {
            let sym = s.scheme.make(|m| m.heap().intern(n));
            let cells = s.scheme.call_global(&format!("{READER_PREFIX}compile-global-cell"), &[sym]).map_err(fail)?;
            let mut found = false;
            let g = s.scheme.make(|m| {
                let cells = m.get(cells);
                found = cells.is_pair();
                if found { m.heap().car(cells) } else { fixpt_heap::Value::FALSE }
            });
            Ok(found.then_some(g))
        };
        let Some(target) = cell_of(self, name)? else { return Ok(Err(format!("`{name}` has no global"))) };
        let mut out = Vec::new();
        let names: Vec<String> = self.checker.value_names().into_iter().map(|n| self.checker.interner.name(n).to_string()).collect();
        // Its own calls of itself, guarded too, are not counted: redefined,
        // it is not called by what it was.
        for n in names.into_iter().filter(|n| n != name) {
            let Some(g) = cell_of(self, &n)? else { continue };
            let mut inlines = false;
            self.scheme.make(|m| {
                let (g, t) = (m.get(g), m.get(target));
                let heap = m.heap();
                inlines = fixpt_runtime::disasm::inlines_global(heap, heap.bloblet_slot(g, 2), t);
                fixpt_heap::Value::FALSE
            });
            if inlines {
                out.push(n);
            }
        }
        out.sort();
        Ok(Ok(out))
    }

    fn compile_global_natively(&mut self, name: Sym, compile: NativeCompiler) -> R<Result<(), String>> {
        self.released(|s| {
        let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
        let text = s.checker.interner.name(name).to_string();
        let sym = s.scheme.make(|m| m.heap().intern(&text));
        let cells = s.scheme.call_global(&format!("{READER_PREFIX}compile-global-cell"), &[sym]).map_err(fail)?;
        let (mut r, mut nanos) = (Ok(()), 0);
        s.scheme.make(|m| {
            let cells = m.get(cells);
            if !cells.is_pair() {
                r = Err(format!("`{text}` has no global"));
                return fixpt_heap::Value::FALSE;
            }
            let heap = m.heap();
            let g = heap.car(cells);
            let v = heap.bloblet_slot(g, 2);
            if v.is_bloblet() && heap.bloblet_kind(v) == fixpt_heap::layout::kind("cellular-closure") {
                let start = std::time::Instant::now();
                let compiled = compile(heap, v);
                nanos = start.elapsed().as_nanos() as u64;
                match compiled {
                    Ok(native) => heap.set_bloblet_slot(g, 2, native),
                    Err(why) => r = Err(why),
                }
            }
            fixpt_heap::Value::FALSE
        });
        s.scheme.runtime_unrooted().compile_nanos += nanos;
        Ok(r)
        })
    }

    /// Run `f`, then release the handles it made (and the roots it pushed):
    /// for work done for one form, whose handles would otherwise root what
    /// they hold for the rest of the session. Anything that must last (what
    /// a lazy load makes, `standard26`) is made before.
    fn released<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let mark = self.scheme.root_mark();
        let r = f(self);
        self.scheme.release_to(mark);
        r
    }

    /// `text` checked and compiled as the next form of this session's
    /// program, and run: its value, to `f`.
    fn with_last_value<T>(&mut self, text: &str, f: impl FnOnce(&mut fixpt_runtime::Runtime, fixpt_heap::Value) -> T) -> R<Result<T, String>> {
        self.own_pieces()?;
        self.scheme.engine.set_step_limit(None);
        let standard = self.next_standard()?;
        self.released(|s| {
        let on = s.scheme.make(|_| fixpt_heap::Value::TRUE);
        let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
        s.scheme.call_global(&format!("{READER_PREFIX}compile-registers!"), &[on]).map_err(fail)?;
        let r = crate::syn::with_last_value(&mut s.scheme, standard, FileId(0), text, f);
        s.own_begun |= !matches!(&r, Ok(Err(m)) if m.starts_with("check:"));
        let off = s.scheme.make(|_| fixpt_heap::Value::boolean(s.register_code));
        s.scheme.call_global(&format!("{READER_PREFIX}compile-registers!"), &[off]).map_err(fail)?;
        s.scheme.engine.set_step_limit(s.step_limit);
        r
        })
    }

    /// Check `text` with the checker written in FX-26 (read and parsed in
    /// FX-26 too): see [`crate::syn::check_with_fx26_checker`].
    pub fn check_with_own_checker(&mut self, text: &str) -> R<crate::syn::Checked26> {
        self.own_pieces()?;
        // Generous, but a checker that loops is an error, not a hang.
        self.scheme.engine.set_step_limit(Some(2_000_000_000));
        let standard = self.standard26()?;
        let r = crate::syn::check_with_fx26_checker(&mut self.scheme, standard, FileId(0), text);
        self.scheme.engine.set_step_limit(self.step_limit);
        r
    }

    /// What the checker written in FX-26 noted of the effects of what it
    /// last checked (`checked-effects`): each expression's start, end (in
    /// characters) and effect summary, newest first.
    pub fn own_effect_summaries(&mut self) -> R<Vec<(i64, i64, i64)>> {
        self.released(|s| {
        let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
        let notes = s.scheme.call_global(&format!("{READER_PREFIX}checked-effects"), &[]).map_err(fail)?;
        let mut out = Vec::new();
        s.scheme.make(|m| {
            let mut l = m.get(notes);
            let heap = m.heap();
            while l.is_pair() {
                let p = heap.car(l);
                out.push((heap.bloblet_slot(p, 2).as_fixnum(), heap.bloblet_slot(p, 3).as_fixnum(), heap.bloblet_slot(p, 4).as_fixnum()));
                l = heap.cdr(l);
            }
            fixpt_heap::Value::FALSE
        });
        Ok(out)
        })
    }

    /// Compile `text` to a cellular word with the compiler written in FX-26
    /// (read and parsed in FX-26 too), and run it on the cellular machine:
    /// its value as Scheme would write it, or `!! ` and why not.
    pub fn compile_with_own_compiler(&mut self, text: &str) -> R<String> {
        self.compile_with_own_compiler_showing(text, false).map(|(out, _)| out)
    }

    /// The checker's start for the next form of this session's program:
    /// the initial environment, if it has not begun; else none, so that the
    /// form is checked after the ones before.
    fn next_standard(&mut self) -> R<Option<fixpt_scheme::Handle>> {
        if self.own_begun { Ok(None) } else { self.standard26().map(Some) }
    }

    /// `text`, one form, as the next of this session's program: checked
    /// after the forms before, compiled against the globals they made, and
    /// run; as [`compile_with_own_compiler_showing`](Self::compile_with_own_compiler_showing).
    fn compile_form_showing(&mut self, text: &str, show: bool) -> R<(String, Option<String>)> {
        self.own_pieces()?;
        let standard = self.next_standard()?;
        let r = self.compile_showing_in(standard, text, show);
        self.own_begun |= !matches!(&r, Ok((out, _)) if out.starts_with("!! check:"));
        r
    }

    /// The same, and, if `show`, the words it made, disassembled. A whole
    /// program: the checker begins again.
    pub fn compile_with_own_compiler_showing(&mut self, text: &str, show: bool) -> R<(String, Option<String>)> {
        self.own_pieces()?;
        let standard = self.standard26()?;
        self.own_begun = false;
        // The compiler, too, sees none of the globals made before.
        self.scheme
            .call_global(&format!("{READER_PREFIX}compile-forget-globals!"), &[])
            .map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), e.to_string()))?;
        self.compile_showing_in(Some(standard), text, show)
    }

    fn compile_showing_in(&mut self, standard: Option<fixpt_scheme::Handle>, text: &str, show: bool) -> R<(String, Option<String>)> {
        self.own_pieces()?;
        self.released(|s| {
        s.scheme.engine.set_step_limit(None);
        let on = s.scheme.make(|_| fixpt_heap::Value::boolean(s.register_code));
        s.scheme
            .call_global(&format!("{READER_PREFIX}compile-registers!"), &[on])
            .map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), e.to_string()))?;
        let r = crate::syn::compile_with_fx26_compiler_showing(&mut s.scheme, standard, FileId(0), text, show, s.step_limit);
        s.scheme.engine.set_step_limit(s.step_limit);
        r
        })
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

/// A definition's type, if it says one, and initializer, when `form` is
/// `(define name [type] init)` of `name`; not one of the forms that define
/// names of their own (`define-generative`'s coercions, say).
fn definition_init<'f>(form: &'f Syntax, c: &Checker, name: Sym) -> Option<(Option<&'f Syntax>, &'f Syntax)> {
    let fixpt_read::Datum::List { items, tail: None } = &form.datum else { return None };
    let is = |s: &Syntax, n: &str| s.as_symbol().is_some_and(|x| c.interner.name(x) == n);
    if !((is(items.first()?, "define") || is(items.first()?, "define*")) && is(items.get(1)?, c.interner.name(name))) {
        return None;
    }
    match items.len() {
        3 => Some((None, &items[2])),
        4 => Some((Some(&items[2]), &items[3])),
        _ => None,
    }
}
