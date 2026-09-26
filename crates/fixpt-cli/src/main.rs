//! `fixpt` — the command-line driver.
//!
//! Argument parsing is hand-rolled rather than pulled from a crate: the command
//! surface is small and fixed, and a runtime whose whole point is a
//! self-contained, dumpable image is better off with a dependency list this
//! short. The same reasoning produced [`lineedit`], which is why this binary
//! has no external dependencies at all.

mod help;
mod fx26;
mod fx87;
mod fx91;
mod image_run;
mod lineedit;
mod speculate;

use crate::lineedit::{Line, LineReader};
use fixpt_engine::Backend;
use fixpt_heap::image;
use fixpt_scheme::Session;

const USAGE: &str = "\
fixpt — a Scheme engine with FX-87 and FX-91 front ends

usage:
  fixpt repl                     start a read-eval-print loop
  fixpt run FILE...              run each file in one session
  fixpt eval EXPR                evaluate one expression and print it
  fixpt dump-heap -o OUT FILE... run FILE... and write the resulting heap image
  fixpt build -o PROG FILE...    the same, as a standalone executable
  fixpt run-image FILE [ARG...]  run a heap image's entry point
  fixpt image info FILE          describe a heap image
  fixpt image verify FILE        load a heap image and check its invariants
  fixpt help                     show this

options:
  --dialect scheme|fx87|fx91|fx26  source language (default: scheme)
  --engine bytecode|ast          execution engine (default: bytecode)
  --main NAME                    an image's entry point (default: main)
  --reader scheme|fx26           the Scheme REPL's eager reader (default: scheme)
  --fx26-run lower|evaluate|threaded
                                 how FX-26 runs, once checked: lowered to Scheme
                                 (default), by the evaluator written in FX-26, or
                                 compiled to threaded words by the compiler
                                 written in FX-26 and run on the threaded machine
  --gc-every N                   also collect at every Nth safepoint, moving every
                                 object each time, to shake out rooting bugs
                                 (default: 0, only when the heap is full)

`--dialect fx87` and `--dialect fx91` select a *language*, not merely its
reader: a form is type- and effect-checked, erased to Scheme and run on the same
engine. Each REPL reports in its own reference's layout — FX-91 puts the type
and effect above the value, FX-87 after it. `--dialect fx26` reports as FX-87
does; its lowered Scheme carries what the checker proved, as `%fx-note`
claims the compiler acts on.

`--reader fx26` reads the Scheme REPL's input with the eager reader written in
FX-26 rather than the one written in Scheme. It runs on every keystroke, so it
is loaded only after its licence is checked: every entry point's effect must
stay within the reader's own regions.

An image built with `build` is a program in its own right: it carries its own
heap, needs no `fixpt` on the target, and runs its entry point when invoked.
`run-image` accepts either kind of file, and picks the engine the image was
made with rather than being told.
";

fn main() {
    // A binary that carries an image *is* that program: it owns its whole
    // command line, and never looks like the driver that built it.
    if let Some(heap) = image_run::embedded_in_self() {
        let argv: Vec<String> = std::env::args().skip(1).collect();
        std::process::exit(image_run::run_entry(heap, "main", &argv));
    }
    let args: Vec<String> = std::env::args().skip(1).collect();
    // The reader, the expander and the IR passes recurse on the Rust stack —
    // one level per nested form, and per nested macro use — so the work runs
    // on a thread with room for it. The size is only reserved address space;
    // pages are committed as they are touched. At about 3.5 KB a level in a
    // debug build, the expander's own limit of 2 000 nested macro uses needs
    // ~7 MB, more than the main thread is given.
    let code = std::thread::Builder::new()
        .name("fixpt".into())
        .stack_size(STACK)
        .spawn(move || run(&args))
        .expect("the main thread can be spawned")
        .join()
        .unwrap_or_else(|e| std::panic::resume_unwind(e));
    std::process::exit(code);
}

/// The stack the whole command runs on.
const STACK: usize = 256 << 20;

fn run(args: &[String]) -> i32 {
    let (flags, rest) = split_flags(args);
    // The dialect picks a *language*, which is a front end, not just a set of
    // lexical rules: FX-91 forms go through the checker and the code generator
    // before any of this runs them.
    let dialect = match flags.dialect.as_deref() {
        None | Some("scheme") => Dialect::Scheme,
        Some("fx91") => Dialect::Fx91,
        Some("fx87") => Dialect::Fx87,
        Some("fx26") => Dialect::Fx26,
        Some(name) => {
            eprintln!("fixpt: unknown dialect `{name}` (want scheme, fx87, fx91 or fx26)");
            return 2;
        }
    };
    let profile = fixpt_read::SyntaxProfile::SCHEME;

    let backend = match flags.engine.as_deref() {
        None | Some("bytecode") | Some("vm") | Some("compiled") => Backend::Bytecode,
        Some("ast") | Some("interp") | Some("interpreted") => Backend::Ast,
        Some(name) => {
            eprintln!("fixpt: unknown engine `{name}` (want bytecode or ast)");
            return 2;
        }
    };
    let entry = flags.main.as_deref().unwrap_or("main");
    let strategy = match flags.fx26_run.as_deref() {
        None | Some("lower") => fixpt_fx26::session::Strategy::Lower,
        Some("evaluate") => fixpt_fx26::session::Strategy::Evaluate,
        Some("threaded") => fixpt_fx26::session::Strategy::Threaded,
        Some(name) => {
            eprintln!("fixpt: unknown --fx26-run `{name}` (want lower, evaluate or threaded)");
            return 2;
        }
    };
    let _ = FX26_RUN.set(strategy);
    if let Some(n) = flags.gc_every.as_deref() {
        match n.parse::<u64>() {
            Ok(n) => {
                let _ = GC_EVERY.set(n);
            }
            Err(_) => {
                eprintln!("fixpt: --gc-every takes a count, 0 or more");
                return 2;
            }
        }
    }

    match rest.first().map(String::as_str) {
        None | Some("help") | Some("-h") | Some("--help") => {
            print!("{USAGE}");
            0
        }
        Some("repl") => match dialect {
            Dialect::Scheme => repl(profile, backend, flags.reader.as_deref() == Some("fx26")),
            Dialect::Fx87 => fx87::repl(backend),
            Dialect::Fx91 => fx91::repl(backend),
            Dialect::Fx26 => fx26::repl(backend),
        },
        Some("run") => {
            if rest.len() < 2 {
                eprintln!("fixpt run: needs at least one file");
                return 2;
            }
            match dialect {
                Dialect::Fx87 => fx87::run_files(backend, &rest[1..]),
                Dialect::Fx91 => fx91::run_files(backend, &rest[1..]),
                Dialect::Fx26 => fx26::run_files(backend, &rest[1..]),
                Dialect::Scheme => match run_files(profile, backend, &rest[1..]) {
                    Ok(_) => 0,
                    Err(e) => {
                        eprintln!("fixpt: {e}");
                        1
                    }
                },
            }
        }
        Some("eval") => {
            if rest.len() < 2 {
                eprintln!("fixpt eval: needs an expression");
                return 2;
            }
            match dialect {
                Dialect::Fx87 => return fx87::eval(backend, &rest[1..].join(" ")),
                Dialect::Fx91 => return fx91::eval(backend, &rest[1..].join(" ")),
                Dialect::Fx26 => return fx26::eval(backend, &rest[1..].join(" ")),
                Dialect::Scheme => {}
            }
            let mut session = Session::with_backend(backend);
    apply_gc_policy(&mut session.rt.heap);
            session.profile = profile;
            match session.eval_to_string("<argument>", &rest[1..].join(" ")) {
                Ok(v) => {
                    println!("{v}");
                    0
                }
                Err(e) => {
                    eprintln!("fixpt: {e}");
                    1
                }
            }
        }
        Some("dump-heap") | Some("build") => {
            if dialect != Dialect::Scheme {
                eprintln!("fixpt: {} is Scheme-only for now", rest[0]);
                return 2;
            }
            let standalone = rest[0] == "build";
            let Some(out) = flags.out.clone() else {
                eprintln!("fixpt {}: needs -o OUT", rest[0]);
                return 2;
            };
            dump_command(profile, backend, &rest[1..], &out, standalone)
        }
        Some("run-image") => {
            if rest.len() < 2 {
                eprintln!("fixpt run-image: needs an image file");
                return 2;
            }
            match image_run::read_image(&rest[1]) {
                Ok(heap) => image_run::run_entry(heap, entry, &rest[2..]),
                Err(e) => {
                    eprintln!("fixpt: {e}");
                    1
                }
            }
        }
        Some("image") => image_command(&rest[1..]),
        Some(other) => {
            eprintln!("fixpt: unknown command `{other}`\n\n{USAGE}");
            2
        }
    }
}

/// Which language the source is in.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Dialect {
    Scheme,
    Fx87,
    Fx91,
    Fx26,
}

struct Flags {
    dialect: Option<String>,
    engine: Option<String>,
    out: Option<String>,
    main: Option<String>,
    reader: Option<String>,
    fx26_run: Option<String>,
    gc_every: Option<String>,
}

/// `--fx26-run`, for every FX-26 session this process starts.
pub(crate) static FX26_RUN: std::sync::OnceLock<fixpt_fx26::session::Strategy> = std::sync::OnceLock::new();
/// `--gc-every`, for every heap this process starts.
pub(crate) static GC_EVERY: std::sync::OnceLock<u64> = std::sync::OnceLock::new();

/// Apply `--gc-every` to a session's heap.
pub(crate) fn apply_gc_policy(heap: &mut fixpt_heap::Heap) {
    if let Some(n) = GC_EVERY.get() {
        heap.gc_every = *n;
    }
}

fn split_flags(args: &[String]) -> (Flags, Vec<String>) {
    let mut flags = Flags {
        dialect: None,
        engine: None,
        out: None,
        main: None,
        reader: None,
        fx26_run: None,
        gc_every: None,
    };
    let mut rest = Vec::new();
    let mut i = 0;
    // Each flag takes a value, spelled either `--flag v` or `--flag=v`.
    type Setter = fn(&mut Flags, String);
    let named: [(&str, Setter); 7] = [
        ("--fx26-run", |f, v| f.fx26_run = Some(v)),
        ("--gc-every", |f, v| f.gc_every = Some(v)),
        ("--dialect", |f, v| f.dialect = Some(v)),
        ("--reader", |f, v| f.reader = Some(v)),
        ("--engine", |f, v| f.engine = Some(v)),
        ("--main", |f, v| f.main = Some(v)),
        ("-o", |f, v| f.out = Some(v)),
    ];
    'outer: while i < args.len() {
        for (name, set) in named {
            if args[i] == name && i + 1 < args.len() {
                set(&mut flags, args[i + 1].clone());
                i += 2;
                continue 'outer;
            }
            let prefix = format!("{name}=");
            if let Some(v) = args[i].strip_prefix(&prefix) {
                set(&mut flags, v.to_string());
                i += 1;
                continue 'outer;
            }
        }
        rest.push(args[i].clone());
        i += 1;
    }
    (flags, rest)
}

fn run_files(
    profile: fixpt_read::SyntaxProfile,
    backend: Backend,
    files: &[String],
) -> Result<Session, String> {
    let mut session = Session::with_backend(backend);
    apply_gc_policy(&mut session.rt.heap);
    session.profile = profile;
    for f in files {
        let text = std::fs::read_to_string(f).map_err(|e| format!("cannot read {f}: {e}"))?;
        session.eval_str(f, &text).map_err(|e| e.to_string())?;
    }
    Ok(session)
}

/// `dump-heap` and `build`: run the files, then write out what they left behind.
///
/// Collecting first is not just tidiness. The collector compacts, so the image
/// holds only reachable objects laid out contiguously — which is what makes
/// loading a `memcpy` and a root fixup rather than a graph walk.
fn dump_command(
    profile: fixpt_read::SyntaxProfile,
    backend: Backend,
    files: &[String],
    out: &str,
    standalone: bool,
) -> i32 {
    let mut session = match run_files(profile, backend, files) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("fixpt: {e}");
            return 1;
        }
    };
    session.rt.heap.collect(&mut []);
    if let Err(e) = session.rt.heap.verify() {
        eprintln!("fixpt: refusing to write an unsound heap: {e}");
        return 1;
    }
    let bytes = image::dump(&session.rt.heap);
    let result = if standalone {
        image_run::embed(&bytes, out)
    } else {
        std::fs::write(out, &bytes).map_err(|e| format!("cannot write {out}: {e}"))
    };
    match result {
        Ok(()) => {
            let kind = if standalone {
                "executable"
            } else {
                "heap image"
            };
            let size = std::fs::metadata(out)
                .map(|m| m.len())
                .unwrap_or(bytes.len() as u64);
            println!(
                "wrote {out}: {kind}, {size} bytes ({} live words)",
                session.rt.heap.used()
            );
            0
        }
        Err(e) => {
            eprintln!("fixpt: {e}");
            1
        }
    }
}

fn repl(profile: fixpt_read::SyntaxProfile, backend: Backend, fx26_reader: bool) -> i32 {
    let mut session = Session::with_backend(backend);
    apply_gc_policy(&mut session.rt.heap);
    session.profile = profile;
    let engine = match backend {
        Backend::Ast => "AST engine",
        Backend::Bytecode => "bytecode engine",
    };
    println!("fixpt {} — {} reader, {engine}", env!("CARGO_PKG_VERSION"), profile.name);
    println!("(an expression, `,help` for commands, or ^D to leave)");

    let mut reader = LineReader::new(".fixpt_history", profile);
    // The eager reader reads the Scheme profile; if it cannot be loaded, the
    // REPL still works, re-reading with the Rust reader.
    let mut eager = if profile.name != "scheme" {
        None
    } else if fx26_reader {
        match load_fx26_reader(&mut session) {
            Ok(r) => {
                println!("(reading with the eager reader written in FX-26; its licence checked)");
                Some(r)
            }
            Err(why) => {
                println!("(the FX-26 reader is not used: {why}; reading with the Scheme one)");
                fixpt_scheme::eager::EagerReader::new(&mut session).ok()
            }
        }
    } else {
        fixpt_scheme::eager::EagerReader::new(&mut session).ok()
    };
    // What to give back for further editing after a mid-form hole.
    let mut initial = String::new();
    loop {
        reader.set_completions(bound_names(&session));
        let line = match eager.as_mut() {
            Some(r) => {
                let mut oracle = EagerOracle { session: &mut session, reader: r };
                reader.read_with("> ", "| ", &mut oracle, &initial)
            }
            None => {
                let mut oracle = lineedit::Reread(profile);
                reader.read_with("> ", "| ", &mut oracle, &initial)
            }
        };
        initial.clear();
        match line {
            Line::Eof => {
                reader.save();
                return 0;
            }
            Line::Interrupted => continue,
            // `,help` written before the form is finished: answer it as though
            // the form had been closed right after the hole, then hand the
            // form back — minus the hole — to carry on typing.
            Line::Ask { closed, keep } => {
                match run_line(&mut session, &closed) {
                    // `,resume` would continue the form as it was closed off to
                    // answer the hole — not the one being typed — so it is not
                    // offered here.
                    Ok(v) => {
                        let report: Vec<&str> = v.lines().filter(|l| !l.contains("`,resume EXPR`")).collect();
                        println!("{}", report.join("\n"));
                        println!("; the form is given back without the hole: carry on typing");
                    }
                    Err(e) => eprintln!("{e}"),
                }
                initial = keep;
            }
            Line::Form(text) if hole_command(&text).is_some() => {
                match hole_command(&text).expect("just checked") {
                    HoleCommand::Where => match session.held_hole_report() {
                        Some(r) => println!("{}", hole_report(&r)),
                        None => println!("; no hole is held — write `,help` inside a form to make one"),
                    },
                    HoleCommand::Resume(expr) => match resume_line(&mut session, expr) {
                        Ok(v) => println!("{}", fixpt_runtime::write_value(&session.rt.heap, v)),
                        Err(fixpt_scheme::SessionError::Hole(r)) => println!("{}", hole_report(&r)),
                        Err(e) => eprintln!("{e}"),
                    },
                }
            }
            Line::Form(text) if help::parse(&text).is_some() => {
                let ask = help::parse(&text).expect("just checked");
                help::answer(&mut SchemeHelp(&session), &ask);
            }
            Line::Form(text) => match run_line(&mut session, &text) {
                Ok(v) => println!("{v}"),
                Err(e) => eprintln!("{e}"),
            },
        }
    }
}

/// Run one REPL line, answering a `,help` hole rather than evaluating past it.
///
/// Scheme is where the dynamic half of `,help` earns its keep. The FX dialects
/// can answer a hole statically, from the operator's type; Scheme has no types
/// to consult, so the only way to say anything about a position is to *get
/// there* — run the program as written, with the hole replaced by a primitive
/// that reports the machine's pending work instead of computing a value. The
/// answer is then made of things that actually happened: this operator, these
/// arguments, these values.
fn run_line(session: &mut Session, text: &str) -> Result<String, String> {
    let forms = session.read_forms("<repl>", text).map_err(|e| e.to_string())?;
    let has_hole = {
        let names = |s: fixpt_read::Sym| session.rt.interner.name(s).to_string();
        forms.iter().any(|f| help::mentions_hole(f, &names))
    };
    if has_hole {
        let with = session.rt.interner.intern("%hole");
        let names = |s: fixpt_read::Sym| session.rt.interner.name(s).to_string();
        let plugged: Vec<_> =
            forms.iter().map(|f| help::plug_hole(f, &names, with)).collect();
        return match session.eval_forms(&plugged) {
            // Reaching the hole raises, so a value means the hole was never
            // reached: the program took a branch around it, which is itself
            // the answer.
            Ok(v) => Ok(format!(
                "; the hole was never reached — the form evaluated to {}",
                fixpt_runtime::write_value(&session.rt.heap, v)
            )),
            Err(e @ fixpt_scheme::SessionError::Hole(_)) => Ok(format!(
                "{}\n; `,resume EXPR` continues from the hole with EXPR's value; `,where` repeats this",
                hole_report(&e.to_string())
            )),
            Err(e) => Ok(hole_report(&e.to_string())),
        };
    }
    session
        .eval_forms(&forms)
        .map(|v| fixpt_runtime::write_value(&session.rt.heap, v))
        .map_err(|e| e.to_string())
}

/// `,resume EXPR`. The expression may itself contain a hole — continuing
/// with a value that is still being worked out — so it is plugged exactly as
/// an ordinary line is.
fn resume_line(session: &mut Session, text: &str) -> Result<fixpt_heap::Value, fixpt_scheme::SessionError> {
    let forms = session.read_forms("<resume>", text)?;
    let with = session.rt.interner.intern("%hole");
    let names = |s: fixpt_read::Sym| session.rt.interner.name(s).to_string();
    let plugged: Vec<_> = forms.iter().map(|f| help::plug_hole(f, &names, with)).collect();
    session.resume_forms(&plugged)
}

enum HoleCommand<'a> {
    /// `,where` — describe the held hole again.
    Where,
    /// `,resume EXPR` — continue the held hole with a value.
    Resume(&'a str),
}

fn hole_command(line: &str) -> Option<HoleCommand<'_>> {
    let line = line.trim();
    if line == ",where" {
        return Some(HoleCommand::Where);
    }
    let rest = line.strip_prefix(",resume")?;
    if !rest.is_empty() && !rest.starts_with(char::is_whitespace) {
        return None;
    }
    Some(HoleCommand::Resume(rest.trim()))
}

/// Print the engine's report as help rather than as a failure.
fn hole_report(raised: &str) -> String {
    let body = raised
        .split_once("evaluation reached a hole")
        .map(|(_, rest)| rest.trim_start_matches([':', ' ']))
        .unwrap_or(raised);
    let mut out = String::from("; at the hole:");
    for line in body.lines() {
        let line = line.trim();
        if !line.is_empty() {
            out.push_str("\n  ");
            out.push_str(line);
        }
    }
    out
}

/// The eager reader written in FX-26, checked, licensed and loaded into this
/// session. Nothing of it runs until the licence is checked: it runs on every
/// keystroke, so every entry point's effect must stay within the regions the
/// reader owns — allocation, and its own state, prompt and marks.
fn load_fx26_reader(session: &mut Session) -> Result<fixpt_scheme::eager::EagerReader, String> {
    fixpt_fx26::session::load_eager_reader(session)?;
    fixpt_scheme::eager::EagerReader::attach(session, fixpt_fx26::session::READER_PREFIX).map_err(|e| e.to_string())
}

/// The eager reader as the line editor's oracle: one checkpoint per character,
/// so each keystroke is one character's worth of parsing, and a mistake is
/// reported where it is made.
struct EagerOracle<'a> {
    session: &'a mut Session,
    reader: &'a mut fixpt_scheme::eager::EagerReader,
}

impl lineedit::Oracle for EagerOracle<'_> {
    fn status(&mut self, text: &str, at_enter: bool) -> lineedit::Status {
        eager_status(self.reader, self.session, text, at_enter, fixpt_read::SyntaxProfile::SCHEME, true)
    }
}

/// What an eager reader says of `text`, as the line editor wants it. With
/// `holes`, a `,help` hole at `Enter` asks for the form to be answered while
/// still unfinished; without, it is simply unfinished.
pub(crate) fn eager_status(
    reader: &mut fixpt_scheme::eager::EagerReader,
    session: &mut Session,
    text: &str,
    at_enter: bool,
    profile: fixpt_read::SyntaxProfile,
    holes: bool,
) -> lineedit::Status {
    use fixpt_scheme::eager::EagerStatus;
    use lineedit::Status;
    match reader.status(session, text, at_enter) {
        Ok(EagerStatus::Complete) => Status::Complete,
        Ok(EagerStatus::Incomplete) => Status::Incomplete,
        Ok(EagerStatus::Invalid { at, message }) => Status::Invalid { at, message },
        Ok(EagerStatus::Hole { closers }) if at_enter && holes => Status::Ask {
            closed: format!("{text}{closers}"),
            keep: without_trailing_hole(text),
        },
        Ok(EagerStatus::Hole { .. }) => Status::Incomplete,
        // The eager reader failing is a bug in it, not the user's problem:
        // fall back to the Rust reader for this answer.
        Err(_) => lineedit::Oracle::status(&mut lineedit::Reread(profile), text, at_enter),
    }
}

/// The text with the `,help` it ends with taken off.
fn without_trailing_hole(text: &str) -> String {
    let trimmed = text.trim_end();
    for hole in [",help", ",?"] {
        if let Some(rest) = trimmed.strip_suffix(hole) {
            return rest.to_string();
        }
    }
    text.to_string()
}

/// Scheme's answer to the same questions.
///
/// Less than FX can say, and the difference is the point: without types there
/// is no way to ask what accepts a value, so `,fits` reports that it needs a
/// typed dialect rather than returning nothing. What Scheme *does* know is the
/// primitive table — every name with its arity — and which globals are bound.
struct SchemeHelp<'a>(&'a Session);

impl help::Helpful for SchemeHelp<'_> {
    fn dialect(&self) -> &'static str {
        "Scheme"
    }

    fn holes(&self) -> bool {
        true
    }

    fn resumable(&self) -> bool {
        true
    }

    fn describe(&mut self, name: &str) -> Vec<String> {
        let mut out = Vec::new();
        if let Some(i) = fixpt_runtime::prim::lookup(name) {
            let d = fixpt_runtime::prim::def(i);
            out.push(format!("{name} — a primitive, {}", arity(d.min, d.max)));
        }
        let heap = &self.0.rt.heap;
        if let Some(sym) = heap.intern_existing(name) {
            let v = heap.global(heap.symbol_global_slot(sym));
            if !v.is_unbound() && out.is_empty() {
                out.push(match arity_of_closure(self.0, v) {
                    Some(text) => format!("{name} — a procedure, {text}"),
                    None => format!("{name} = {}", fixpt_runtime::write_value(heap, v)),
                });
            }
        }
        out
    }

    fn apropos(&mut self, pattern: &str) -> Vec<String> {
        let mut out: Vec<String> = bound_names(self.0)
            .into_iter()
            .filter(|n| n.contains(pattern))
            .map(|n| match fixpt_runtime::prim::lookup(&n) {
                Some(i) => {
                    let d = fixpt_runtime::prim::def(i);
                    format!("{n} — a primitive, {}", arity(d.min, d.max))
                }
                None => n,
            })
            .collect();
        out.sort();
        out.dedup();
        out
    }
}

fn arity(min: usize, max: Option<usize>) -> String {
    match max {
        Some(m) if m == min => format!("{min} argument(s)"),
        Some(m) => format!("{min} to {m} arguments"),
        None => format!("{min} or more arguments"),
    }
}

/// A compiled or interpreted closure's arity, read off its code object.
fn arity_of_closure(session: &Session, v: fixpt_heap::Value) -> Option<String> {
    let heap = &session.rt.heap;
    if !heap.is_a(v, fixpt_heap::ObjType::Closure) {
        return None;
    }
    let code = heap.closure_code(v);
    if !heap.is_a(code, fixpt_heap::ObjType::Code) {
        return None;
    }
    let n = heap.bloblet_slot(code, fixpt_core::lower::CODE_ARITY).as_fixnum() as usize;
    let rest = heap.bloblet_slot(code, fixpt_core::lower::CODE_HAS_REST).is_true();
    Some(arity(n, if rest { None } else { Some(n) }))
}

/// Every name the session has actually bound, for completion.
///
/// Read out of the heap's symbol table rather than kept alongside it, so a
/// procedure defined a moment ago can be completed immediately and one that was
/// never defined never appears.
pub fn bound_names(session: &Session) -> Vec<String> {
    let heap = &session.rt.heap;
    let symbols: Vec<fixpt_heap::Value> = heap.symbols_slice().to_vec();
    symbols
        .into_iter()
        .filter(|s| !heap.global(heap.symbol_global_slot(*s)).is_unbound())
        .map(|s| heap.symbol_name(s))
        .filter(|n| !n.starts_with('%'))
        .collect()
}

fn image_command(args: &[String]) -> i32 {
    match args.first().map(String::as_str) {
        Some("info") | Some("verify") if args.len() == 2 => {
            let path = &args[1];
            let bytes = match std::fs::read(path) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("fixpt: cannot read {path}: {e}");
                    return 1;
                }
            };
            // An image may be appended to an executable rather than standing
            // alone; look for the trailer first.
            let img = image::extract_embedded(&bytes).unwrap_or(&bytes);
            match image::load(img) {
                Ok(heap) => {
                    println!("{path}: valid fixpt heap image");
                    println!("  live words:  {}", heap.used());
                    println!("  globals:     {}", heap.global_count());
                    println!("  symbols:     {}", heap.symbol_count());
                    if img.len() != bytes.len() {
                        println!(
                            "  embedded in an executable of {} bytes",
                            bytes.len() - img.len()
                        );
                    }
                    match heap.verify() {
                        Ok(()) => {
                            println!("  structure:   ok");
                            0
                        }
                        Err(e) => {
                            eprintln!("  structure:   FAILED: {e}");
                            1
                        }
                    }
                }
                Err(e) => {
                    eprintln!("fixpt: {path}: {e}");
                    1
                }
            }
        }
        _ => {
            eprintln!("usage: fixpt image info|verify FILE");
            2
        }
    }
}
