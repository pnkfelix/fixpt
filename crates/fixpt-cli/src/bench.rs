//! `fixpt bench`: FX-26 programs timed on each way this repository has of
//! running them, best of a few runs, as an aligned table. Each way's answer
//! is compared with the lowered program's; one that differs is marked.
//! A second table times compiling them, phase by phase, and the front end
//! too. (PLAN.md, M13 step 13b; the figures go in `docs/performance.md`.)

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_fx26::{Checker, Top};
use fixpt_heap::Value;
use fixpt_read::FileId;
use std::time::Instant;

const USAGE: &str = "\
usage: fixpt bench [--runs N] [--machines LIST] [--tables LIST] [--front-end] [FILE...]

Times FX-26 programs, best of N runs (default 3), and prints two tables.
With no FILE, the benchmarks in crates/fixpt-fx26/tests/programs/bench,
and in the compile table scheme-bench/peval.fx too: a program of a size
whose compiling, unlike theirs, takes long enough to follow over time.

The run table: each way of running them, the run alone (checking and
compiling are done before the clock starts); an answer that differs from
the lowered one is marked `✗`. Machines (--machines, default: all):
  lowered     lowered to Scheme, run on the bytecode engine (its compiling
              of the lowered Scheme, quick, counted as run)
  rust        compiled to cellular words, run by the machine written in Rust
  hand        run by the hand-encoded arm64 machine
  stencils    run by the stencil machine (a build with nightly only)
  compiled    each word compiled to machine code first (native-compiled)
  registers   each lambda's register code, run by the hand-encoded machine
  native      the native calling convention: the procedure the program's
              last line calls, on integer literals, compiled and called
              (`—` if the last line is not such a call, or it is declined)

The compile table: each phase alone, for each program; with --front-end,
also for the front end (the FX-26 reader, checker and compilers with
their bootstrap), once (about 10 s, most of it the lowered reader):
  check       the Rust checker (reading included)
  lower       lowering what it checked to Scheme
  words       the Rust compiler to cellular words, register code included
  arm64       every word's cells to arm64, by the Rust `assemble_word`
  registers   the same, register code where a word has some
  native      `direct.rs`, the native convention (`—` where the run table
              has none, and for the front end)
  fx read     the reader written in FX-26 (lowered, as the REPL runs it)
  fx parse    the parser written in FX-26
  fx check    the checker written in FX-26, making no line for each form
              (`FIXPT_BENCH_LINES` set: making them, as `fixpt check` does)
  fx words    the compiler written in FX-26, register code included
  fx arm64    every word's cells to arm64, by `native.fx`
  fx M words  millions of words the `fx` phases allocated
  fx GCs      their collections, minor and major
The arm64 phases assemble, and do not place the code. The `fx` phases
run as the front end's register code, as at the REPL.

--tables run,compile chooses the tables (default: both).
";

type Run = fn(&mut fixpt_runtime::Runtime, Value, &[Value]) -> Result<Value, String>;

/// `fixpt bench …`: an exit code.
pub fn command(args: &[String]) -> i32 {
    let (mut runs, mut wanted, mut files) = (3usize, None::<Vec<String>>, Vec::new());
    let (mut run_table, mut compile_table, mut front_end) = (true, true, false);
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--runs" => match it.next().and_then(|n| n.parse().ok()).filter(|n: &usize| *n > 0) {
                Some(n) => runs = n,
                None => return usage("`--runs` wants a number of runs"),
            },
            "--machines" => match it.next() {
                Some(l) => wanted = Some(l.split(',').map(|m| m.trim().to_string()).collect()),
                None => return usage("`--machines` wants a list"),
            },
            "--tables" => match it.next() {
                Some(l) => {
                    let l: Vec<&str> = l.split(',').map(str::trim).collect();
                    if let Some(bad) = l.iter().find(|t| !["run", "compile"].contains(t)) {
                        return usage(&format!("unknown table `{bad}` (want run or compile)"));
                    }
                    (run_table, compile_table) = (l.contains(&"run"), l.contains(&"compile"));
                }
                None => return usage("`--tables` wants a list"),
            },
            "--front-end" => front_end = true,
            "-h" | "--help" => {
                print!("{USAGE}");
                return 0;
            }
            f if f.starts_with('-') => return usage(&format!("unknown option `{f}`")),
            f => files.push(std::path::PathBuf::from(f)),
        }
    }
    let all = ["lowered", "rust", "hand", "stencils", "compiled", "registers", "native"];
    let mut machines: Vec<&str> = match &wanted {
        Some(w) => {
            if let Some(bad) = w.iter().find(|m| !all.contains(&m.as_str())) {
                return usage(&format!("unknown machine `{bad}`"));
            }
            all.iter().copied().filter(|m| w.iter().any(|x| x == m)).collect()
        }
        None => all.to_vec(),
    };
    if fixpt_native::stencil::opt_levels().is_empty() {
        machines.retain(|m| *m != "stencils");
    }
    let mid_sized = files.is_empty();
    if files.is_empty() {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../fixpt-fx26/tests/programs/bench");
        let Ok(entries) = std::fs::read_dir(dir) else { return usage("no FILE, and the benchmarks are not where this build expects") };
        files = entries.filter_map(|e| Some(e.ok()?.path())).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
        files.sort();
    }
    let mut programs = Vec::new();
    for path in &files {
        let Ok(text) = std::fs::read_to_string(path) else {
            eprintln!("fixpt bench: cannot read {}", path.display());
            return 1;
        };
        let name = path.file_stem().map_or_else(|| path.display().to_string(), |s| s.to_string_lossy().to_string());
        programs.push((name, text));
    }
    if run_table {
        let code = run_table_of(&programs, &machines, runs);
        if code != 0 {
            return code;
        }
    }
    if compile_table {
        if run_table {
            println!();
        }
        // A mid-sized program, compiled only: what its run takes says less.
        if mid_sized {
            let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../scheme-bench/peval.fx");
            match std::fs::read_to_string(path) {
                Ok(text) => programs.push(("peval".to_string(), text)),
                Err(e) => eprintln!("fixpt bench: no peval ({e}), so no mid-sized program"),
            }
        }
        return compile_table_of(&programs, runs, front_end);
    }
    0
}

/// The run table, printed: an exit code.
fn run_table_of(programs: &[(String, String)], machines: &[&str], runs: usize) -> i32 {
    let mut rows = Vec::new();
    let mut notes = Vec::new();
    for (name, text) in programs {
        eprintln!("fixpt bench: {name}…");
        match row(name, text, machines, runs, &mut notes) {
            Ok(r) => rows.push(r),
            Err(e) => {
                eprintln!("fixpt bench: {name}: {e}");
                return 1;
            }
        }
    }
    let mut header = vec!["program".to_string(), "answer".to_string()];
    header.extend(machines.iter().map(|m| m.to_string()));
    if machines.contains(&"native") {
        header.extend(["M words".to_string(), "GCs".to_string()]);
    }
    print_table(&header, &rows, 2);
    println!("\nrun alone: best of {runs} run(s), in milliseconds; the answer is the lowered program's.");
    if machines.contains(&"native") {
        println!("M words: millions of words the native run allocated; GCs: its collections, minor and major.");
    }
    for n in notes {
        println!("{n}");
    }
    0
}

fn usage(why: &str) -> i32 {
    eprintln!("fixpt bench: {why}\n\n{USAGE}");
    2
}

/// One program's row: its name, its answer, and a time per machine.
fn row(name: &str, text: &str, machines: &[&str], runs: usize, notes: &mut Vec<String>) -> Result<Vec<String>, String> {
    let answer = {
        let mut s = Fx26Session::with_backend(Backend::Bytecode).map_err(|e| e.message)?;
        s.scheme.engine.set_step_limit(None);
        match s.run_program(text) {
            Ok(Ok(v)) => v,
            Ok(Err(e)) => return Err(e),
            Err(e) => return Err(e.message),
        }
    };
    let lowered = lowered_run(text, runs)?;
    let short = if answer.chars().count() > 24 { format!("{}…", answer.chars().take(24).collect::<String>()) } else { answer.clone() };
    let mut out = vec![name.to_string(), short];
    let mut cell = |machine: &str, got: Option<(String, f64)>| match got {
        None => "—".to_string(),
        Some((v, t)) if v == answer => format!("{:.1}", 1e3 * t),
        Some((v, t)) => {
            notes.push(format!("✗ {name} on {machine}: {v}"));
            format!("{:.1} ✗", 1e3 * t)
        }
    };
    let (c, tops) = checked(text)?;
    let mut work = None;
    for m in machines {
        let got = match *m {
            "lowered" => Some(lowered.clone()),
            "rust" => on_machine(text, &c, &tops, runs, fixpt_engine::cellular::run_word, false, false),
            "hand" => on_machine(text, &c, &tops, runs, fixpt_native::cellular::run_word_as_is, false, false),
            "stencils" => on_machine(text, &c, &tops, runs, fixpt_native::stencil::run_word, false, false),
            "compiled" => on_machine(text, &c, &tops, runs, fixpt_native::cellular::run_word_compiled, false, true),
            "registers" => on_machine(text, &c, &tops, runs, fixpt_native::cellular::run_word_registers, true, true),
            _ => in_native_convention(text, runs).map(|(v, t, w)| {
                work = Some(w);
                (v, t)
            }),
        };
        out.push(cell(m, got));
    }
    if machines.contains(&"native") {
        match work {
            Some((words, gcs)) => out.extend([format!("{:.1}", words as f64 / 1e6), gcs.to_string()]),
            None => out.extend(["—".to_string(), "—".to_string()]),
        }
    }
    Ok(out)
}

pub(crate) fn checked(text: &str) -> Result<(Checker, Vec<Top>), String> {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), text).map_err(|e| e.message)?;
    let done = c.declare_ahead(&forms).map_err(|e| e.message)?;
    let mut tops = Vec::new();
    for (f, d) in forms.iter().zip(done) {
        if !d {
            tops.extend(c.top_all(f).map_err(|e| e.message)?);
        }
    }
    Ok((c, tops))
}

fn best(runs: usize, mut f: impl FnMut() -> String) -> (String, f64) {
    let (mut out, mut t) = (String::new(), f64::INFINITY);
    for _ in 0..runs {
        let start = Instant::now();
        out = f();
        t = t.min(start.elapsed().as_secs_f64());
    }
    (out, t)
}

/// The best time of `runs` runs of `f`, which times itself (what it does
/// before or after the run left out), and the last run's value.
fn best_of(runs: usize, mut f: impl FnMut() -> (String, f64)) -> (String, f64) {
    let (mut out, mut t) = (String::new(), f64::INFINITY);
    for _ in 0..runs {
        let (o, u) = f();
        out = o;
        t = t.min(u);
    }
    (out, t)
}

/// The best time of `runs` runs of `f`.
fn time(runs: usize, mut f: impl FnMut()) -> f64 {
    best(runs, || {
        f();
        String::new()
    })
    .1
}

/// The program checked and lowered by the Rust front end, then run on the
/// bytecode engine in a session of its own each time, only that timed.
fn lowered_run(text: &str, runs: usize) -> Result<(String, f64), String> {
    let compiled = fixpt_fx26::session::compile_program(text).map_err(|e| e.message)?;
    let code = compiled.code.join("\n");
    Ok(best_of(runs, || {
        let Ok(mut s) = Fx26Session::with_backend(Backend::Bytecode) else { return ("!! no session".into(), f64::INFINITY) };
        s.scheme.engine.set_step_limit(None);
        s.scheme.scope(|sc| {
            let start = Instant::now();
            let (_, r) = sc.eval_capturing("<fx26>", &code);
            let t = start.elapsed().as_secs_f64();
            (r.map_or_else(|e| format!("!! {e}"), |v| sc.write(v)), t)
        })
    }))
}

/// The program compiled by the Rust compiler to cellular words (with
/// register code, if asked), in a session of its own, and run by `run`.
/// Where the machine compiles words to machine code (`compiles`), that is
/// done first, and not timed.
fn on_machine(text: &str, c: &Checker, tops: &[Top], runs: usize, run: Run, registers: bool, compiles: bool) -> Option<(String, f64)> {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).ok()?;
    s.scheme.engine.set_step_limit(None);
    s.scheme.scope(|sc| {
        let w = sc.make(|m| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), c, text);
            comp.registers = registers;
            comp.program(tops).unwrap_or(Value::FALSE)
        });
        if compiles {
            let mut done = Ok(0);
            sc.make(|m| {
                let w = m.get(w);
                done = fixpt_native::cellular::with_machine(|nm| nm.compile_reachable_as(m.heap(), w, registers));
                Value::NULL
            });
            done.ok()?;
        }
        sc.runtime_unrooted().run_word = Some(run);
        Some(best(runs, || {
            let none = sc.make(|_| Value::NULL);
            match sc.call_global("%run-word", &[w, none]) {
                Ok(v) => sc.write(v),
                Err(e) => format!("!! {e}"),
            }
        }))
    })
}

/// A program whose last line calls a procedure on integer literals: the
/// program with that line naming the procedure instead, the procedure's
/// name, and the arguments.
fn native_call(text: &str) -> Option<(String, String, Vec<Value>)> {
    let lines: Vec<&str> = text.trim_end().lines().collect();
    let call = lines.last()?.trim().strip_prefix('(')?.strip_suffix(')')?;
    let mut parts = call.split_whitespace();
    let name = parts.next()?;
    let args: Vec<Value> = parts.map(|a| a.parse().ok().map(Value::fixnum)).collect::<Option<_>>()?;
    Some((format!("{}\n{name}", lines[..lines.len() - 1].join("\n")), name.to_string(), args))
}

/// A program whose last line calls a procedure on integers, that procedure
/// compiled in the native convention (`fixpt_native::direct`) and called
/// so: what it gave, and the best time, and the words it allocated and the
/// collections it made (the last run's: the same in each); or nothing, if
/// it is declined.
fn in_native_convention(text: &str, runs: usize) -> Option<(String, f64, (u64, u64))> {
    let (defs, _, args) = native_call(text)?;
    let (c, tops) = checked(&defs).ok()?;
    let mut s = Fx26Session::with_backend(Backend::Bytecode).ok()?;
    let mut m = fixpt_native::direct::DirectMachine::new().ok()?;
    s.scheme.scope(|sc| {
        let w = sc.make(|h| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(h.heap(), &c, &defs);
            comp.registers = true;
            comp.program(&tops).unwrap_or(Value::FALSE)
        });
        let none = sc.make(|_| Value::NULL);
        let h = sc.call_global("%run-word", &[w, none]).ok()?;
        let mut closure = Value::NULL;
        sc.make(|m| {
            closure = m.get(h);
            closure
        });
        let rt = sc.runtime_unrooted();
        let p = m.compile(&mut rt.heap, closure).ok()?[0].1;
        let mut work = (0, 0);
        let (v, t) = best(runs, || {
            let (a0, g0) = (rt.heap.allocated(), rt.heap.collections());
            let v = m.call(rt, p, &args, u64::MAX >> 1).map(|v| fixpt_runtime::write_value(&rt.heap, v)).unwrap_or_else(|t| format!("!! {}", t.what));
            work = (rt.heap.allocated() - a0, rt.heap.collections() - g0);
            v
        });
        Some((v, t, work))
    })
}

/// The rows under the header, each column as wide as its widest cell:
/// names and answers to the left, times to the right.
fn print_table(header: &[String], rows: &[Vec<String>], left: usize) {
    let width = |i: usize| rows.iter().map(|r| r[i].chars().count()).chain([header[i].chars().count()]).max().unwrap_or(0);
    let widths: Vec<usize> = (0..header.len()).map(width).collect();
    let line = |cells: &[String]| {
        let shown: Vec<String> = cells
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let pad = " ".repeat(widths[i] - c.chars().count());
                if i < left { format!("{c}{pad}") } else { format!("{pad}{c}") }
            })
            .collect();
        println!("| {} |", shown.join(" | "));
    };
    line(header);
    println!("|{}|", widths.iter().enumerate().map(|(i, w)| if i < left { format!(" {} ", "-".repeat(*w)) } else { format!(" {}:", "-".repeat(*w)) }).collect::<Vec<_>>().join("|"));
    for r in rows {
        line(r);
    }
}

/// The compile table, printed: an exit code.
fn compile_table_of(programs: &[(String, String)], runs: usize, with_front_end: bool) -> i32 {
    let mut fx = match fx_session() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("fixpt bench: the front end: {e}");
            return 1;
        }
    };
    let front_end = ("front end".to_string(), fixpt_fx26::bootstrap_program());
    let mut rows = Vec::new();
    for (name, text) in programs.iter().chain(with_front_end.then_some(&front_end)) {
        eprintln!("fixpt bench: compiling {name}…");
        // The front end's phases take seconds: once is enough.
        let (runs, native) = if name == &front_end.0 { (1, false) } else { (runs, true) };
        match compile_row(&mut fx, name, text, runs, native) {
            Ok(r) => rows.push(r),
            Err(e) => {
                eprintln!("fixpt bench: compiling {name}: {e}");
                return 1;
            }
        }
    }
    let header: Vec<String> = [
        "program", "check", "lower", "words", "arm64", "registers", "native", "fx read", "fx parse", "fx check", "fx words", "fx arm64", "fx M words",
        "fx GCs",
    ]
        .iter()
        .map(|h| h.to_string())
        .collect();
    print_table(&header, &rows, 1);
    let once = if with_front_end { "; the front end once" } else { "" };
    println!("\ncompile phases alone: best of {runs} run(s){once}, in milliseconds; fx M words and GCs: the fx phases' (the last run's).");
    0
}

/// `f` run `runs` times in `sc`: the best time, with the words allocated
/// and the collections made, and the last run's value.
fn fx_phase<T>(
    sc: &mut fixpt_scheme::Session,
    runs: usize,
    mut f: impl FnMut(&mut fixpt_scheme::Session) -> Result<T, String>,
) -> Result<((f64, (u64, u64)), T), String> {
    let (mut t, mut work, mut out) = (f64::INFINITY, (0, 0), None);
    for _ in 0..runs {
        let h = &sc.runtime_unrooted().heap;
        let (a0, g0, start) = (h.allocated(), h.collections(), Instant::now());
        out = Some(f(sc)?);
        t = t.min(start.elapsed().as_secs_f64());
        let h = &sc.runtime_unrooted().heap;
        work = (h.allocated() - a0, h.collections() - g0);
    }
    Ok(((t, work), out.expect("at least one run")))
}

/// A session with the pieces written in FX-26 loaded, as register code, as
/// the REPL runs them.
fn fx_session() -> Result<Fx26Session, String> {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).map_err(|e| e.message)?;
    s.scheme.runtime_unrooted().front_end_run_word = Some(fixpt_native::cellular::run_word_registers);
    s.front_end_compiled = true;
    s.load_own_pieces().map_err(|e| e.message)?;
    s.scheme.engine.set_step_limit(None);
    Ok(s)
}

/// One program's compile row: each phase timed alone.
fn compile_row(fx: &mut Fx26Session, name: &str, text: &str, runs: usize, native: bool) -> Result<Vec<String>, String> {
    let ms = |t: f64| format!("{:.2}", 1e3 * t);
    // `FIXPT_BENCH_ONLY=PHASE` (a column's name, `fx check`): that phase
    // run `runs` times, every other once, for a profiler to sample one.
    let only = std::env::var("FIXPT_BENCH_ONLY").ok();
    let r = |p: &str| if only.as_deref().is_none_or(|o| o == p) { runs } else { 1 };
    let t_check = time(r("check"), || {
        let _ = checked(text);
    });
    let (c, tops) = checked(text)?;
    let tops_rs = &tops;
    let t_lower = time(r("lower"), || {
        let mut g = fixpt_fx26::lower::Globals::with_prefix("fx:");
        for t in &tops {
            let _ = fixpt_fx26::session::lower_top(&c, &mut g, t);
        }
    });
    // The Rust compiler, and the Rust assemblers over what it made.
    let mut s = Fx26Session::with_backend(Backend::Bytecode).map_err(|e| e.message)?;
    s.scheme.engine.set_step_limit(None);
    let (t_words, t_arm, t_regs) = s.scheme.scope(|sc| -> Result<(f64, f64, f64), String> {
        let (mut t_words, mut made) = (f64::INFINITY, Err(String::new()));
        let w = sc.make(|m| {
            for _ in 0..r("words") {
                let start = Instant::now();
                let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, text);
                comp.registers = true;
                made = comp.program(&tops);
                t_words = t_words.min(start.elapsed().as_secs_f64());
            }
            made.clone().unwrap_or(Value::FALSE)
        });
        made?;
        let (mut t_arm, mut t_regs, mut failed) = (0.0, 0.0, Ok(()));
        sc.make(|m| {
            let w = m.get(w);
            let heap: &fixpt_heap::Heap = m.heap();
            let words = fixpt_fx26::syn::cell_words_reachable(heap, w);
            t_arm = time(r("arm64"), || {
                for &x in &words {
                    if let Err(e) = fixpt_native::cellular::assemble_word(heap, x, [0, 0]) {
                        failed = Err(e);
                    }
                }
            });
            t_regs = time(r("registers"), || {
                if let Err(e) = assemble_registers(heap, w) {
                    failed = Err(e);
                }
            });
            Value::NULL
        });
        failed?;
        Ok((t_words, t_arm, t_regs))
    })?;
    let t_native = if native { native_compile_time(text, r("native")) } else { None };
    // The pieces written in FX-26, as the REPL runs them: the reader
    // lowered, on the bytecode engine; the rest as the front end's register
    // code. Each phase starts from what the one before made.
    let (fx_read, fx_parse, fx_check, fx_words, fx_arm) = fx.scheme.scope(|sc| -> Result<_, String> {
        let file = FileId(0);
        let msg = |e: fixpt_fx26::FxError| e.message;
        // Reading, the files its `load-module`s name too (the front end's
        // module files built in), handed to the parser.
        let (fx_read, syns) = fx_phase(sc, r("fx read"), |sc| {
            fixpt_fx26::syn::supply_loaded(sc, file, text).map_err(msg)?;
            fixpt_fx26::syn::read_to_syns(sc, file, text).map_err(msg)
        })?;
        let (fx_parse, tops) = fx_phase(sc, r("fx parse"), |sc| fixpt_fx26::syn::parse_syns(sc, file, text, syns).map_err(msg))?;
        let standard = fixpt_fx26::syn::read_standard(sc).map_err(msg)?;
        let reader = |n: &str| format!("{}{n}", fixpt_fx26::session::READER_PREFIX);
        // A compile reads the facts, not each form's line; with
        // `FIXPT_BENCH_LINES` set, the lines too, as `fixpt check` makes them.
        let lines = std::env::var_os("FIXPT_BENCH_LINES").is_some();
        fixpt_fx26::syn::lines(sc, lines).map_err(|e| e.to_string())?;
        let (fx_check, ()) = fx_phase(sc, r("fx check"), |sc| {
            let r = sc.call_global(&reader("check-program"), &[standard, tops]).map_err(|e| e.to_string())?;
            let tag = sc.view(|v| v.get(r).field(2).and_then(|t| t.symbol_name()).unwrap_or_default());
            if tag == "k-ok" { Ok(()) } else { Err("the checker written in FX-26 finds it wrong".to_string()) }
        })?;
        let facts = fixpt_fx26::syn::rust_facts(sc, file, text).map_err(msg)?;
        let on = sc.make(|_| Value::TRUE);
        sc.call_global(&reader("compile-registers!"), &[on]).map_err(|e| e.to_string())?;
        let fx_words = fx_phase(sc, r("fx words"), |sc| {
            let made = fixpt_fx26::syn::compile_trees_to_word(sc, file, tops, facts).map_err(msg)?;
            made.map(|_| ()).map_err(|e| format!("the compiler written in FX-26: {e}"))
        });
        let off = sc.make(|_| Value::FALSE);
        sc.call_global(&reader("compile-registers!"), &[off]).map_err(|e| e.to_string())?;
        let (fx_words, ()) = fx_words?;
        // `native.fx` over the words the Rust compiler makes, as
        // `fx-compiled` at the REPL over the FX-26 compiler's.
        let w = sc.make(|m| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, text);
            comp.registers = true;
            comp.program(&tops_rs).unwrap_or(Value::FALSE)
        });
        let (fx_arm, ()) = fx_phase(sc, r("fx arm64"), |sc| fixpt_fx26::syn::assemble_reachable_by_fx26(sc, w, &mut |_, _, _, _| Ok(())))?;
        Ok((fx_read, fx_parse, fx_check, fx_words, fx_arm))
    })?;
    let work = [fx_read.1, fx_parse.1, fx_check.1, fx_words.1, fx_arm.1].iter().fold((0, 0), |a, w| (a.0 + w.0, a.1 + w.1));
    Ok(vec![
        name.to_string(),
        ms(t_check),
        ms(t_lower),
        ms(t_words),
        ms(t_arm),
        ms(t_regs),
        t_native.map_or_else(|| "—".to_string(), ms),
        ms(fx_read.0),
        ms(fx_parse.0),
        ms(fx_check.0),
        ms(fx_words.0),
        ms(fx_arm.0),
        format!("{:.1}", work.0 as f64 / 1e6),
        work.1.to_string(),
    ])
}

/// Every word `word` reaches assembled as `compile_reachable_as` with
/// register code compiles it: a word's register code where it has some
/// (and its cells too, where stack code cannot enter the register code),
/// else its cells.
fn assemble_registers(heap: &fixpt_heap::Heap, word: Value) -> Result<(), String> {
    use fixpt_heap::layout::cellular::{CLOSURE_WORD, PRIMITIVES, ROUTINE_DOCOL, WORD_CELL0, WORD_ENTRY, WORD_TWIN};
    use fixpt_native::cellular::{assemble_register_word, assemble_word};
    let closure = fixpt_heap::layout::kind("cellular-closure");
    let vargs = fixpt_heap::layout::regcode::op("vargs");
    let (mut todo, mut seen) = (vec![word], std::collections::HashSet::new());
    while let Some(w) = todo.pop() {
        if !seen.insert(w.raw()) {
            continue;
        }
        let entry = heap.bloblet_slot(w, WORD_ENTRY).as_fixnum() as u64;
        if entry != ROUTINE_DOCOL && entry < PRIMITIVES as u64 {
            continue;
        }
        for k in WORD_CELL0..=heap.bloblet_head(w).fields {
            let v = heap.bloblet_slot(w, k);
            if heap.is_cellular_word(v) {
                todo.push(v);
            } else if v.is_bloblet() && heap.bloblet_kind(v) == closure {
                todo.push(heap.bloblet_slot(v, CLOSURE_WORD));
            }
        }
        if entry != ROUTINE_DOCOL {
            continue;
        }
        let twin = heap.bloblet_slot(w, WORD_TWIN);
        if !heap.is_register_word(twin) {
            assemble_word(heap, w, [0, 0])?;
            continue;
        }
        for k in WORD_CELL0..=heap.bloblet_head(twin).fields {
            let v = heap.bloblet_slot(twin, k);
            if heap.is_cellular_word(v) {
                todo.push(v);
            }
        }
        if heap.bloblet_slot(twin, WORD_CELL0).as_fixnum() as usize == vargs {
            assemble_word(heap, w, [0, 0])?;
            continue;
        }
        assemble_register_word(heap, twin, [0, 0])?;
        if heap.bloblet_slot(twin, WORD_CELL0 + 1).as_fixnum() as usize > fixpt_heap::layout::regcode::REGS {
            assemble_word(heap, w, [0, 0])?;
        }
    }
    Ok(())
}

/// How long `direct.rs` takes to compile the procedure the program's last
/// line calls, in the native convention ([`in_native_convention`]); none
/// if it is declined.
fn native_compile_time(text: &str, runs: usize) -> Option<f64> {
    let (defs, _, _) = native_call(text)?;
    let (c, tops) = checked(&defs).ok()?;
    let mut s = Fx26Session::with_backend(Backend::Bytecode).ok()?;
    let mut m = fixpt_native::direct::DirectMachine::new().ok()?;
    s.scheme.scope(|sc| {
        let w = sc.make(|h| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(h.heap(), &c, &defs);
            comp.registers = true;
            comp.program(&tops).unwrap_or(Value::FALSE)
        });
        let none = sc.make(|_| Value::NULL);
        let h = sc.call_global("%run-word", &[w, none]).ok()?;
        let mut closure = Value::NULL;
        sc.make(|m| {
            closure = m.get(h);
            closure
        });
        let rt = sc.runtime_unrooted();
        m.compile(&mut rt.heap, closure).ok()?;
        Some(time(runs, || {
            let _ = m.compile(&mut rt.heap, closure);
        }))
    })
}
