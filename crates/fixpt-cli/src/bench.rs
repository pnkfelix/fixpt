//! `fixpt bench`: FX-26 programs timed on each way this repository has of
//! running them, best of a few runs, as an aligned table. Each way's answer
//! is compared with the lowered program's; one that differs is marked.
//! (PLAN.md, M13 step 13b; the figures go in `docs/performance.md`.)

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_fx26::{Checker, Top};
use fixpt_heap::Value;
use fixpt_read::FileId;
use std::time::Instant;

const USAGE: &str = "\
usage: fixpt bench [--runs N] [--machines LIST] [FILE...]

Times FX-26 programs, best of N runs (default 3), on each way of running
them, and prints a table; an answer that differs from the lowered one is
marked `✗`. With no FILE, the benchmarks in
crates/fixpt-fx26/tests/programs/bench.

machines (default: all), comma-separated:
  lowered     lowered to Scheme, run on the bytecode engine
  rust        compiled to cellular words, run by the machine written in Rust
  hand        run by the hand-encoded arm64 machine
  stencils    run by the stencil machine (a build with nightly only)
  compiled    each word compiled to machine code first (native-compiled)
  registers   each lambda's register code, run by the hand-encoded machine
  native      the native calling convention: the procedure the program's
              last line calls, on integer literals, compiled and called
              (`—` if the last line is not such a call, or it is declined)
";

type Run = fn(&mut fixpt_runtime::Runtime, Value, &[Value]) -> Result<Value, String>;

/// `fixpt bench …`: an exit code.
pub fn command(args: &[String]) -> i32 {
    let (mut runs, mut wanted, mut files) = (3usize, None::<Vec<String>>, Vec::new());
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
    if files.is_empty() {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../fixpt-fx26/tests/programs/bench");
        let Ok(entries) = std::fs::read_dir(dir) else { return usage("no FILE, and the benchmarks are not where this build expects") };
        files = entries.filter_map(|e| Some(e.ok()?.path())).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
        files.sort();
    }
    let mut rows = Vec::new();
    let mut notes = Vec::new();
    for path in &files {
        let Ok(text) = std::fs::read_to_string(path) else {
            eprintln!("fixpt bench: cannot read {}", path.display());
            return 1;
        };
        let name = path.file_stem().map_or_else(|| path.display().to_string(), |s| s.to_string_lossy().to_string());
        eprintln!("fixpt bench: {name}…");
        match row(&name, &text, &machines, runs, &mut notes) {
            Ok(r) => rows.push(r),
            Err(e) => {
                eprintln!("fixpt bench: {name}: {e}");
                return 1;
            }
        }
    }
    let mut header = vec!["program".to_string(), "answer".to_string()];
    header.extend(machines.iter().map(|m| m.to_string()));
    print_table(&header, &rows);
    println!("\nbest of {runs} run(s), in milliseconds; the answer is the lowered program's.");
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
    let (answer, t_lowered) = best(runs, || {
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        s.scheme.engine.set_step_limit(None);
        match s.run_program(text) {
            Ok(Ok(v)) => v,
            Ok(Err(e)) => format!("!! {e}"),
            Err(e) => format!("!! {}", e.message),
        }
    });
    if answer.starts_with("!! ") {
        return Err(answer[3..].to_string());
    }
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
    for m in machines {
        let got = match *m {
            "lowered" => Some((answer.clone(), t_lowered)),
            "rust" => on_machine(text, &c, &tops, runs, fixpt_engine::cellular::run_word, false),
            "hand" => on_machine(text, &c, &tops, runs, fixpt_native::cellular::run_word_as_is, false),
            "stencils" => on_machine(text, &c, &tops, runs, fixpt_native::stencil::run_word, false),
            "compiled" => on_machine(text, &c, &tops, runs, fixpt_native::cellular::run_word_compiled, false),
            "registers" => on_machine(text, &c, &tops, runs, fixpt_native::cellular::run_word_registers, true),
            _ => in_native_convention(text, runs),
        };
        out.push(cell(m, got));
    }
    Ok(out)
}

fn checked(text: &str) -> Result<(Checker, Vec<Top>), String> {
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

/// The program compiled by the Rust compiler to cellular words (with
/// register code, if asked), in a session of its own, and run by `run`.
fn on_machine(text: &str, c: &Checker, tops: &[Top], runs: usize, run: Run, registers: bool) -> Option<(String, f64)> {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).ok()?;
    s.scheme.engine.set_step_limit(None);
    s.scheme.scope(|sc| {
        let w = sc.make(|m| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), c, text);
            comp.registers = registers;
            comp.program(tops).unwrap_or(Value::FALSE)
        });
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

/// A program whose last line calls a procedure on integers, that procedure
/// compiled in the native convention (`fixpt_native::direct`) and called
/// so: what it gave, and the best time; or nothing, if it is declined.
fn in_native_convention(text: &str, runs: usize) -> Option<(String, f64)> {
    let lines: Vec<&str> = text.trim_end().lines().collect();
    let call = lines.last()?.trim().strip_prefix('(')?.strip_suffix(')')?;
    let mut parts = call.split_whitespace();
    let name = parts.next()?;
    let args: Vec<Value> = parts.map(|a| a.parse().ok().map(Value::fixnum)).collect::<Option<_>>()?;
    let defs = format!("{}\n{name}", lines[..lines.len() - 1].join("\n"));
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
        Some(best(runs, || m.call(rt, p, &args, u64::MAX >> 1).map(|v| fixpt_runtime::write_value(&rt.heap, v)).unwrap_or_else(|t| format!("!! {}", t.what))))
    })
}

/// The rows under the header, each column as wide as its widest cell:
/// names and answers to the left, times to the right.
fn print_table(header: &[String], rows: &[Vec<String>]) {
    let width = |i: usize| rows.iter().map(|r| r[i].chars().count()).chain([header[i].chars().count()]).max().unwrap_or(0);
    let widths: Vec<usize> = (0..header.len()).map(width).collect();
    let line = |cells: &[String]| {
        let shown: Vec<String> = cells
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let pad = " ".repeat(widths[i] - c.chars().count());
                if i < 2 { format!("{c}{pad}") } else { format!("{pad}{c}") }
            })
            .collect();
        println!("| {} |", shown.join(" | "));
    };
    line(header);
    println!("|{}|", widths.iter().enumerate().map(|(i, w)| if i < 2 { format!(" {} ", "-".repeat(*w)) } else { format!(" {}:", "-".repeat(*w)) }).collect::<Vec<_>>().join("|"));
    for r in rows {
        line(r);
    }
}
