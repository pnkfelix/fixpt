//! `fixpt` — the command-line driver.
//!
//! Argument parsing is hand-rolled rather than pulled from a crate: the command
//! surface is small and fixed, and a runtime whose whole point is a
//! self-contained, dumpable image is better off with a dependency list this
//! short.

mod fx91;
mod image_run;

use fixpt_engine::Backend;
use fixpt_heap::image;
use fixpt_scheme::Session;
use std::io::{BufRead, Write};

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
  --dialect scheme|fx91          source language (default: scheme)
  --engine bytecode|ast          execution engine (default: bytecode)
  --main NAME                    an image's entry point (default: main)

`--dialect fx91` selects the FX-91 language, not merely its reader: a form is
type- and effect-checked, lowered to Scheme and run on the same engine, and the
REPL shows the inferred type and effect above each value. FX-87 is not wired up
yet.

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
    let code = run(&args);
    std::process::exit(code);
}

fn run(args: &[String]) -> i32 {
    let (flags, rest) = split_flags(args);
    // The dialect picks a *language*, which is a front end, not just a set of
    // lexical rules: FX-91 forms go through the checker and the code generator
    // before any of this runs them.
    let dialect = match flags.dialect.as_deref() {
        None | Some("scheme") => Dialect::Scheme,
        Some("fx91") => Dialect::Fx91,
        Some("fx87") => {
            eprintln!(
                "fixpt: the FX-87 front end is not implemented yet (M6); \
                 `--dialect fx91` and the default Scheme both work"
            );
            return 2;
        }
        Some(name) => {
            eprintln!("fixpt: unknown dialect `{name}` (want scheme or fx91)");
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

    match rest.first().map(String::as_str) {
        None | Some("help") | Some("-h") | Some("--help") => {
            print!("{USAGE}");
            0
        }
        Some("repl") => match dialect {
            Dialect::Scheme => repl(profile, backend),
            Dialect::Fx91 => fx91::repl(backend),
        },
        Some("run") => {
            if rest.len() < 2 {
                eprintln!("fixpt run: needs at least one file");
                return 2;
            }
            match dialect {
                Dialect::Fx91 => fx91::run_files(backend, &rest[1..]),
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
            if dialect == Dialect::Fx91 {
                return fx91::eval(backend, &rest[1..].join(" "));
            }
            let mut session = Session::with_backend(backend);
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
    Fx91,
}

struct Flags {
    dialect: Option<String>,
    engine: Option<String>,
    out: Option<String>,
    main: Option<String>,
}

fn split_flags(args: &[String]) -> (Flags, Vec<String>) {
    let mut flags = Flags {
        dialect: None,
        engine: None,
        out: None,
        main: None,
    };
    let mut rest = Vec::new();
    let mut i = 0;
    // Each flag takes a value, spelled either `--flag v` or `--flag=v`.
    type Setter = fn(&mut Flags, String);
    let named: [(&str, Setter); 4] = [
        ("--dialect", |f, v| f.dialect = Some(v)),
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

fn repl(profile: fixpt_read::SyntaxProfile, backend: Backend) -> i32 {
    let mut session = Session::with_backend(backend);
    session.profile = profile;
    let engine = match backend {
        Backend::Ast => "AST engine",
        Backend::Bytecode => "bytecode engine",
    };
    println!(
        "fixpt {} — {} reader, {engine}",
        env!("CARGO_PKG_VERSION"),
        profile.name
    );
    println!("(type an expression, or ^D to leave)");

    let stdin = std::io::stdin();
    let mut pending = String::new();
    loop {
        let prompt = if pending.is_empty() { "> " } else { "| " };
        print!("{prompt}");
        let _ = std::io::stdout().flush();
        let mut line = String::new();
        match stdin.lock().read_line(&mut line) {
            Ok(0) => {
                println!();
                return 0;
            }
            Ok(_) => {}
            Err(e) => {
                eprintln!("fixpt: {e}");
                return 1;
            }
        }
        pending.push_str(&line);
        // Keep reading while the input is obviously incomplete, so a
        // multi-line definition can be pasted or typed out.
        if !balanced(&pending) {
            continue;
        }
        let text = std::mem::take(&mut pending);
        if text.trim().is_empty() {
            continue;
        }
        match session.eval_to_string("<repl>", &text) {
            Ok(v) => println!("{v}"),
            Err(e) => eprintln!("{e}"),
        }
    }
}

/// A cheap completeness test: are the delimiters balanced outside strings and
/// comments? Wrong only for inputs that are already syntax errors, which the
/// reader will report anyway.
pub fn balanced(text: &str) -> bool {
    let mut depth: i32 = 0;
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            ';' => {
                for c in chars.by_ref() {
                    if c == '\n' {
                        break;
                    }
                }
            }
            '"' => {
                while let Some(c) = chars.next() {
                    match c {
                        '\\' => {
                            chars.next();
                        }
                        '"' => break,
                        _ => {}
                    }
                }
            }
            '#' if chars.peek() == Some(&'\\') => {
                chars.next();
                chars.next();
            }
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            _ => {}
        }
    }
    depth <= 0
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
