//! `fixpt` — the command-line driver.
//!
//! Argument parsing is hand-rolled rather than pulled from a crate: the command
//! surface is small and fixed, and a runtime whose whole point is a
//! self-contained, dumpable image is better off with a dependency list this
//! short.

use fixpt_heap::image;
use fixpt_scheme::Session;
use std::io::{BufRead, Write};

const USAGE: &str = "\
fixpt — a Scheme engine with FX-87 and FX-91 front ends

usage:
  fixpt repl                     start a read-eval-print loop
  fixpt run FILE...              run each file in one session
  fixpt eval EXPR                evaluate one expression and print it
  fixpt image info FILE          describe a heap image
  fixpt image verify FILE        load a heap image and check its invariants
  fixpt help                     show this

options:
  --dialect scheme|fx87|fx91     reader syntax (default: scheme)
";

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let code = run(&args);
    std::process::exit(code);
}

fn run(args: &[String]) -> i32 {
    let (flags, rest) = split_flags(args);
    let profile = match flags.dialect.as_deref() {
        None | Some("scheme") => fixpt_read::SyntaxProfile::SCHEME,
        Some(name) => match fixpt_read::SyntaxProfile::by_name(name) {
            Some(p) => p,
            None => {
                eprintln!("fixpt: unknown dialect `{name}`");
                return 2;
            }
        },
    };

    match rest.first().map(String::as_str) {
        None | Some("help") | Some("-h") | Some("--help") => {
            print!("{USAGE}");
            0
        }
        Some("repl") => repl(profile),
        Some("run") => {
            if rest.len() < 2 {
                eprintln!("fixpt run: needs at least one file");
                return 2;
            }
            run_files(profile, &rest[1..])
        }
        Some("eval") => {
            if rest.len() < 2 {
                eprintln!("fixpt eval: needs an expression");
                return 2;
            }
            let mut session = Session::new();
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
        Some("image") => image_command(&rest[1..]),
        Some(other) => {
            eprintln!("fixpt: unknown command `{other}`\n\n{USAGE}");
            2
        }
    }
}

struct Flags {
    dialect: Option<String>,
}

fn split_flags(args: &[String]) -> (Flags, Vec<String>) {
    let mut flags = Flags { dialect: None };
    let mut rest = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--dialect" if i + 1 < args.len() => {
                flags.dialect = Some(args[i + 1].clone());
                i += 2;
            }
            a if a.starts_with("--dialect=") => {
                flags.dialect = Some(a["--dialect=".len()..].to_string());
                i += 1;
            }
            _ => {
                rest.push(args[i].clone());
                i += 1;
            }
        }
    }
    (flags, rest)
}

fn run_files(profile: fixpt_read::SyntaxProfile, files: &[String]) -> i32 {
    let mut session = Session::new();
    session.profile = profile;
    for f in files {
        let text = match std::fs::read_to_string(f) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("fixpt: cannot read {f}: {e}");
                return 1;
            }
        };
        if let Err(e) = session.eval_str(f, &text) {
            eprintln!("fixpt: {e}");
            return 1;
        }
    }
    0
}

fn repl(profile: fixpt_read::SyntaxProfile) -> i32 {
    let mut session = Session::new();
    session.profile = profile;
    println!("fixpt {} — {} reader, AST engine", env!("CARGO_PKG_VERSION"), profile.name);
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
fn balanced(text: &str) -> bool {
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
                        println!("  embedded in an executable of {} bytes", bytes.len() - img.len());
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
