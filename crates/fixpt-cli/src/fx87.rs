//! The FX-87 language at the command line.
//!
//! Like FX-91, FX-87 is a front end onto the same Core IR and the same engines,
//! so `--dialect fx87` selects a *language* rather than a set of lexical rules:
//! a form is type- and effect-checked, erased to Scheme, and run.
//!
//! The REPL prints what the 1987 top level printed. `show-type-and-effect`
//! emits ` : <type> ! <effect>` after the value, on one line — which is not
//! FX-91's layout, and the difference is kept rather than smoothed over.

use crate::lineedit::{Line, LineReader};
use fixpt_engine::Backend;
use fixpt_fx87::session::{Fx87Session, Outcome};
use fixpt_read::{Reader, Syntax, SyntaxProfile};

/// Read FX-87 source into forms, using the checker's own interner.
fn read(session: &mut Fx87Session, name: &str, text: &str) -> Result<Vec<Syntax>, String> {
    let file = session.scheme.rt.sources.add(name, text);
    let mut interner = std::mem::take(&mut session.checker.p.interner);
    let result = Reader::new(text, file, SyntaxProfile::FX87, &mut interner).read_all();
    session.checker.p.interner = interner;
    result.map_err(|e| format!("{}: {}", session.scheme.rt.sources.describe(e.span), e.message))
}

fn start(backend: Backend) -> Result<Fx87Session, i32> {
    match Fx87Session::with_backend(backend) {
        Ok(s) => Ok(s),
        Err(e) => {
            eprintln!("fixpt: the FX-87 environment failed to load: {e}");
            Err(1)
        }
    }
}

/// One result, in the 1987 top level's own layout.
fn report(outcome: &Outcome, printed: &str, show_code: bool) {
    if show_code {
        println!("; {}", outcome.code);
    }
    print!("{printed}");
    match &outcome.value {
        Ok(v) => println!("{v} : {} ! {}", outcome.ty, outcome.effect),
        Err(e) => {
            println!(" : {} ! {}", outcome.ty, outcome.effect);
            eprintln!("! evaluation failed: {e}");
        }
    }
}

pub fn repl(backend: Backend) -> i32 {
    let mut session = match start(backend) {
        Ok(s) => s,
        Err(code) => return code,
    };
    let engine = match backend {
        Backend::Ast => "AST engine",
        Backend::Bytecode => "bytecode engine",
    };
    println!("fixpt {} — FX-87, {engine}", env!("CARGO_PKG_VERSION"));
    println!("(every type is written down and checked; `,code` shows the erased");
    println!(" Scheme, with the metadata the checker proved. ^D leaves.)");

    let mut reader = LineReader::new(".fixpt_fx87_history", SyntaxProfile::FX87);
    let mut show_code = false;
    let mut n = 0usize;
    loop {
        reader.set_completions(known_names(&session));
        let text = match reader.read("fx87> ", "     | ") {
            Line::Eof => {
                reader.save();
                return 0;
            }
            Line::Interrupted => continue,
            Line::Form(text) => text,
        };
        match text.trim() {
            "" => continue,
            ",code" => {
                show_code = !show_code;
                println!("; erased Scheme: {}", if show_code { "on" } else { "off" });
                continue;
            }
            ",quit" => {
                reader.save();
                return 0;
            }
            _ => {}
        }
        n += 1;
        let forms = match read(&mut session, &format!("<fx87:{n}>"), &text) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("read error: {e}");
                continue;
            }
        };
        for form in &forms {
            match session.run(form) {
                Ok(outcome) => {
                    let printed = std::mem::take(&mut session.printed);
                    report(&outcome, &printed, show_code);
                }
                Err(e) => eprintln!("{e}"),
            }
        }
    }
}

/// Names FX-87 knows, for completion: everything the standard environment
/// bound, plus whatever the session has parsed.
fn known_names(session: &Fx87Session) -> Vec<String> {
    session
        .checker
        .p
        .interner
        .names()
        .filter(|n| !n.starts_with('%') && n.len() > 1)
        .map(str::to_string)
        .collect()
}

pub fn run_files(backend: Backend, files: &[String]) -> i32 {
    let mut session = match start(backend) {
        Ok(s) => s,
        Err(code) => return code,
    };
    for f in files {
        let text = match std::fs::read_to_string(f) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("fixpt: cannot read {f}: {e}");
                return 1;
            }
        };
        let forms = match read(&mut session, f, &text) {
            Ok(forms) => forms,
            Err(e) => {
                eprintln!("fixpt: read error: {e}");
                return 1;
            }
        };
        for form in &forms {
            match session.run(form) {
                Ok(outcome) => {
                    print!("{}", std::mem::take(&mut session.printed));
                    if let Err(e) = &outcome.value {
                        eprintln!("fixpt: {e}");
                        return 1;
                    }
                }
                Err(e) => {
                    eprintln!("fixpt: {e}");
                    return 1;
                }
            }
        }
    }
    0
}

pub fn eval(backend: Backend, text: &str) -> i32 {
    let mut session = match start(backend) {
        Ok(s) => s,
        Err(code) => return code,
    };
    let forms = match read(&mut session, "<argument>", text) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("fixpt: read error: {e}");
            return 1;
        }
    };
    let mut status = 0;
    for form in &forms {
        match session.run(form) {
            Ok(outcome) => {
                let printed = std::mem::take(&mut session.printed);
                report(&outcome, &printed, false);
                if outcome.value.is_err() {
                    status = 1;
                }
            }
            Err(e) => {
                eprintln!("fixpt: {e}");
                status = 1;
            }
        }
    }
    status
}
