//! The FX-91 language at the command line.
//!
//! FX-91 is a front end onto the same Core IR and the same engines, exactly as
//! `code.scm` was a front end onto Scheme in 1991: a form is parsed, its type
//! and effect are inferred, it is lowered to Scheme, and the Scheme session
//! runs it. So `--dialect fx91` selects a *language*, not just a reader — which
//! is the whole difference between this and reading FX-91 tokens into a Scheme
//! expander that would not know what to do with them.
//!
//! The REPL prints what the reference's top level prints, in its own notation:
//! `:` the inferred type, `!` the inferred effect, `=` the value
//! (`extracted/fx91/top.scm:159`).
//!
//! Like the reference, it is **expression-oriented** and re-checks each form in
//! the initial environment — the original resets `*tk-env*`, `*store*` and the
//! alpha counter on every line. FX-91 has no top-level `define`; a binding is
//! introduced with a module, as `(with (module (define f 3)) f)`. That is the
//! language, not a gap in this driver.

use crate::lineedit::{Line, LineReader};
use fixpt_engine::Backend;
use fixpt_fx91::session::{Fx91Session, Outcome};
use fixpt_read::{Reader, Syntax, SyntaxProfile};

/// Read FX-91 source into forms, using the checker's own interner.
///
/// The checker and the Scheme session intern symbols separately, so the forms
/// have to be read against the checker's table — which is also why lowering
/// goes back out through text before the Scheme session sees it.
fn read(session: &mut Fx91Session, name: &str, text: &str) -> Result<Vec<Syntax>, String> {
    let file = session.scheme.rt.sources.add(name, text);
    let mut interner = std::mem::take(&mut session.checker.p.interner);
    let result = Reader::new(text, file, SyntaxProfile::FX91, &mut interner).read_all();
    session.checker.p.interner = interner;
    result.map_err(|e| format!("{}: {}", session.scheme.rt.sources.describe(e.span), e.message))
}

fn start(backend: Backend) -> Result<Fx91Session, i32> {
    match Fx91Session::with_backend(backend) {
        Ok(s) => Ok(s),
        Err(e) => {
            eprintln!("fixpt: the FX-91 environment failed to load: {e}");
            Err(1)
        }
    }
}

/// One result, in the reference's notation.
fn report(outcome: &Outcome, printed: &str, show_code: bool) {
    if show_code {
        println!("; {}", outcome.code);
    }
    // Whatever the form itself printed comes before its value, as it would
    // have while running.
    print!("{printed}");
    println!(": {}", outcome.ty);
    println!("! {}", outcome.effect);
    match &outcome.value {
        Ok(v) => println!("= {v}"),
        Err(e) => eprintln!("! evaluation failed: {e}"),
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
    println!("fixpt {} — FX-91, {engine}", env!("CARGO_PKG_VERSION"));
    println!("(expressions only, as in the 1991 top level: bind with");
    println!(" `(with (module (define f 3)) f)`. `,code` shows the generated");
    println!(" Scheme; ^D leaves.)");

    let mut reader = LineReader::new(".fixpt_fx91_history", SyntaxProfile::FX91);
    let mut show_code = false;
    let mut n = 0usize;
    loop {
        reader.set_completions(known_names(&session));
        let text = match reader.read("fx91> ", "    | ") {
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
                println!("; generated Scheme: {}", if show_code { "on" } else { "off" });
                continue;
            }
            ",quit" => {
                reader.save();
                return 0;
            }
            _ => {}
        }
        n += 1;
        let forms = match read(&mut session, &format!("<fx91:{n}>"), &text) {
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

/// Names FX-91 knows, for completion.
///
/// The checker's interner holds every name the `fx` module introduced along
/// with anything the session has parsed. Unification variables are filtered
/// out: they are internal and arrive named after their own alpha number.
fn known_names(session: &Fx91Session) -> Vec<String> {
    session
        .checker
        .p
        .interner
        .names()
        .filter(|n| !n.contains('*') && !n.starts_with('%') && n.len() > 1)
        .map(str::to_string)
        .collect()
}

/// Run FX-91 files. Each form is checked and evaluated in turn, and a form's
/// own output goes to stdout rather than being swallowed.
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
        // `(load "…")` inside FX-91 is a *checking*-time inclusion, so it
        // resolves relative to the file that mentions it.
        if let Some(dir) = std::path::Path::new(f).parent()
            && !dir.as_os_str().is_empty()
        {
            session.set_load_base(dir);
        }
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

/// Check and evaluate one expression, printing its type, effect and value.
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
