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
use fixpt_read::{Datum, Reader, Syntax, SyntaxProfile};

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
    println!(" Scheme; `,help` for commands; ^D leaves.)");

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
        if let Some(ask) = crate::help::parse(&text) {
            crate::help::answer(&mut session, &ask);
            continue;
        }
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
            // A `,help` hole asks what belongs at that position.
            let names = |s: fixpt_read::Sym| session.checker.p.interner.name(s).to_string();
            if crate::help::mentions_hole(form, &names) {
                for line in answer_hole(&mut session, form) {
                    println!("{line}");
                }
                continue;
            }
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
            // A `,help` hole asks what belongs at that position.
            let names = |s: fixpt_read::Sym| session.checker.p.interner.name(s).to_string();
            if crate::help::mentions_hole(form, &names) {
                for line in answer_hole(&mut session, form) {
                    println!("{line}");
                }
                continue;
            }
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

// ------------------------------------------------------------------- help

/// FX-91 answers `,help` by *checking* the name, which is both the simplest
/// implementation and the most honest one: the answer is the type the session
/// would give that expression right now, not a separate description that might
/// have drifted.
///
/// `,fits` and `,returns` are not offered. FX-91's environment is keyed by
/// alpha-renamed variables rather than by source names, so enumerating it takes
/// more than a lookup — the same search FX-87 supports is possible here and is
/// simply not built yet. Saying so beats returning nothing.
impl crate::help::Helpful for Fx91Session {
    fn dialect(&self) -> &'static str {
        "FX-91"
    }

    /// Holes work, though only the first half of the answer: FX-91 can say
    /// what a position wants, not yet what produces one.
    fn holes(&self) -> bool {
        true
    }

    fn describe(&mut self, name: &str) -> Vec<String> {
        let file = self.scheme.rt.sources.add("<help>", name);
        let mut interner = std::mem::take(&mut self.checker.p.interner);
        let read = Reader::new(name, file, SyntaxProfile::FX91, &mut interner).read_all();
        self.checker.p.interner = interner;
        let Ok(forms) = read else { return Vec::new() };
        let Some(form) = forms.first() else { return Vec::new() };
        match self.run(form) {
            Ok(o) => vec![format!("{name} : {} ! {}", o.ty, o.effect)],
            Err(_) => Vec::new(),
        }
    }

    fn apropos(&mut self, pattern: &str) -> Vec<String> {
        let mut out: Vec<String> = self
            .checker
            .p
            .interner
            .names()
            .filter(|n| n.contains(pattern) && !n.contains('*') && !n.starts_with('%'))
            .map(str::to_string)
            .collect();
        out.sort();
        out.dedup();
        out
    }
}


// ----------------------------------------------- help inside an expression

/// `,help` written inside a form, asking what belongs there.
///
/// FX-91 can say *what the hole wants*, because that needs only the operator's
/// type — peel the `poly` binders, take the formal at that position. What it
/// cannot yet do is the second half, listing what produces such a value: that
/// needs the environment enumerated by source name, and FX-91's is keyed by
/// alpha-renamed variables. The two halves are genuinely different questions
/// and only the second is blocked, so only the second is declined.
fn answer_hole(session: &mut Fx91Session, form: &Syntax) -> Vec<String> {
    let names = |s: fixpt_read::Sym| session.checker.p.interner.name(s).to_string();
    let Datum::List { items, tail: None } = &form.datum else {
        return vec!["; a hole makes sense inside an application".into()];
    };
    let Some(at) = items.iter().position(|i| crate::help::mentions_hole(i, &names)) else {
        return vec!["; no hole found".into()];
    };
    let items = items.clone();
    let mut out = Vec::new();
    out.extend(static_hole(session, &items, at));
    out.extend(dynamic_hole(session, &items, at));
    out
}

/// What the types say belongs in the hole.
fn static_hole(session: &mut Fx91Session, items: &[Syntax], at: usize) -> Vec<String> {
    if at == 0 {
        return vec![
            "; FX-91 cannot yet search for an operator by argument type — \
             `--dialect fx87` can"
                .into(),
        ];
    }
    session.checker.reset();
    let alpha = session.checker.p.init_alpha;
    let Ok(node) = session.checker.p.parse_exp(alpha, &items[0]) else {
        return vec![format!("; cannot work out the type of {}", render(session, &items[0]))];
    };
    let Ok(ty) = session.checker.type_of_exp(node) else {
        return vec![format!("; cannot work out the type of {}", render(session, &items[0]))];
    };
    match session.checker.argument_type(ty, at - 1) {
        Some(want) => vec![
            format!("; the hole wants: {}", session.checker.render_dexp(want)),
            "; (FX-91 cannot yet list what produces one — `--dialect fx87` can)".into(),
        ],
        None => vec![format!(
            "; {} takes no argument in that position",
            render(session, &items[0])
        )],
    }
}

/// What the run says is around the hole.
///
/// The operator and the arguments before the hole are evaluated and shown, so
/// the answer is made of values rather than of types. FX pays for this: an
/// argument is only evaluated when its **inferred effect is `pure`**, because
/// evaluating something the user did not ask to evaluate is defensible exactly
/// when the effect system guarantees no one can tell. An impure argument is
/// reported with the effect that stopped it — which is itself worth knowing,
/// since it says what will happen when the form is finally run.
fn dynamic_hole(session: &mut Fx91Session, items: &[Syntax], at: usize) -> Vec<String> {
    let mut out = vec![format!("; at the hole — argument {at} of {}:", items.len() - 1)];
    for (i, arg) in items[..at].iter().enumerate() {
        let what = if i == 0 { "the operator".to_string() } else { format!("argument {i}") };
        let src = render(session, arg);
        let checked = match session.check(arg) {
            Ok(c) => c,
            Err(e) => {
                out.push(format!("  {what} {src} does not check: {e}"));
                continue;
            }
        };
        if !checked.safe {
            out.push(format!(
                "  {what} {src} not evaluated — its effect is {}",
                checked.effect
            ));
            continue;
        }
        match session.run_code(&checked.code) {
            Ok(v) => out.push(format!("  {what} {src} = {v}")),
            Err(e) => out.push(format!("  {what} {src} fails: {e}")),
        }
    }
    out
}

fn render(session: &Fx91Session, form: &Syntax) -> String {
    fixpt_read::write_syntax(form, &session.checker.p.interner)
}
