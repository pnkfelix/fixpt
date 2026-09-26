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
    let file = session.scheme.sources().add(name, text);
    let mut interner = std::mem::take(&mut session.checker.p.interner);
    let result = Reader::new(text, file, SyntaxProfile::FX91, &mut interner).read_all();
    session.checker.p.interner = interner;
    result.map_err(|e| format!("{}: {}", session.scheme.sources().describe(e.span), e.message))
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
        let line = {
            let mut oracle = Oracle { session: &mut session };
            reader.read_with("fx91> ", "    | ", &mut oracle, "")
        };
        let text = match line {
            Line::Eof => {
                reader.save();
                return 0;
            }
            Line::Interrupted => continue,
            Line::Form(text) => text,
            // Only the eager reader asks mid-form, and this dialect re-reads
            // with the Rust one.
            Line::Ask { .. } => continue,
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

/// Names FX-91 knows, for completion and for not colouring as unbound: what
/// the initial environment binds — `fx` and every identifier of its module,
/// values and descriptions alike — and the reserved words.
///
/// Taken from the environment's own index of source names, not from the
/// checker's symbol table, which also holds unification variables (named by
/// their alpha numbers) and every name ever read, typos included.
fn known_names(session: &Fx91Session) -> Vec<String> {
    let p = &session.checker.p;
    let mut names: Vec<String> = p
        .arena
        .alpha_names(p.init_alpha)
        .into_iter()
        .chain(p.keywords())
        .map(|s| p.interner.name(s).to_string())
        .collect();
    names.sort();
    names.dedup();
    names
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
/// `,fits` and `,returns` are not offered yet. The environment *can* be
/// enumerated by source name — the initial alpha frame is exactly that index
/// (`Arena::alpha_names`) — so what is missing is the search itself: matching
/// each binding's type against the one asked about, under FX-91's inference
/// rather than FX-87's subtyping. Saying so beats returning nothing.
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
        let file = self.scheme.sources().add("<help>", name);
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
/// cannot yet do is the second half, listing what produces such a value. The
/// names are enumerable (`Arena::alpha_names`); the matching of each one's
/// result type against the hole, under FX-91's inference, is not built. The
/// two halves are genuinely different questions and only the second is
/// missing, so only the second is declined.
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
    match hole_want(session, items, at) {
        Err(()) => vec![format!("; cannot work out the type of {}", render(session, &items[0]))],
        Ok(Some(want)) => vec![
            format!("; the hole wants: {want}"),
            "; (FX-91 cannot yet list what produces one — `--dialect fx87` can)".into(),
        ],
        Ok(None) => vec![format!(
            "; {} takes no argument in that position",
            render(session, &items[0])
        )],
    }
}

/// What argument `at` of the application `items` must be, rendered: `Err`
/// when the operator does not check, `Ok(None)` when it takes no argument
/// there.
fn hole_want(session: &mut Fx91Session, items: &[Syntax], at: usize) -> Result<Option<String>, ()> {
    session.checker.reset();
    let alpha = session.checker.p.init_alpha;
    let node = session.checker.p.parse_exp(alpha, &items[0]).map_err(|_| ())?;
    let ty = session.checker.type_of_exp(node).map_err(|_| ())?;
    Ok(session.checker.argument_type(ty, at - 1).map(|w| session.checker.render_dexp(w)))
}

// ------------------------------------------------ checking while typing

/// The FX-91 REPL's oracle: as FX-87's (`fx87::Oracle`), over FX-91's
/// inference instead of FX-87's checking.
struct Oracle<'a> {
    session: &'a mut Fx91Session,
}

impl crate::lineedit::Oracle for Oracle<'_> {
    fn status(&mut self, text: &str, at_enter: bool) -> crate::lineedit::Status {
        crate::lineedit::Reread(SyntaxProfile::FX91).status(text, at_enter)
    }

    fn notes(&mut self, text: &str) -> Vec<crate::lineedit::Note> {
        let Some(p) = crate::speculate::partial(text, SyntaxProfile::FX91) else {
            return Vec::new();
        };
        let mark = self.session.checker.p.interner.len();
        let notes = speculative_notes(self.session, text, &p);
        self.session.checker.p.interner.truncate(mark);
        notes
    }
}

fn speculative_notes(
    session: &mut Fx91Session,
    text: &str,
    p: &crate::speculate::Partial,
) -> Vec<crate::lineedit::Note> {
    use crate::lineedit::Note;
    let Some(forms) = read_quietly(session, &p.closed) else { return Vec::new() };
    for form in &forms {
        session.checker.reset();
        let alpha = session.checker.p.init_alpha;
        let checked = session
            .checker
            .p
            .parse_exp(alpha, form)
            .and_then(|node| session.checker.type_effect_of_exp(node).map(|_| ()));
        if let Err(e) = checked {
            let (start, end) = (e.span.start as usize, e.span.end as usize);
            if p.finished(text) || p.believe(start, end) {
                return vec![Note { span: char_span(text, start, end), message: e.message, error: true }];
            }
        }
    }
    let hint = p.hole_form.as_ref().and_then(|h| {
        let form = read_quietly(session, h)?.into_iter().next()?;
        let names = |s: fixpt_read::Sym| session.checker.p.interner.name(s).to_string();
        let Datum::List { items, tail: None } = &form.datum else { return None };
        let at = items.iter().position(|i| crate::help::mentions_hole(i, &names))?;
        let items = items.clone();
        let want = hole_want(session, &items, at).ok()??;
        let op = render(session, &items[0]);
        Some(format!("argument {at} of {op} wants {want}"))
    });
    hint.map(|message| vec![Note { span: None, message, error: false }]).unwrap_or_default()
}

/// Read without recording a source or reporting anything.
fn read_quietly(session: &mut Fx91Session, text: &str) -> Option<Vec<Syntax>> {
    let mut interner = std::mem::take(&mut session.checker.p.interner);
    let result = Reader::new(text, fixpt_read::FileId(0), SyntaxProfile::FX91, &mut interner).read_all();
    session.checker.p.interner = interner;
    result.ok()
}

fn char_span(text: &str, start: usize, end: usize) -> Option<(usize, usize)> {
    if start >= end || end > text.len() {
        return None;
    }
    Some((text[..start].chars().count(), text[..end].chars().count()))
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


#[cfg(test)]
mod speculative {
    use super::*;
    use crate::lineedit::{Note, Oracle as _};

    fn notes(text: &str) -> Vec<Note> {
        let mut session = Fx91Session::with_backend(Backend::Ast).expect("starts");
        let before = session.checker.p.interner.len();
        let notes = Oracle { session: &mut session }.notes(text);
        assert_eq!(session.checker.p.interner.len(), before, "checking left symbols behind");
        notes
    }

    #[test]
    fn an_error_in_a_finished_subform_is_reported_while_typing() {
        let n = notes("(+ 1 (car 5) ");
        assert_eq!(n.len(), 1, "{n:?}");
        assert!(n[0].error);
        assert_eq!(n[0].span, Some((5, 12)), "{n:?}");
    }

    #[test]
    fn what_closing_off_would_break_is_not_reported() {
        for text in ["(if", "(if #t", "(+ 1", "(car"] {
            assert!(notes(text).iter().all(|n| !n.error), "{text:?}: {:?}", notes(text));
        }
    }

    #[test]
    fn a_name_nothing_binds_is_reported_once_it_is_finished() {
        assert!(notes("(+ 1 nosuchname").iter().all(|n| !n.error), "still being typed");
        let n = notes("(+ 1 nosuchname ");
        assert!(n.first().is_some_and(|n| n.error), "{n:?}");
    }

    #[test]
    fn a_finished_form_is_judged_whole() {
        let n = notes("(+ 1 \"s\")");
        assert!(n.first().is_some_and(|n| n.error), "{n:?}");
        assert!(notes("(+ 1 2)").is_empty());
    }

    #[test]
    #[ignore = "prints what the notes say, for a person to read"]
    fn show_notes() {
        for t in ["(+ 1 (car 5) ", "(+ 1 nosuchname ", "(+ 1 \"s\")", "(vector-ref (make-vector 3 0) ", "(vector-ref (make-vector 3 0) 1"] {
            println!("{t:<34} => {:?}", notes(t));
        }
    }

    #[test]
    fn the_argument_at_the_cursor_is_described() {
        let n = notes("(vector-ref (make-vector 3 0) ");
        assert_eq!(n.len(), 1, "{n:?}");
        assert!(!n[0].error);
        assert!(n[0].message.contains("argument 2 of vector-ref wants"), "{n:?}");
        assert!(n[0].message.contains("int"), "{n:?}");
    }
}


#[cfg(test)]
mod completion {
    use super::*;

    #[test]
    fn known_names_are_what_is_bound_and_what_is_reserved() {
        let mut session = Fx91Session::with_backend(Backend::Ast).expect("starts");
        // Leave a typo and some unification variables behind.
        let forms = read(&mut session, "<t>", "(car nosuchname) (lambda (x) x)").expect("reads");
        for f in &forms {
            let _ = session.run(f);
        }
        let names = known_names(&session);
        for want in ["+", "car", "fx", "lambda", "with", "module"] {
            assert!(names.iter().any(|n| n == want), "missing {want:?}");
        }
        assert!(!names.iter().any(|n| n == "nosuchname"), "a typo became a completion");
        assert!(!names.iter().any(|n| n.chars().all(|c| c.is_ascii_digit())), "a numbered name leaked");
    }
}
