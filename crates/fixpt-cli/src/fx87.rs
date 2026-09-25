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
use fixpt_read::{Datum, Reader, Syntax, SyntaxProfile};

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
    println!("(every type is written down and checked. `,help` for commands,");
    println!(" `,code` to show the erased Scheme. ^D leaves.)");

    let mut reader = LineReader::new(".fixpt_fx87_history", SyntaxProfile::FX87);
    let mut show_code = false;
    let mut n = 0usize;
    loop {
        reader.set_completions(known_names(&session));
        let line = {
            let mut oracle = Oracle { session: &mut session };
            reader.read_with("fx87> ", "     | ", &mut oracle, "")
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
            // A `,help` written inside the form asks about the hole rather
            // than about the whole expression.
            if let Some(lines) = answer_hole(&mut session, form) {
                for l in lines {
                    println!("{l}");
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

/// Names FX-87 knows, for completion and for not colouring as unbound: what
/// the environment binds, as values and as descriptions, and the reserved
/// words. Taken from the environment rather than from the checker's symbol
/// table, which also holds every name ever read — type variables named by
/// number, typos from forms already submitted — and would need filtering to
/// be any use.
fn known_names(session: &Fx87Session) -> Vec<String> {
    let c = &session.checker;
    let mut names: Vec<String> = c
        .env
        .value_names()
        .chain(c.env.desc_names())
        .chain(c.p.syms.all())
        .map(|s| c.p.interner.name(s).to_string())
        .filter(|n| !n.starts_with('%'))
        .collect();
    names.sort();
    names.dedup();
    names
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

// ------------------------------------------------------------------- help

/// FX-87 can answer the interesting questions, because its standard
/// environment carries a type for all 190 of its bindings — generated from the
/// 1987 sources, not transcribed — and subtyping decides what fits what.
impl crate::help::Helpful for Fx87Session {
    fn dialect(&self) -> &'static str {
        "FX-87"
    }

    fn typed(&self) -> bool {
        true
    }

    fn holes(&self) -> bool {
        true
    }

    fn describe(&mut self, name: &str) -> Vec<String> {
        let Some(sym) = self.checker.p.interner.get(name) else { return Vec::new() };
        match self.checker.describe(sym) {
            Some((ty, region)) => {
                let mut out = vec![format!("{name} : {ty}")];
                // The region is why `(set! + -)` is a type error, so it is
                // worth saying rather than hiding.
                out.push(format!("  bound in region {region}{}", immutability(&region)));
                out
            }
            None => Vec::new(),
        }
    }

    fn apropos(&mut self, pattern: &str) -> Vec<String> {
        let names: Vec<_> = self.checker.env.value_names().collect();
        let mut out = Vec::new();
        for sym in names {
            let name = self.checker.p.interner.name(sym).to_string();
            if !name.contains(pattern) {
                continue;
            }
            if let Some((ty, _)) = self.checker.describe(sym) {
                out.push(format!("{name} : {ty}"));
            }
        }
        out.sort();
        out
    }

    fn fits(&mut self, type_text: &str) -> Option<Vec<String>> {
        let ty = read_type(self, type_text)?;
        let found = self.checker.accepting(ty, 0);
        Some(render(self, found))
    }

    fn returns(&mut self, type_text: &str) -> Option<Vec<String>> {
        let ty = read_type(self, type_text)?;
        let found = self.checker.returning(ty);
        Some(render(self, found))
    }
}

fn immutability(region: &str) -> &'static str {
    if region == "@=" { " (immutable, so it cannot be assigned)" } else { "" }
}

/// Read a type written at the prompt.
///
/// Free functions rather than inherent methods: `Fx87Session` belongs to
/// another crate, so this one cannot add to it.
fn read_type(s: &mut Fx87Session, text: &str) -> Option<fixpt_fx87::DescId> {
    let unused = |_: &mut Fx87Session| ();
    let _ = unused;
    {
        let self_ = s;
        let file = self_.scheme.rt.sources.add("<help>", text);
        let mut interner = std::mem::take(&mut self_.checker.p.interner);
        let forms = Reader::new(text, file, SyntaxProfile::FX87, &mut interner).read_all();
        self_.checker.p.interner = interner;
        let forms = forms.ok()?;
        let first = forms.first()?;
        self_.checker.p.parse_desc(first, &Default::default()).ok()
    }
}

/// Specific answers first; the ones that would match any question are counted
/// rather than listed, since they are true and unhelpful.
fn render(s: &Fx87Session, found: Vec<fixpt_fx87::check::Found>) -> Vec<String> {
    let line = |f: fixpt_fx87::check::Found| {
        format!(
            "{} : {}",
            s.checker.p.interner.name(f.name),
            fixpt_fx87::unparse::unparse(&s.checker.p.arena, &s.checker.p.interner, f.ty)
        )
    };
    let (generic, specific): (Vec<_>, Vec<_>) = found.iter().partition(|f| f.generic);
    let mut out: Vec<String> = specific.iter().copied().map(line).collect();
    if !generic.is_empty() {
        let names: Vec<&str> =
            generic.iter().map(|f| s.checker.p.interner.name(f.name)).collect();
        out.push(format!(
            "({} more that fit anything: {})",
            generic.len(),
            names.join(" ")
        ));
    }
    out
}

// ----------------------------------------------- help inside an expression

/// A `,help` written *inside* a form, asking what belongs there.
///
/// ```text
/// fx87> (vector-ref (make-vector 3 0) ,help)
/// ; the hole wants: int
/// ```
///
/// This is the contextual version of `,fits`, and the difference matters: the
/// hole is not "anything at all", it is one particular argument of one
/// particular subroutine, and the arguments already written have often pinned
/// down what the rest must be. The checker answers that question directly —
/// see [`Checker::expected_argument`].
///
/// The marker is `(unquote help)`, which is what `,help` reads as. That costs
/// nothing in the reader and collides only with someone writing `,help` inside
/// a quasiquote, which FX-87 does not have.
fn hole_position(session: &Fx87Session, form: &Syntax) -> Option<(Vec<Syntax>, usize)> {
    let Datum::List { items, tail: None } = &form.datum else { return None };
    let is_hole = |s: &Syntax| match &s.datum {
        Datum::List { items, tail: None } if items.len() == 2 => {
            matches!((&items[0].datum, &items[1].datum),
                (Datum::Symbol(u), Datum::Symbol(h))
                    if session.checker.p.interner.name(*u) == "unquote"
                        && matches!(session.checker.p.interner.name(*h), "help" | "?"))
        }
        _ => false,
    };
    let at = items.iter().position(is_hole)?;
    Some((items.clone(), at))
}

/// Answer a hole, or `None` if this form has none.
fn answer_hole(session: &mut Fx87Session, form: &Syntax) -> Option<Vec<String>> {
    let (items, at) = hole_position(session, form)?;
    if at == 0 {
        // `(,help x y)` — the hole is the operator. What takes these?
        let Some(first) = items.get(1) else {
            return Some(vec!["; a hole in operator position needs an argument to go on".into()]);
        };
        let ty = type_of(session, first)?;
        let found = session.checker.accepting(ty, 0);
        let mut out = vec![format!("; the hole is applied to a {}", show(session, ty))];
        out.extend(render(session, found));
        return Some(out);
    }

    // `(f a … ,help … )` — the hole is an argument.
    let want = hole_want(session, &items, at)?;
    let mut out = vec![format!("; the hole wants: {}", show(session, want))];
    let found = session.checker.returning(want);
    let lines = render(session, found);
    if lines.is_empty() {
        out.push("(nothing in the environment produces one)".into());
    } else {
        out.push("; what produces one:".into());
        out.extend(lines);
    }
    out.extend(dynamic_hole(session, &items, at));
    Some(out)
}

/// What the run says is around the hole.
///
/// The static half above answers from types; this one answers from values, and
/// the two are worth having together — a type says `int` where a value says
/// `3`, and only the value shows that the vector really does have three slots.
///
/// An argument is evaluated only when the checker calls it pure. That is not a
/// new rule invented for the REPL: `purify` already treats an effect confined
/// to a private region as no effect, which is exactly the question — can
/// anything outside tell that this ran early?
fn dynamic_hole(session: &mut Fx87Session, items: &[Syntax], at: usize) -> Vec<String> {
    let mut out = vec![format!("; at the hole — argument {at} of {}:", items.len() - 1)];
    for (i, arg) in items[..at].iter().enumerate() {
        let what = if i == 0 { "the operator".to_string() } else { format!("argument {i}") };
        let src = fixpt_read::write_syntax(arg, &session.checker.p.interner);
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

/// What the argument at `at` of the application `items` must be — given the
/// operator's type and whatever the other arguments already pin down.
fn hole_want(session: &mut Fx87Session, items: &[Syntax], at: usize) -> Option<fixpt_fx87::DescId> {
    let fun_ty = type_of(session, &items[0])?;
    let mut known = Vec::new();
    for (i, arg) in items.iter().enumerate().skip(1) {
        if i == at {
            continue;
        }
        if let Some(t) = type_of(session, arg) {
            known.push((i - 1, t));
        }
    }
    session.checker.expected_argument(fun_ty, &known, at - 1)
}

// ------------------------------------------------ checking while typing

/// The FX-87 REPL's oracle: the Rust reader decides what `Enter` does, and the
/// checker comments on the form as it is typed — see [`crate::speculate`].
struct Oracle<'a> {
    session: &'a mut Fx87Session,
}

impl crate::lineedit::Oracle for Oracle<'_> {
    fn status(&mut self, text: &str, at_enter: bool) -> crate::lineedit::Status {
        crate::lineedit::Reread(SyntaxProfile::FX87).status(text, at_enter)
    }

    fn notes(&mut self, text: &str) -> Vec<crate::lineedit::Note> {
        let Some(p) = crate::speculate::partial(text, SyntaxProfile::FX87) else {
            return Vec::new();
        };
        // Leave no trace: symbols read here are forgotten afterwards, so a
        // typo never turns up as a completion.
        let mark = self.session.checker.p.interner.len();
        let notes = speculative_notes(self.session, text, &p);
        self.session.checker.p.interner.truncate(mark);
        notes
    }
}

fn speculative_notes(
    session: &mut Fx87Session,
    text: &str,
    p: &crate::speculate::Partial,
) -> Vec<crate::lineedit::Note> {
    use crate::lineedit::Note;
    let Some(forms) = read_quietly(session, &p.closed) else { return Vec::new() };
    for form in &forms {
        let env = session.checker.env.clone();
        let checked = session
            .checker
            .p
            .parse_exp(form, &Default::default())
            .and_then(|e| session.checker.check(e, &env));
        if let Err(e) = checked {
            // A finished text's errors are all about what was typed; an
            // unfinished one's only when they lie inside a finished subform.
            let (start, end) = (e.span.start as usize, e.span.end as usize);
            if p.finished(text) || p.believe(start, end) {
                return vec![Note { span: char_span(text, start, end), message: e.message, error: true }];
            }
        }
    }
    // Nothing wrong with what is finished: say what the argument at the
    // cursor should be.
    let hint = p.hole_form.as_ref().and_then(|h| {
        let form = read_quietly(session, h)?.into_iter().next()?;
        let (items, at) = hole_position(session, &form)?;
        let want = hole_want(session, &items, at)?;
        let op = fixpt_read::write_syntax(&items[0], &session.checker.p.interner);
        Some(format!("argument {at} of {op} wants {}", show(session, want)))
    });
    hint.map(|message| vec![Note { span: None, message, error: false }]).unwrap_or_default()
}

/// Read without recording a source or reporting anything.
fn read_quietly(session: &mut Fx87Session, text: &str) -> Option<Vec<Syntax>> {
    let mut interner = std::mem::take(&mut session.checker.p.interner);
    let result = Reader::new(text, fixpt_read::FileId(0), SyntaxProfile::FX87, &mut interner).read_all();
    session.checker.p.interner = interner;
    result.ok()
}

/// A byte span of `text` as characters, if it is a real one.
fn char_span(text: &str, start: usize, end: usize) -> Option<(usize, usize)> {
    if start >= end || end > text.len() {
        return None;
    }
    Some((text[..start].chars().count(), text[..end].chars().count()))
}

/// The type of one subexpression, or `None` if it does not check.
fn type_of(session: &mut Fx87Session, form: &Syntax) -> Option<fixpt_fx87::DescId> {
    let env = session.checker.env.clone();
    let exp = session.checker.p.parse_exp(form, &Default::default()).ok()?;
    session.checker.check(exp, &env).ok().map(|d| d.ty)
}

fn show(session: &Fx87Session, ty: fixpt_fx87::DescId) -> String {
    fixpt_fx87::unparse::unparse(&session.checker.p.arena, &session.checker.p.interner, ty)
}


#[cfg(test)]
mod speculative {
    use super::*;
    use crate::lineedit::{Note, Oracle as _};

    fn notes(text: &str) -> Vec<Note> {
        let mut session = Fx87Session::with_backend(Backend::Ast).expect("starts");
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
        let mut session = Fx87Session::with_backend(Backend::Ast).expect("starts");
        // Leave a typo and a type variable behind in the symbol table.
        let forms = read(&mut session, "<t>", "(car nosuchname) (lambda ((x int)) x)").expect("reads");
        for f in &forms {
            let _ = session.run(f);
        }
        let names = known_names(&session);
        for want in ["+", "-", "*", "car", "vector-ref", "int", "pairof", "lambda", "if", "let"] {
            assert!(names.iter().any(|n| n == want), "missing {want:?}");
        }
        assert!(!names.iter().any(|n| n == "nosuchname"), "a typo became a completion");
        assert!(!names.iter().any(|n| n.chars().all(|c| c.is_ascii_digit())), "a numbered name leaked");
    }
}
