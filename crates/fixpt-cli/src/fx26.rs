//! FX-26 at the command line.
//!
//! A form is checked, lowered to Scheme that carries what the checker proved
//! (`fixpt_fx26::lower`), and run. The REPL prints what FX-87's did — the
//! value, then ` : <type> ! <effect>` — and `,code` shows the lowered Scheme.
//!
//! Definitions persist between inputs: `(define name type expression)`,
//! `(define name expression)` and `(define-type name type)`.

use crate::lineedit::{Line, LineReader, Note};
use fixpt_engine::Backend;
use fixpt_fx26::session::{Fx26Session, Outcome};
use fixpt_fx26::{Checker, Top};
use fixpt_read::{Datum, FileId, Sym, Syntax, SyntaxProfile};

/// Line and column (both from 1) of byte `at` in `text`.
fn line_col(text: &str, at: usize) -> (usize, usize) {
    let before = &text[..at.min(text.len())];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    (line, col)
}

fn located(name: &str, text: &str, e: &fixpt_fx26::FxError) -> String {
    let (line, col) = line_col(text, e.span.start as usize);
    format!("{name}:{line}:{col}: {}", e.message)
}

/// What checking found, as the REPL prints it after the value.
fn report(c: &Checker, top: &Top) -> String {
    match top {
        Top::Exp(k) => format!(" : {} ! {}", c.show_ty(k.ty), c.show_effect(&k.effect)),
        Top::Define { name, ty, effect, .. } => {
            format!("{} : {} ! {}", c.interner.name(*name), c.show_ty(*ty), c.show_effect(effect))
        }
        Top::DefineRec { bindings } => {
            let lines: Vec<String> =
                bindings.iter().map(|(n, t, _)| format!("{} : {} ! pure", c.interner.name(*n), c.show_ty(*t))).collect();
            lines.join("\n")
        }
        Top::DefineType { name, ty } => format!("{} = {}", c.interner.name(*name), c.show_definition(*ty)),
        Top::DefineTypeFamily { name } => format!("{}: a type with parameters", c.interner.name(*name)),
        Top::DefineEffect { name, effect } => format!("{} = {}", c.interner.name(*name), c.show_effect(effect)),
        Top::PrivateRegions { regions } => {
            let names: Vec<String> = regions.iter().map(|r| c.show_region(*r)).collect();
            format!("; private: {}", names.join(" "))
        }
    }
}

/// One result: what it printed, its value and what checking found — or why
/// running it failed.
fn show(session: &Fx26Session, out: &Outcome, show_code: bool) {
    if show_code && !out.code.is_empty() {
        println!("; {}", out.code);
    }
    print!("{}", out.printed);
    let found = report(&session.checker, &out.top);
    match &out.value {
        Ok(Some(v)) => println!("{v}{found}"),
        Ok(None) => println!("{found}"),
        Err(e) => {
            println!("{found}");
            eprintln!("! evaluation failed: {e}");
        }
    }
}

fn start(backend: Backend) -> Result<Fx26Session, i32> {
    let mut s = Fx26Session::with_backend(backend).map_err(|e| {
        eprintln!("fixpt: {e}");
        1
    })?;
    s.strategy = crate::FX26_RUN.get().copied().unwrap_or_default();
    if let Some(m) = crate::THREADED_MACHINE.get() {
        s.scheme.runtime_unrooted().run_word = Some(*m);
    }
    crate::apply_gc_policy(&mut s.scheme);
    if let Some(l) = crate::STEP_LIMIT.get() {
        s.set_step_limit(*l);
    }
    if let Some(l) = crate::SPECULATION_STEP_LIMIT.get() {
        s.speculation_limit = *l;
    }
    Ok(s)
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
    println!("fixpt {} — FX-26, {engine}", env!("CARGO_PKG_VERSION"));
    println!("(each form is checked, lowered to Scheme and run. `,help` for commands,");
    println!(" `,code` to show the lowered Scheme. ^D leaves.)");

    // FX-26 code reads FX-26 input: the eager reader written in FX-26, once
    // its licence is checked. Without it, the Rust reader.
    let mut eager = match fixpt_fx26::session::load_eager_reader(&mut session.scheme).and_then(|()| {
        fixpt_scheme::eager::EagerReader::attach_starting(
            &mut session.scheme,
            fixpt_fx26::session::READER_PREFIX,
            "eager-start-fx26",
        )
        .map_err(|e| e.to_string())
    }) {
        Ok(r) => {
            println!("(read as you type by the eager reader written in FX-26; its licence checked)");
            Some(r)
        }
        Err(why) => {
            println!("(the FX-26 eager reader is not used: {why})");
            None
        }
    };
    let mut reader = LineReader::new(".fixpt_fx26_history", SyntaxProfile::FX26);
    let mut show_code = false;
    let mut disassembling;
    let mut n = 0usize;
    loop {
        reader.set_completions(known_names(&session.checker));
        let line = {
            let mut oracle = Oracle { session: &mut session, reader: eager.as_mut() };
            reader.read_with("fx26> ", "     | ", &mut oracle, "")
        };
        let text = match line {
            Line::Eof => {
                reader.save();
                return 0;
            }
            Line::Interrupted | Line::Ask { .. } => continue,
            Line::Form(text) => text,
        };
        if let Some(ask) = crate::help::parse(&text) {
            crate::help::answer(&mut session.checker, &ask);
            continue;
        }
        // `,disassemble E`: E's threaded code, shown, as `disassemble` gives
        // it (under `--fx26-run threaded`; lowered, there is none).
        let text = match text.trim().strip_prefix(",disassemble") {
            Some(e) if !e.trim().is_empty() => {
                disassembling = true;
                format!("(disassemble {e})")
            }
            _ => {
                disassembling = false;
                text
            }
        };
        // `,step-limit [N|none]`: the limit on a form's steps, shown or set.
        if let Some(arg) = text.trim().strip_prefix(",step-limit") {
            let show = |l: Option<u64>| l.map_or("none".to_string(), |n| n.to_string());
            match arg.trim() {
                "" => println!("; step limit: {}", show(session.step_limit())),
                v => match crate::parse_limit(v) {
                    Some(l) => {
                        session.set_step_limit(l);
                        println!("; step limit: {}", show(l));
                    }
                    None => eprintln!("; `,step-limit` takes a count of steps, or none"),
                },
            }
            continue;
        }
        match text.trim() {
            "" => continue,
            ",code" => {
                show_code = !show_code;
                println!("; lowered Scheme: {}", if show_code { "on" } else { "off" });
                continue;
            }
            ",quit" => {
                reader.save();
                return 0;
            }
            _ => {}
        }
        n += 1;
        let name = format!("<fx26:{n}>");
        let forms = match session.checker.read_in(FileId(0), &text) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("read error: {}", located(&name, &text, &e));
                continue;
            }
        };
        for form in &forms {
            if let Some(lines) = answer_hole(&mut session.checker, form) {
                for l in lines {
                    println!("{l}");
                }
                continue;
            }
            let known = session.checker.value_names();
            match session.run(form) {
                Ok(out) if disassembling => match &out.value {
                    Ok(Some(v)) => print!("{}", unwrite_string(v)),
                    _ => show(&session, &out, show_code),
                },
                Ok(out) => {
                    show(&session, &out, show_code);
                    let defined: Vec<Sym> = match &out.top {
                        Top::Define { name, .. } => vec![*name],
                        Top::DefineRec { bindings } => bindings.iter().map(|(n, _, _)| *n).collect(),
                        _ => Vec::new(),
                    };
                    for name in defined.iter().filter(|n| known.contains(n)) {
                        println!("{}", shadowing_note(session.checker.interner.name(*name)));
                    }
                }
                Err(e) => eprintln!("{}", located(&name, &text, &e)),
            }
        }
    }
}

/// A second `define` makes a new binding (ML's top level, not Scheme's):
/// said at the REPL, where Scheme's habits would expect an assignment.
fn shadowing_note(name: &str) -> String {
    format!("; note: a new `{name}`. What was defined before keeps the old one: define it again to use this one.")
}

/// A string as it was written, `"…"` with escapes, back to its text.
fn unwrite_string(w: &str) -> String {
    let Some(inner) = w.strip_prefix('"').and_then(|x| x.strip_suffix('"')) else { return format!("{w}\n") };
    let mut out = String::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some(x) => out.push(x),
            None => {}
        }
    }
    out
}

/// Run every form of `files` in one session, printing only what the program
/// prints. The first error, static or dynamic, stops it.
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
        let forms = match session.checker.read_in(FileId(0), &text) {
            Ok(forms) => forms,
            Err(e) => {
                eprintln!("fixpt: read error: {}", located(f, &text, &e));
                return 1;
            }
        };
        // A file is a whole program: its definitions may come in any order.
        let outs = match session.run_forms(&forms) {
            Ok(outs) => outs,
            Err(e) => {
                eprintln!("fixpt: {}", located(f, &text, &e));
                return 1;
            }
        };
        for out in outs {
            match out {
                Ok(out) => {
                    print!("{}", out.printed);
                    if let Err(e) = out.value {
                        eprintln!("fixpt: {e}");
                        return 1;
                    }
                }
                Err(e) => {
                    eprintln!("fixpt: {}", located(f, &text, &e));
                    return 1;
                }
            }
        }
    }
    0
}

/// Run the forms of `text` and print what each is.
pub fn eval(backend: Backend, text: &str) -> i32 {
    let mut session = match start(backend) {
        Ok(s) => s,
        Err(code) => return code,
    };
    let forms = match session.checker.read_in(FileId(0), text) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("fixpt: read error: {}", located("<argument>", text, &e));
            return 1;
        }
    };
    for form in &forms {
        match session.run(form) {
            Ok(out) => {
                show(&session, &out, false);
                if out.value.is_err() {
                    return 1;
                }
            }
            Err(e) => {
                eprintln!("fixpt: {}", located("<argument>", text, &e));
                return 1;
            }
        }
    }
    0
}

/// Names for completion and for not colouring as unbound: what the
/// environment binds, the type names, and the reserved words.
fn known_names(c: &Checker) -> Vec<String> {
    let mut names: Vec<String> = c
        .value_names()
        .into_iter()
        .chain(c.type_names())
        .chain(c.base_names())
        .map(|s| c.interner.name(s).to_string())
        .chain(fixpt_fx26::top::KEYWORDS.iter().map(|k| k.to_string()))
        .collect();
    names.sort();
    names.dedup();
    names
}

// ------------------------------------------------------------------- help

impl crate::help::Helpful for Checker {
    fn dialect(&self) -> &'static str {
        "FX-26"
    }

    fn typed(&self) -> bool {
        true
    }

    fn holes(&self) -> bool {
        true
    }

    fn describe(&mut self, name: &str) -> Vec<String> {
        let Some(sym) = self.interner.get(name) else { return Vec::new() };
        let mut out = Vec::new();
        if let Some(t) = self.type_of_name(sym) {
            out.push(format!("{name} : {}", self.show_ty(t)));
        }
        if let Some(t) = self.type_named(sym) {
            out.push(format!("{name} = {}  (a type)", self.show_definition(t)));
        }
        if self.base_names().contains(&sym) {
            out.push(format!("{name}  (a base type)"));
        }
        out
    }

    fn apropos(&mut self, pattern: &str) -> Vec<String> {
        let mut out: Vec<String> = self
            .value_names()
            .into_iter()
            .filter(|s| self.interner.name(*s).contains(pattern))
            .filter_map(|s| {
                let t = self.type_of_name(s)?;
                Some(format!("{} : {}", self.interner.name(s), self.show_ty(t)))
            })
            .collect();
        out.sort();
        out
    }

    fn fits(&mut self, type_text: &str) -> Option<Vec<String>> {
        let want = self.type_of_str(type_text).ok()?;
        Some(self.search(|c, params, _| params.first().is_some_and(|p| c.subtype(want, *p))))
    }

    fn returns(&mut self, type_text: &str) -> Option<Vec<String>> {
        let want = self.type_of_str(type_text).ok()?;
        Some(self.search(|c, _, result| c.subtype(result, want)))
    }
}

/// A search over the subroutines in the environment. Polymorphic ones are
/// not instantiated — FX-26 has no inference yet (plan step 4) — so they are
/// found only by name.
trait Search {
    fn search(
        &mut self,
        keep: impl FnMut(&mut Checker, &[fixpt_fx26::ast::TyId], fixpt_fx26::ast::TyId) -> bool,
    ) -> Vec<String>;
}

impl Search for Checker {
    fn search(
        &mut self,
        mut keep: impl FnMut(&mut Checker, &[fixpt_fx26::ast::TyId], fixpt_fx26::ast::TyId) -> bool,
    ) -> Vec<String> {
        let mut out = Vec::new();
        for s in self.value_names() {
            let Some(t) = self.type_of_name(s) else { continue };
            let fixpt_fx26::ast::Ty::Subr { params, result, .. } = self.arena.get(t).clone() else {
                continue;
            };
            if keep(self, &params, result) {
                out.push(format!("{} : {}", self.interner.name(s), self.show_ty(t)));
            }
        }
        out.sort();
        out
    }
}

// ----------------------------------------------- help inside an expression

/// Where a `,help` hole is in `form`, if `form` is an application with one.
fn hole_position(c: &Checker, form: &Syntax) -> Option<(Vec<Syntax>, usize)> {
    let Datum::List { items, tail: None } = &form.datum else { return None };
    let is_hole = |s: &Syntax| match &s.datum {
        Datum::List { items, tail: None } if items.len() == 2 => matches!(
            (&items[0].datum, &items[1].datum),
            (Datum::Symbol(u), Datum::Symbol(h))
                if c.interner.name(*u) == "unquote" && matches!(c.interner.name(*h), "help" | "?")
        ),
        _ => false,
    };
    let at = items.iter().position(is_hole)?;
    Some((items.clone(), at))
}

/// The static answer to a hole: what the argument there must be.
fn answer_hole(c: &mut Checker, form: &Syntax) -> Option<Vec<String>> {
    let (items, at) = hole_position(c, form)?;
    if at == 0 {
        return Some(vec!["; FX-26 answers a hole in argument position, not as the operator".into()]);
    }
    let op = fixpt_read::write_syntax(&items[0], &c.interner);
    Some(match c.describe_argument(&items, at) {
        Some(t) => vec![format!("; the hole wants: {t}  (argument {at} of {op})")],
        None => vec![format!("; `{op}` is not a subroutine whose argument {at} can be known here")],
    })
}

// ------------------------------------------------ checking while typing

/// Reads with the Rust reader, and checks the form as it is typed — see
/// [`crate::speculate`]. A finished expression is also *run* as it is typed,
/// when its effect is licensed (`fixpt_fx26::licence`): its value is shown
/// before `Enter`, and nothing it could do is visible to the program.
struct Oracle<'a> {
    session: &'a mut Fx26Session,
    /// The eager reader written in FX-26, deciding what `Enter` does.
    reader: Option<&'a mut fixpt_scheme::eager::EagerReader>,
}

impl crate::lineedit::Oracle for Oracle<'_> {
    fn status(&mut self, text: &str, at_enter: bool) -> crate::lineedit::Status {
        match self.reader.as_deref_mut() {
            // A `,help` hole in FX-26 is answered once the form is entered,
            // so a hole mid-form is just an unfinished form.
            Some(r) => crate::eager_status(r, &mut self.session.scheme, text, at_enter, SyntaxProfile::FX26, false),
            None => crate::lineedit::Reread(SyntaxProfile::FX26).status(text, at_enter),
        }
    }

    fn notes(&mut self, text: &str) -> Vec<Note> {
        let Some(p) = crate::speculate::partial(text, SyntaxProfile::FX26) else {
            return Vec::new();
        };
        // Leave no trace: symbols read here are forgotten afterwards, so a
        // typo never turns up as a completion.
        let mark = self.session.checker.interner.len();
        let notes = speculative_notes(self.session, text, &p);
        self.session.checker.interner.truncate(mark);
        notes
    }
}

fn speculative_notes(session: &mut Fx26Session, text: &str, p: &crate::speculate::Partial) -> Vec<Note> {
    let c = &mut session.checker;
    let Ok(forms) = c.read_in(FileId(0), &p.closed) else { return Vec::new() };
    // Each form is tried in the environment the ones before it would make,
    // and all of it is forgotten afterwards.
    let error = try_all(c, &forms, &mut |e| {
        let (start, end) = (e.span.start as usize, e.span.end as usize);
        (p.finished(text) || p.believe(start, end)).then(|| Note {
            span: char_span(text, start, end),
            message: e.message.clone(),
            error: true,
        })
    });
    if let Some(note) = error {
        return vec![note];
    }
    // One finished expression: run it early, if the licence allows.
    if p.finished(text)
        && let [form] = &forms[..]
    {
        use fixpt_fx26::session::Speculation;
        let message = match session.speculate(form) {
            Speculation::Value(v) => Some(format!("= {v}")),
            Speculation::Failed(e) => Some(format!("running it fails: {e}")),
            Speculation::NotLicensed(atom) => Some(format!("not run early: it may {atom}")),
            Speculation::Rejected(_) | Speculation::NotAnExpression => None,
        };
        return message.map(|message| vec![Note { span: None, message, error: false }]).unwrap_or_default();
    }
    let c = &mut session.checker;
    let hint = p.hole_form.as_ref().and_then(|h| {
        let form = c.read_in(FileId(0), h).ok()?.into_iter().next()?;
        let (items, at) = hole_position(c, &form)?;
        let want = c.describe_argument(&items, at)?;
        let op = fixpt_read::write_syntax(&items[0], &c.interner);
        Some(format!("argument {at} of {op} wants {want}"))
    });
    hint.map(|message| vec![Note { span: None, message, error: false }]).unwrap_or_default()
}

/// Try `forms` in order, each in the scope of the ones before, keeping
/// nothing; the first error `judge` accepts is the answer.
fn try_all(
    c: &mut Checker,
    forms: &[Syntax],
    judge: &mut dyn FnMut(&fixpt_fx26::FxError) -> Option<Note>,
) -> Option<Note> {
    let (first, rest) = forms.split_first()?;
    c.try_top(first, |c, r| match r {
        Err(e) => judge(&e),
        Ok(_) => try_all(c, rest, judge),
    })
}

/// A byte span of `text` as characters, if it is a real one.
fn char_span(text: &str, start: usize, end: usize) -> Option<(usize, usize)> {
    if start >= end || end > text.len() {
        return None;
    }
    Some((text[..start].chars().count(), text[..end].chars().count()))
}

#[cfg(test)]
mod speculative {
    use super::*;
    use crate::lineedit::Oracle as _;

    fn notes_in(s: &mut Fx26Session, text: &str) -> Vec<Note> {
        let before = s.checker.interner.len();
        let notes = Oracle { session: s, reader: None }.notes(text);
        assert_eq!(s.checker.interner.len(), before, "checking left symbols behind");
        notes
    }

    fn session() -> Fx26Session {
        Fx26Session::with_backend(Backend::Ast).expect("starts")
    }

    fn notes(text: &str) -> Vec<Note> {
        notes_in(&mut session(), text)
    }

    #[test]
    fn an_error_in_a_finished_subform_is_reported_while_typing() {
        let n = notes("(+ 1 (car 5) ");
        assert_eq!(n.len(), 1, "{n:?}");
        assert!(n[0].error);
        // The argument itself, and the pair `+` needs one element of.
        assert_eq!(n[0].span, Some((10, 11)), "{n:?}");
        assert_eq!(n[0].message, "argument 1 is a int, where a (pairof int t2 r) is expected");
    }

    #[test]
    fn what_closing_off_would_break_is_not_reported() {
        for text in ["(if", "(if #t", "(+ 1", "(lambda ((x int))"] {
            assert!(notes(text).iter().all(|n| !n.error), "{text:?}: {:?}", notes(text));
        }
    }

    #[test]
    fn a_finished_form_is_judged_whole() {
        assert!(notes("(+ 1 #t)").first().is_some_and(|n| n.error));
    }

    /// A finished expression whose effect is licensed runs as it is typed,
    /// and its value is the hint.
    #[test]
    fn a_licensed_expression_shows_its_value_before_enter() {
        assert_eq!(notes("(+ 1 2)")[0].message, "= 3");
        assert_eq!(notes("(car (cons 1 #t))")[0].message, "= 1");
    }

    /// One that is not licensed says why, and does not run.
    #[test]
    fn an_unlicensed_expression_says_why_it_was_not_run() {
        let mut s = session();
        let forms = s.checker.read_in(FileId(0), "(define c (ref int @c) (new 1))").expect("reads");
        s.run(&forms[0]).expect("runs");
        assert_eq!(notes_in(&mut s, "(set c 5)")[0].message, "not run early: it may (write @c)");
        let forms = s.checker.read_in(FileId(0), "(define peek (subr (read @c) () int) (lambda () (get c)))").expect("reads");
        s.run(&forms[0]).expect("runs");
        let forms = s.checker.read_in(FileId(0), "(peek)").expect("reads");
        assert_eq!(s.run(&forms[0]).expect("runs").value, Ok(Some("1".into())));
    }

    #[test]
    fn the_argument_at_the_cursor_is_described() {
        let n = notes("(+ 1 ");
        assert_eq!(n.len(), 1, "{n:?}");
        assert!(!n[0].error);
        assert_eq!(n[0].message, "argument 2 of + wants int");
    }

    /// The hint infers from the arguments already written: once `cons` has
    /// an int, its pair's first element is known, and the second is not.
    #[test]
    fn the_hint_solves_what_the_arguments_so_far_determine() {
        assert_eq!(notes("(car ")[0].message, "argument 1 of car wants (pairof t1 t2 r)");
        assert_eq!(notes("(set-car! (cons 1 #t) ")[0].message.split(" wants ").nth(1), Some("int"));
    }

    #[test]
    fn a_definition_being_typed_is_not_kept() {
        let mut s = session();
        assert!(notes_in(&mut s, "(define z 4) (+ z 1)").is_empty());
        let x = s.checker.read_in(FileId(0), "z").expect("reads");
        assert!(s.checker.top(&x[0]).is_err(), "a definition typed but not entered was kept");
    }
}

#[cfg(test)]
mod commands {
    use super::*;
    use crate::help::Helpful;

    #[test]
    fn known_names_include_definitions_types_and_keywords() {
        let mut c = Checker::new();
        let forms = c.read_in(FileId(0), "(define seven 7) (define-type cell (ref int @c))").expect("reads");
        for f in &forms {
            c.top(f).expect("checks");
        }
        let names = known_names(&c);
        for want in ["seven", "cell", "int", "cwcc", "lambda", "define-type"] {
            assert!(names.iter().any(|n| n == want), "missing {want:?}");
        }
    }

    #[test]
    fn describe_and_search() {
        let mut c = Checker::new();
        assert_eq!(c.describe("+"), ["+ : (subr pure (int int) int)"]);
        let returns = c.returns("bool").expect("typed");
        assert!(returns.iter().any(|l| l.starts_with("= :")), "{returns:?}");
        let fits = c.fits("int").expect("typed");
        assert!(fits.iter().any(|l| l.starts_with("+ :")), "{fits:?}");
    }

    #[test]
    fn a_hole_is_answered_from_the_operators_type() {
        let mut c = Checker::new();
        let forms = c.read_in(FileId(0), "(= 1 ,help)").expect("reads");
        let lines = answer_hole(&mut c, &forms[0]).expect("a hole");
        assert_eq!(lines, ["; the hole wants: int  (argument 2 of =)"]);
    }
}
