//! FX-26 at the command line: checking only, for now.
//!
//! Until FX-26 lowers to Scheme (`docs/fx26.md`, plan step 5), a form is
//! checked and its type and effect reported, and nothing runs. The layout is
//! FX-87's, less the value: ` : <type> ! <effect>`, so that when evaluation
//! arrives the value goes in front and nothing else moves.
//!
//! Definitions persist between inputs: `(define name type expression)`,
//! `(define name expression)` and `(define-type name type)`.

use crate::lineedit::{Line, LineReader, Note};
use fixpt_fx26::{Checker, Top};
use fixpt_read::{Datum, FileId, Syntax, SyntaxProfile};

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

/// What one top-level form did, as the REPL prints it.
fn report(c: &Checker, top: &Top) -> String {
    match top {
        Top::Exp(k) => format!(" : {} ! {}", c.show_ty(k.ty), c.show_effect(&k.effect)),
        Top::Define { name, ty, effect } => {
            format!("{} : {} ! {}", c.interner.name(*name), c.show_ty(*ty), c.show_effect(effect))
        }
        Top::DefineType { name, ty } => format!("{} = {}", c.interner.name(*name), c.show_definition(*ty)),
    }
}

pub fn repl() -> i32 {
    let mut checker = Checker::new();
    println!("fixpt {} — FX-26, checking only (nothing runs yet)", env!("CARGO_PKG_VERSION"));
    println!("(each form is checked and its type and effect shown. `,help` for");
    println!(" commands; ^D leaves.)");

    let mut reader = LineReader::new(".fixpt_fx26_history", SyntaxProfile::FX87);
    let mut n = 0usize;
    loop {
        reader.set_completions(known_names(&checker));
        let line = {
            let mut oracle = Oracle { checker: &mut checker };
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
            crate::help::answer(&mut checker, &ask);
            continue;
        }
        match text.trim() {
            "" => continue,
            ",quit" => {
                reader.save();
                return 0;
            }
            _ => {}
        }
        n += 1;
        let name = format!("<fx26:{n}>");
        let forms = match checker.read_in(FileId(0), &text) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("read error: {}", located(&name, &text, &e));
                continue;
            }
        };
        for form in &forms {
            if let Some(lines) = answer_hole(&mut checker, form) {
                for l in lines {
                    println!("{l}");
                }
                continue;
            }
            match checker.top(form) {
                Ok(top) => println!("{}", report(&checker, &top)),
                Err(e) => eprintln!("{}", located(&name, &text, &e)),
            }
        }
    }
}

/// Check every form of `files` in one environment. Prints nothing when all
/// is well — this is `run` until FX-26 runs — and the first error otherwise.
pub fn run_files(files: &[String]) -> i32 {
    let mut checker = Checker::new();
    for f in files {
        let text = match std::fs::read_to_string(f) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("fixpt: cannot read {f}: {e}");
                return 1;
            }
        };
        let forms = match checker.read_in(FileId(0), &text) {
            Ok(forms) => forms,
            Err(e) => {
                eprintln!("fixpt: read error: {}", located(f, &text, &e));
                return 1;
            }
        };
        for form in &forms {
            if let Err(e) = checker.top(form) {
                eprintln!("fixpt: {}", located(f, &text, &e));
                return 1;
            }
        }
    }
    0
}

/// Check the forms of `text` and print what each is.
pub fn eval(text: &str) -> i32 {
    let mut checker = Checker::new();
    let forms = match checker.read_in(FileId(0), text) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("fixpt: read error: {}", located("<argument>", text, &e));
            return 1;
        }
    };
    for form in &forms {
        match checker.top(form) {
            Ok(top) => println!("{}", report(&checker, &top)),
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
/// [`crate::speculate`].
struct Oracle<'a> {
    checker: &'a mut Checker,
}

impl crate::lineedit::Oracle for Oracle<'_> {
    fn status(&mut self, text: &str, at_enter: bool) -> crate::lineedit::Status {
        crate::lineedit::Reread(SyntaxProfile::FX87).status(text, at_enter)
    }

    fn notes(&mut self, text: &str) -> Vec<Note> {
        let Some(p) = crate::speculate::partial(text, SyntaxProfile::FX87) else {
            return Vec::new();
        };
        // Leave no trace: symbols read here are forgotten afterwards, so a
        // typo never turns up as a completion.
        let mark = self.checker.interner.len();
        let notes = speculative_notes(self.checker, text, &p);
        self.checker.interner.truncate(mark);
        notes
    }
}

fn speculative_notes(c: &mut Checker, text: &str, p: &crate::speculate::Partial) -> Vec<Note> {
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

    fn notes_in(c: &mut Checker, text: &str) -> Vec<Note> {
        let before = c.interner.len();
        let notes = Oracle { checker: c }.notes(text);
        assert_eq!(c.interner.len(), before, "checking left symbols behind");
        notes
    }

    fn notes(text: &str) -> Vec<Note> {
        notes_in(&mut Checker::new(), text)
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
        assert!(notes("(+ 1 2)").is_empty());
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
        let mut c = Checker::new();
        assert!(notes_in(&mut c, "(define z 4) (+ z 1)").is_empty());
        let x = c.read_in(FileId(0), "z").expect("reads");
        assert!(c.top(&x[0]).is_err(), "a definition typed but not entered was kept");
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
