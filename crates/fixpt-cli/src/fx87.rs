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
        let text = match reader.read("fx87> ", "     | ") {
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
    let want = session.checker.expected_argument(fun_ty, &known, at - 1)?;
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

/// The type of one subexpression, or `None` if it does not check.
fn type_of(session: &mut Fx87Session, form: &Syntax) -> Option<fixpt_fx87::DescId> {
    let env = session.checker.env.clone();
    let exp = session.checker.p.parse_exp(form, &Default::default()).ok()?;
    session.checker.check(exp, &env).ok().map(|d| d.ty)
}

fn show(session: &Fx87Session, ty: fixpt_fx87::DescId) -> String {
    fixpt_fx87::unparse::unparse(&session.checker.p.arena, &session.checker.p.interner, ty)
}
