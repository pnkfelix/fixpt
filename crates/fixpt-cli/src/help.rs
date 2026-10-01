//! Asking the REPL what to do next.
//!
//! Ordinary REPL help is a list of names and a paragraph each, written by hand
//! and out of date by the second release. This one asks the running system,
//! which already knows more than a manual would: the Scheme side has the
//! primitive table, and the FX front ends have a *type* for every binding in
//! their standard environment, generated from the 1987 and 1991 sources.
//!
//! That makes one question answerable that a REPL usually cannot answer at all:
//!
//! ```text
//! fx87> ,fits (pairof int bool @=)
//! ```
//!
//! — *I have one of these; what accepts it?* The environment carries a type for
//! every name and [`subtype`](fixpt_fx87::subtype) decides the rest, so the
//! answer is a search rather than a guess. Polymorphic bindings are matched
//! with their binders left as unknowns, exactly as implicit projection does at
//! a real call site, so `car` is found without anyone having to instantiate it
//! first.
//!
//! A hole — `,help` written *inside* a form — is answered twice, because there
//! are two different things to know and neither subsumes the other.
//!
//! *Statically*, from the types: the hole is one argument of one subroutine,
//! and the arguments already written often pin down what the rest must be, so
//! FX can say `the hole wants: int` and then list what produces one.
//!
//! *Dynamically*, by running the program: the form is evaluated as written
//! except at the hole, which becomes `(%hole POSITION TOTAL)` — a primitive
//! that reports the machine's pending work instead of computing. That answer is
//! made of values rather than types (`#(0 0 0)`, not `(vectorof int r)`), it
//! notices things no type can (the branch that means the hole is never reached
//! at all), and it is the *only* answer available in Scheme, which has no types
//! to consult.
//!
//! In Scheme the hole is also *held*: reaching it captures the rest of the
//! form as a composable continuation, delimited by the top level's prompt, so
//! `,resume EXPR` carries on from the hole with a value — as many times as you
//! like, which is how a candidate from the static half gets tried.
//!
//! The dynamic half costs something the static half does not: evaluating an
//! argument the user only asked *about*. In FX that cost is priced by the
//! effect system — an argument is run only when its inferred effect says no one
//! could tell, and otherwise the effect itself is reported. So the static
//! analysis is what licenses the dynamic one.
//!
//! The commands are the same in every dialect; what each can answer differs,
//! and a dialect that cannot answer one says so rather than staying silent.

/// A request typed at the prompt.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Ask {
    /// `,help` — what the commands are.
    Overview,
    /// `,help NAME` — what one name is.
    Name(String),
    /// `,apropos TEXT` — names containing it; in FX-26, `,apropos KIND TEXT`
    /// looks in one namespace (`value`, `type`, `family`, `generative`,
    /// `effect`, `region`, `base`).
    Apropos(String),
    /// `,fits TYPE` — what accepts a value of this type.
    Fits(String),
    /// `,returns TYPE` — what produces one.
    Returns(String),
}

/// Recognise a help request, or `None` if this line is a program.
pub fn parse(line: &str) -> Option<Ask> {
    let line = line.trim();
    let rest = line.strip_prefix(',')?;
    let (word, arg) = match rest.find(char::is_whitespace) {
        Some(i) => (&rest[..i], rest[i..].trim()),
        None => (rest, ""),
    };
    let arg = arg.to_string();
    match word {
        "help" | "h" | "?" if arg.is_empty() => Some(Ask::Overview),
        "help" | "h" | "?" => Some(Ask::Name(arg)),
        "apropos" | "a" if !arg.is_empty() => Some(Ask::Apropos(arg)),
        "fits" | "f" if !arg.is_empty() => Some(Ask::Fits(arg)),
        "returns" | "r" if !arg.is_empty() => Some(Ask::Returns(arg)),
        _ => None,
    }
}

/// Does this form contain a `,help` hole?
///
/// Shared so that a dialect which does not support holes can say so, rather
/// than reporting whatever its checker makes of the bare `unquote` that
/// `,help` reads as. Structural rather than a text search: `",help"` can appear
/// inside a string perfectly legitimately.
pub fn mentions_hole(form: &fixpt_read::Syntax, name_of: &dyn Fn(fixpt_read::Sym) -> String) -> bool {
    use fixpt_read::Datum;
    match &form.datum {
        Datum::List { items, tail } => {
            if is_hole(form, name_of) {
                return true;
            }
            items.iter().any(|i| mentions_hole(i, name_of))
                || tail.as_ref().is_some_and(|t| mentions_hole(t, name_of))
        }
        Datum::Vector(items) => items.iter().any(|i| mentions_hole(i, name_of)),
        _ => false,
    }
}

/// What a dialect can tell you.
///
/// Every method returns lines to print. An empty result and an unsupported
/// question are different, and the caller distinguishes them — a REPL that
/// answers "nothing found" when it means "I cannot ask that" is worse than one
/// that says nothing.
pub trait Helpful {
    /// The dialect's name, for the overview.
    fn dialect(&self) -> &'static str;
    /// Whether the dialect has an environment of types to search, so that
    /// `,fits` and `,returns` mean anything. Listing a command that cannot
    /// work is worse than not having it.
    fn typed(&self) -> bool {
        false
    }
    /// Whether `,help` may be written inside a form to ask about that position.
    fn holes(&self) -> bool {
        false
    }
    /// Whether a hole is *held* when reached, so that `,resume` can continue
    /// it. Only where the hole is really run to — Scheme; the FX dialects
    /// answer a hole by checking it, and speculative evaluation there stops
    /// at the siblings the effect system allows, so there is nothing to hold.
    fn resumable(&self) -> bool {
        false
    }
    fn describe(&mut self, name: &str) -> Vec<String>;
    fn apropos(&mut self, pattern: &str) -> Vec<String>;
    /// `None` when the dialect has no types to search.
    fn fits(&mut self, _type_text: &str) -> Option<Vec<String>> {
        None
    }
    fn returns(&mut self, _type_text: &str) -> Option<Vec<String>> {
        None
    }
}

/// Answer one request, printing the result.
pub fn answer(h: &mut dyn Helpful, ask: &Ask) {
    let dialect = h.dialect();
    let _ = dialect;
    match ask {
        Ask::Overview => overview(h),
        Ask::Name(n) => show("", h.describe(n), &format!("nothing named `{n}`")),
        Ask::Apropos(p) => {
            show("", h.apropos(p), &format!("no name contains `{p}`"))
        }
        Ask::Fits(t) => match h.fits(t) {
            Some(lines) => show(
                &format!("what accepts a value of type {t}:"),
                lines,
                "nothing in the environment accepts one",
            ),
            None => println!(
                "; {} cannot answer that — `,fits` searches an environment of \
                 types, which `--dialect fx87` has",
                h.dialect()
            ),
        },
        Ask::Returns(t) => match h.returns(t) {
            Some(lines) => show(
                &format!("what produces a value of type {t}:"),
                lines,
                "nothing in the environment produces one",
            ),
            None => println!(
                "; {} cannot answer that — `,returns` searches an environment of \
                 types, which `--dialect fx87` has",
                h.dialect()
            ),
        },
    }
}

fn show(header: &str, lines: Vec<String>, empty: &str) {
    if lines.is_empty() {
        println!("; {empty}");
        return;
    }
    if !header.is_empty() {
        println!("; {header}");
    }
    for l in lines {
        println!("  {l}");
    }
}

fn overview(h: &dyn Helpful) {
    println!("; {} — commands", h.dialect());
    let mut rows: Vec<(&str, &str)> = vec![(",help NAME", "what a name is")];
    if h.dialect() == "FX-26" {
        rows.push((",apropos [KIND] TEXT", "names containing TEXT, in every namespace; KIND (value, type, family, generative, effect, region, base) narrows it"));
    } else {
        rows.push((",apropos TEXT", "names containing TEXT"));
    }
    if h.typed() {
        rows.push((",fits TYPE", "what accepts a value of that type"));
        rows.push((",returns TYPE", "what produces one"));
    }
    if h.dialect() == "FX-26" {
        rows.push((",disassemble E", "E's cellular code (under --fx26-run cellular)"));
        rows.push((",disassemble-asm E", "the same, and each word's machine code (or its stencils' source)"));
        rows.push((",inliners NAME", "the globals whose register code inlines NAME's calls"));
        rows.push((",native NAME [ARG…]", "NAME's procedure in the native convention: its machine code, and called on ARGs (under --fx26-run cellular)"));
        rows.push((",redefine b|r", "whether the next redefinition that would break definitions breaks them or is refused"));
        rows.push((",step-limit [N|none]", "show or set how many steps a form may take"));
        rows.push((",time E", "run E, then how long it took to check, generate code for and run, and its collections"));
    }
    rows.push((",quit", "leave"));
    for (cmd, what) in rows {
        println!("  {cmd:<16} {what}");
    }
    if h.holes() {
        println!("; `,help` inside a form asks about that position — the form is");
        println!("  run up to the hole, and what is around it is reported:");
        println!("    (vector-ref (make-vector 3 0) ,help)");
        if h.resumable() {
            println!("  ,resume EXPR     continue from the hole as though it gave EXPR's value");
            println!("  ,where           describe the held hole again");
        }
    }
    if !h.typed() {
        println!(
            "; `,fits` and `,returns` search an environment of types, which \
             `--dialect fx87` has."
        );
    }
    println!("; anything else is evaluated.");
}

/// Replace every `,help` hole with `(with)`, leaving the rest of the form alone.
///
/// The dynamic half of answering a hole: the form is run as written except at
/// the hole, which becomes a call to a primitive that reports the evaluation
/// context instead of computing. Everything the language already does —
/// argument order, macros, the operator's own evaluation — happens for real,
/// so the report describes the program the user actually typed rather than a
/// static reconstruction of it.
pub fn plug_hole(
    form: &fixpt_read::Syntax,
    name_of: &dyn Fn(fixpt_read::Sym) -> String,
    with: fixpt_read::Sym,
) -> fixpt_read::Syntax {
    use fixpt_read::{Datum, Num, Syntax};
    let span = form.span;
    // `(%hole POSITION TOTAL)`. The two constants are what the *reader* knows
    // and the machine may not: which argument of how many the hole is. The AST
    // engine can work that out from its frames, but the compiled engine cannot
    // — a call is push-operator, push-arguments, `CALL n`, so until the `CALL`
    // runs the arity lives only in the instruction stream. Handing the static
    // fact to the dynamic report is what lets the compiled engine segment its
    // operand stack into "this call" and "the calls waiting beneath it".
    let hole = |span, position: i64, total: i64| Syntax {
        span,
        datum: Datum::List {
            items: vec![
                Syntax { span, datum: Datum::Symbol(with) },
                Syntax { span, datum: Datum::Number(Num::Int(position)) },
                Syntax { span, datum: Datum::Number(Num::Int(total)) },
            ],
            tail: None,
        },
    };
    let datum = match &form.datum {
        Datum::List { items, tail } => {
            if is_hole(form, name_of) {
                return hole(span, 0, 0);
            }
            let total = items.len().saturating_sub(1) as i64;
            let at = |i: usize, s: &Syntax| {
                if is_hole(s, name_of) {
                    hole(s.span, i as i64, total)
                } else {
                    plug_hole(s, name_of, with)
                }
            };
            Datum::List {
                items: items.iter().enumerate().map(|(i, s)| at(i, s)).collect(),
                tail: tail.as_ref().map(|t| Box::new(plug_hole(t, name_of, with))),
            }
        }
        Datum::Vector(items) => {
            Datum::Vector(items.iter().map(|i| plug_hole(i, name_of, with)).collect())
        }
        _ => form.datum.clone(),
    };
    Syntax { span, datum }
}

/// Is this form itself the hole — `(unquote help)`, as `,help` reads?
fn is_hole(form: &fixpt_read::Syntax, name_of: &dyn Fn(fixpt_read::Sym) -> String) -> bool {
    use fixpt_read::Datum;
    let Datum::List { items, tail: None } = &form.datum else { return false };
    items.len() == 2
        && matches!((&items[0].datum, &items[1].datum),
            (Datum::Symbol(u), Datum::Symbol(h))
                if name_of(*u) == "unquote" && matches!(name_of(*h).as_str(), "help" | "?"))
}
