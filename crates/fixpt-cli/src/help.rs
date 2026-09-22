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
//! The commands are the same in every dialect; what each can answer differs,
//! and a dialect that cannot answer one says so rather than staying silent.

/// A request typed at the prompt.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Ask {
    /// `,help` — what the commands are.
    Overview,
    /// `,help NAME` — what one name is.
    Name(String),
    /// `,apropos TEXT` — names containing it.
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

/// What a dialect can tell you.
///
/// Every method returns lines to print. An empty result and an unsupported
/// question are different, and the caller distinguishes them — a REPL that
/// answers "nothing found" when it means "I cannot ask that" is worse than one
/// that says nothing.
pub trait Helpful {
    /// The dialect's name, for the overview.
    fn dialect(&self) -> &'static str;
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
    for (cmd, what) in [
        (",help NAME", "what a name is"),
        (",apropos TEXT", "names containing TEXT"),
        (",fits TYPE", "what accepts a value of that type"),
        (",returns TYPE", "what produces one"),
        (",quit", "leave"),
    ] {
        println!("  {cmd:<16} {what}");
    }
    println!("; anything else is evaluated.");
}
