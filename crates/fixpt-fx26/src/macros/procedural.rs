//! Procedural macros, a prototype (`TODO.md` §228; `docs/research/
//! typed-macros.md`, "Procedural macros, prototyped"): Clinger's explicit
//! renaming, `(er-macro-transformer proc)`, and Hanson's syntactic closures,
//! `(sc-macro-transformer proc)` and `(rsc-macro-transformer proc)`, each
//! `proc` an FX-26 procedure over `datum`s.
//!
//! A transformer is checked and run, at each use, by an FX-26 session of its
//! own (`run`), in the standard environment and this prelude alone: what the
//! program defines is not there as it expands. Its answer, a datum, comes
//! back as text, read at the use's place.
//!
//! Hygiene is by aliases, one spelling for both systems: `%~N:x` is `x` as
//! where the macro was defined, made by expansion `N`. An alias the expansion
//! binds is a name of its own, which nothing the use wrote can capture; one
//! it leaves free is the top level's `x` (`#%toplevel:x`); one at a form's
//! head that names a form, or as a label, or quoted, is `x`
//! (`Checker::unaliased`). ER's `rename` makes them; syntactic closures are
//! aliases made of every name closed in the macro's environment
//! (`closed`). What is not built: `capture-syntactic-environment`, and
//! names compared by what they mean rather than as written (`TODO.md`
//! §222).

use std::cell::RefCell;

use fixpt_read::{Datum, Interner, Span, Sym, Syntax};

use crate::{FxError, R};

/// Which transformer a procedural macro has.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Style {
    /// `(er-macro-transformer (lambda (form rename compare) …))`.
    Er,
    /// `(sc-macro-transformer (lambda (form use-env) …))`: what it gives is
    /// closed in the macro's environment.
    Sc,
    /// `(rsc-macro-transformer (lambda (form macro-env) …))`: what it gives
    /// is closed in the use's.
    Rsc,
}

impl Style {
    pub(crate) fn named(n: &str) -> Option<Style> {
        match n {
            "er-macro-transformer" => Some(Style::Er),
            "sc-macro-transformer" => Some(Style::Sc),
            "rsc-macro-transformer" => Some(Style::Rsc),
            _ => None,
        }
    }

    /// The type a transformer of this style is checked at.
    fn ty(self) -> &'static str {
        match self {
            Style::Er => {
                "(subr spin (datum (subr pure (symbol) symbol) (subr spin (symbol symbol) bool)) datum)"
            }
            Style::Sc | Style::Rsc => "(subr spin (datum symbol) datum)",
        }
    }
}

/// A procedural macro: its style, and its transformer's text.
#[derive(Debug)]
pub(crate) struct Procedural {
    pub style: Style,
    pub code: String,
}

/// The syntactic environments a syntactic-closure transformer is given and
/// closes in: the use's, and the macro's.
pub(crate) const USE_ENV: &str = "%env:use";
pub(crate) const MACRO_ENV: &str = "%env:macro";
/// A syntactic closure as a datum: `(%sc env (free …) form)`.
const CLOSURE: &str = "%sc";

/// What every transformer sees besides the standard environment.
const PRELUDE: &str = include_str!("procedural-prelude.fx");

thread_local! {
    /// The session transformers run in, made at the first and kept.
    static SESSION: RefCell<Option<crate::session::Fx26Session>> = const { RefCell::new(None) };
}

/// `run` made what the runtime's syscall for the expander written in
/// FX-26 calls (`fixpt_runtime::syscall::PROCEDURAL`).
pub fn install() {
    let _ = fixpt_runtime::syscall::PROCEDURAL.set(run);
}

/// FX-26 program `code` run in the transformers' session: the last form's
/// value, printed as `write` does; or why not.
pub fn run(code: &str) -> Result<String, String> {
    SESSION.with(|s| {
        let mut s = s.borrow_mut();
        if s.is_none() {
            let mut made = crate::session::Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).map_err(|e| e.message)?;
            match made.run_program(PRELUDE) {
                Ok(Ok(_)) => {}
                Ok(Err(e)) => return Err(format!("the transformers' prelude: {e}")),
                Err(e) => return Err(format!("the transformers' prelude: {}", e.message)),
            }
            *s = Some(made);
        }
        match s.as_mut().expect("made").run_program(code) {
            Ok(r) => r,
            Err(e) => Err(e.message.into()),
        }
    })
}

/// The program that checks a transformer, `code`, at its style's type.
pub(crate) fn checked(style: Style, code: &str) -> String {
    format!("(begin (the {} {}) #u)", style.ty(), helpers(code))
}

/// `code` with the prelude's procedures bound around it, as locals.
fn helpers(code: &str) -> String {
    format!(
        "(let ((make-syntactic-closure %make-syntactic-closure) (identifier? %identifier?) (identifier=? %identifier=?)) {code})"
    )
}

/// The program that runs a transformer, `code`, on `form` (as text), in
/// expansion `made`.
pub(crate) fn applied(style: Style, code: &str, form: &str, made: u32) -> String {
    let t = style.ty();
    let code = helpers(code);
    match style {
        Style::Er => format!("((the {t} {code}) (quote {form}) (%er-renamer {made}) %er-compare)"),
        Style::Sc => format!("((the {t} {code}) (quote {form}) (quote {USE_ENV}))"),
        Style::Rsc => format!("((the {t} {code}) (quote {form}) (quote {MACRO_ENV}))"),
    }
}

/// `x`'s name as where its alias's macro was defined, if `x` is an alias:
/// every `%~N:` taken off.
pub fn alias_base(x: &str) -> Option<&str> {
    let mut s = x;
    let mut any = false;
    while let Some(rest) = s.strip_prefix("%~") {
        let Some(c) = rest.find(':') else { break };
        if c == 0 || !rest[..c].bytes().all(|b| b.is_ascii_digit()) {
            break;
        }
        s = &rest[c + 1..];
        any = true;
    }
    any.then_some(s)
}

/// `x`'s alias, made by expansion `made`.
fn alias(x: &str, made: u32) -> String {
    format!("%~{made}:{x}")
}

/// What a syntactic-closure transformer gave, `s`, its closures opened: in
/// environment `macro_env` (else the use's), each name an alias (expansion
/// `made`'s) or as written; a closure's form in its own environment, its
/// free names in the one around it; a quoted datum as it is.
pub(crate) fn closed(s: &Syntax, macro_env: bool, made: u32, interner: &mut Interner) -> R<Syntax> {
    match &s.datum {
        Datum::Symbol(x) if macro_env => {
            let n = alias(interner.name(*x), made);
            Ok(Syntax::symbol(s.span, interner.intern(&n)))
        }
        Datum::List { items, tail } => {
            let head = items.first().and_then(|h| h.as_symbol()).map(|h| interner.name(h).to_string());
            if head.as_deref() == Some("quote") {
                return Ok(s.clone());
            }
            if head.as_deref() == Some(CLOSURE) {
                let [_, env, free, form] = &items[..] else {
                    return Err(FxError::at(s.span, "a syntactic closure is `(%sc env (free …) form)`"));
                };
                let inner = match env.as_symbol().map(|e| interner.name(e)) {
                    Some(USE_ENV) => false,
                    Some(MACRO_ENV) => true,
                    _ => return Err(FxError::at(env.span, "a syntactic closure's environment is one a transformer was given")),
                };
                let free: Vec<Sym> = match &free.datum {
                    Datum::Nil => Vec::new(),
                    _ => free.as_proper_list().and_then(|l| l.iter().map(|x| x.as_symbol()).collect()).ok_or_else(|| FxError::at(free.span, "a syntactic closure's free names are a list of names"))?,
                };
                return opened(form, inner, macro_env, &free, made, interner);
            }
            let items = items.iter().map(|i| closed(i, macro_env, made, interner)).collect::<R<Vec<_>>>()?;
            let tail = match tail {
                Some(t) => Some(Box::new(closed(t, macro_env, made, interner)?)),
                None => None,
            };
            Ok(Syntax::new(s.span, Datum::List { items, tail }))
        }
        _ => Ok(s.clone()),
    }
}

/// A closure's form, `s`, closed in environment `inner`, its `free` names
/// in `outer`.
fn opened(s: &Syntax, inner: bool, outer: bool, free: &[Sym], made: u32, interner: &mut Interner) -> R<Syntax> {
    match &s.datum {
        Datum::Symbol(x) if free.contains(x) => closed(s, outer, made, interner),
        Datum::Symbol(_) => closed(s, inner, made, interner),
        Datum::List { items, tail } => {
            let head = items.first().and_then(|h| h.as_symbol()).map(|h| interner.name(h).to_string());
            if matches!(head.as_deref(), Some("quote") | Some(CLOSURE)) {
                return closed(s, inner, made, interner);
            }
            let items = items.iter().map(|i| opened(i, inner, outer, free, made, interner)).collect::<R<Vec<_>>>()?;
            let tail = match tail {
                Some(t) => Some(Box::new(opened(t, inner, outer, free, made, interner)?)),
                None => None,
            };
            Ok(Syntax::new(s.span, Datum::List { items, tail }))
        }
        _ => Ok(s.clone()),
    }
}

/// What a transformer gave, `s`, each alias that is a keyword's name made
/// the keyword (`is_keyword`: a form's, a description's word, a macro's),
/// which nothing binds, so nothing could capture; and every alias quoted
/// made its name, a symbol as data.
pub(crate) fn keywords(s: &Syntax, is_keyword: &dyn Fn(&str) -> bool, interner: &mut Interner) -> Syntax {
    match &s.datum {
        Datum::Symbol(x) => match alias_base(interner.name(*x)) {
            Some(b) if is_keyword(b) => {
                let b = b.to_string();
                Syntax::symbol(s.span, interner.intern(&b))
            }
            _ => s.clone(),
        },
        Datum::List { items, tail } => {
            let quoted = items.first().and_then(|h| h.as_symbol()).is_some_and(|h| {
                let n = interner.name(h);
                matches!(n, "quote" | "quasiquote") || alias_base(n).is_some_and(|b| matches!(b, "quote" | "quasiquote"))
            });
            if quoted {
                return Syntax::new(s.span, Datum::List { items: items.iter().map(|i| unaliased(i, interner)).collect(), tail: tail.as_ref().map(|t| Box::new(unaliased(t, interner))) });
            }
            Syntax::new(
                s.span,
                Datum::List { items: items.iter().map(|i| keywords(i, is_keyword, interner)).collect(), tail: tail.as_ref().map(|t| Box::new(keywords(t, is_keyword, interner))) },
            )
        }
        Datum::Vector(xs) => Syntax::new(s.span, Datum::Vector(xs.iter().map(|i| keywords(i, is_keyword, interner)).collect())),
        _ => s.clone(),
    }
}

/// `s` with every alias its name.
fn unaliased(s: &Syntax, interner: &mut Interner) -> Syntax {
    match &s.datum {
        Datum::Symbol(x) => match alias_base(interner.name(*x)) {
            Some(b) => {
                let b = b.to_string();
                Syntax::symbol(s.span, interner.intern(&b))
            }
            None => s.clone(),
        },
        Datum::List { items, tail } => {
            Syntax::new(s.span, Datum::List { items: items.iter().map(|i| unaliased(i, interner)).collect(), tail: tail.as_ref().map(|t| Box::new(unaliased(t, interner))) })
        }
        Datum::Vector(xs) => Syntax::new(s.span, Datum::Vector(xs.iter().map(|i| unaliased(i, interner)).collect())),
        _ => s.clone(),
    }
}

/// `s` at the use's place, `at`, of expansion `made`: what a transformer
/// gave, read from text, placed where the use was.
pub(crate) fn placed(s: &Syntax, at: Span, made: u32) -> Syntax {
    let span = Span { expansion: made, ..at };
    match &s.datum {
        Datum::List { items, tail } => Syntax::new(
            span,
            Datum::List { items: items.iter().map(|i| placed(i, at, made)).collect(), tail: tail.as_ref().map(|t| Box::new(placed(t, at, made))) },
        ),
        Datum::Vector(xs) => Syntax::new(span, Datum::Vector(xs.iter().map(|i| placed(i, at, made)).collect())),
        d => Syntax::new(span, d.clone()),
    }
}

#[cfg(test)]
mod tests {
    use super::alias_base;

    #[test]
    fn an_alias_is_its_base_name_marked() {
        assert_eq!(alias_base("%~3:let"), Some("let"));
        assert_eq!(alias_base("%~7:%~3:x"), Some("x"));
        assert_eq!(alias_base("let"), None);
        assert_eq!(alias_base("%x:3"), None);
        assert_eq!(alias_base("%~:x"), None);
    }
}
