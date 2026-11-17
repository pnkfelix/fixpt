//! Procedural macros, a prototype (`TODO.md` §228; `docs/research/
//! typed-macros.md`, "Procedural macros, prototyped"): Clinger's explicit
//! renaming, `(er-macro-transformer proc)`, and Hanson's syntactic closures,
//! `(sc-macro-transformer proc)` and `(rsc-macro-transformer proc)`, each
//! `proc` an FX-26 procedure over `datum`s.
//!
//! A transformer is checked where its macro is defined and called at each
//! use in a phase-1 namespace (`phase1.rs`), in the standard environment and
//! this prelude alone: what the program defines is not there as it expands.
//! A session's expansion's own, in its runtime, which both expanders call
//! it in; else the transformers' session's (`apply_copied`). It is given
//! the use's datum and gives one, made syntax at the use's place, with no
//! text between (`heap_syn::syn_of_datum`, `copy_datum`).
//!
//! Hygiene is by aliases, one spelling for both systems: `%~K.N:x` is `x` as
//! where the macro was defined, made by the `N`th expansion of the form of
//! key `K` (`Macros::expansion_begun`). An alias the expansion
//! binds is a name of its own, which nothing the use wrote can capture; one
//! it leaves free is the top level's `x` (`#%toplevel:x`); one at a form's
//! head that names a form, or as a label, or quoted, is `x`
//! (`Checker::unaliased`). ER's `rename` makes them; syntactic closures are
//! aliases made of every name closed in the macro's environment
//! (`closed`). What is not built: `capture-syntactic-environment`, and
//! names compared by what they mean rather than as written (`TODO.md`
//! §222).

use std::cell::RefCell;

use fixpt_read::{Interner, Sym};
use crate::heap_syn::{Syn, V};

use crate::{FxError, R};

/// Which transformer a procedural macro has.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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
    /// The type its transformer is checked at: it may not end, and may
    /// read phase 1's globals (`(read @globals)`), the prelude's and its
    /// `begin-for-syntax`'s, which in its namespace, once defined, are never
    /// others (`phase1.rs`); nothing more, no state of any region written
    /// or read, so it is deterministic, as its contract needs.
    pub(crate) fn ty(self) -> &'static str {
        match self {
            Style::Er => {
                "(subr (maxeff (read @globals) spin) (datum (subr pure (symbol) symbol) (subr spin (symbol symbol) bool)) datum)"
            }
            Style::Sc | Style::Rsc => "(subr (maxeff (read @globals) spin) (datum symbol) datum)",
        }
    }
}

/// A procedural macro: its style, its transformer's text, and where it is
/// defined, what its aliases are read in (`hygiene::DefEnv`).
#[derive(Debug)]
pub(crate) struct Procedural {
    pub style: Style,
    pub code: String,
    pub def_env: super::hygiene::DefEnv,
    /// Whether its signature is written, its contract: its uses aligned
    /// with it, its expansions held to it (`Macros::contract_expanded`).
    pub contract: bool,
    /// The phase-1 forms in force where it is defined (`begin-for-syntax`'s
    /// texts, in order), whose namespace it runs in (`phase1.rs`).
    pub phase1: std::rc::Rc<Vec<String>>,
}

/// The syntactic environments a syntactic-closure transformer is given and
/// closes in: the use's, and the macro's.
pub(crate) const USE_ENV: &str = "%env:use";
pub(crate) const MACRO_ENV: &str = "%env:macro";
/// A syntactic closure as a datum: `(%sc env (free …) form)`.
const CLOSURE: &str = "%sc";

thread_local! {
    /// The transformers' session: a session of its own, made at the first
    /// and kept, and a phase-1 namespace in its runtime (`phase1.rs`), each
    /// transformer defined there once, by its style and text. For what has
    /// no namespace of its own to run one in: a checker of its own heap, a
    /// lowering session, and the expander written in FX-26 where its
    /// session's namespace has not the transformer, which it may not define
    /// there (`phase1::run_transformer`). This runtime's front end is its
    /// own, so a definition here, inside a parse of another's, is apart.
    static SESSION: RefCell<Option<(crate::session::Fx26Session, fixpt_hash::HashMap<u64, crate::phase1::Phase1>)>> = RefCell::new(None);
}

/// A transformer's key in a namespace: its style and text.
pub(crate) fn key(style: Style, code: &str) -> String {
    format!("{style:?}\n{code}")
}

/// `f` of the transformers' session's runtime and its namespace of the
/// phase-1 forms `forms` (one for each list of them, its forms defined in
/// it: `phase1::Phase1::with_forms`), made at the first; apart from the
/// session whose check or run asks (`crossing::apart`).
fn with_session<T>(forms: &[String], f: impl FnOnce(&mut fixpt_runtime::Runtime, &crate::phase1::Phase1) -> Result<T, String>) -> Result<T, String> {
    fixpt_runtime::crossing::apart(|| {
        SESSION.with(|s| {
            let mut s = s.borrow_mut();
            if s.is_none() {
                let mut made = crate::session::Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).map_err(|e| e.message)?;
                made.strategy = crate::session::Strategy::Cellular;
                // Its front end loaded and the standard environment read,
                // which each namespace is made of.
                made.phase1().map_err(|e| format!("the transformers' namespace: {}", e.message))?.end(made.scheme.runtime_unrooted());
                *s = Some((made, fixpt_hash::HashMap::default()));
            }
            let (session, spaces) = s.as_mut().expect("made");
            let rt = session.scheme.runtime_unrooted();
            let digest = crate::phase1::forms_digest(forms);
            if !spaces.contains_key(&digest) {
                let p = crate::phase1::Phase1::with_forms(rt, forms)?;
                spaces.insert(digest, p);
            }
            f(rt, &spaces[&digest])
        })
    })
}

/// Transformer `code`, of `style`, defined in the transformers' session
/// where its macro is defined: checked at its style's type and compiled,
/// once; its global. Both front ends define each macro, and agree; a
/// session's checker defines its in its own namespace instead
/// (`Macros::define_procedural`).
pub(crate) fn define(style: Style, code: &str, forms: &[String]) -> Result<String, String> {
    with_session(forms, |rt, p| p.transformer(rt, style.ty(), &key(style, code), &helpers(code)))
}

/// Phase-1 forms `forms` checked, compiled and run in the transformers'
/// session, in a namespace of theirs (`Macros::for_syntax`).
pub(crate) fn with_forms_checked(forms: &[String]) -> Result<(), String> {
    with_session(forms, |_, _| Ok(()))
}

/// Transformer `code`, of `style`, called in the transformers' session on
/// datum `v` of `heap`, copied there, in expansion `made`, in its namespace
/// of the phase-1 forms `forms` in force where it was defined: what it gave,
/// copied into `heap` (`heap_syn::copy_datum`), no text between; or why
/// not. Defined there if it is not, as in a session made since.
pub(crate) fn apply_copied(style: Style, code: &str, forms: &[String], tag: &str, heap: &mut fixpt_heap::Heap, v: fixpt_heap::Value) -> Result<fixpt_heap::Value, String> {
    let out = with_session(forms, |rt, p| {
        let d = crate::heap_syn::copy_datum(heap, v, &mut rt.heap)?;
        let base = rt.heap.push_root(d);
        let g = p.transformer(rt, style.ty(), &key(style, code), &helpers(code));
        let d = rt.heap.root_at(base);
        rt.heap.pop_roots_to(base);
        let out = crate::phase1::call_transformer(rt, p, &g?, style, d, tag)?;
        crate::heap_syn::copy_datum(&rt.heap, out, heap)
    });
    out
}

/// What the expander written in FX-26 asks, through the runtime (only
/// where no namespace answers it: the evaluator's, `%macros:call-procedural`
/// answering `apart` there): `%define STYLE N\n`, N phase-1 forms each as
/// `LENGTH\n` and its text, and then a transformer's text, to `define`; or
/// `%apply STYLE MADE LENGTH N\n`, the N forms so, and then the
/// transformer's text, `LENGTH` characters, and the form's, to run it on
/// the form read in the transformers' session, its answer written.
fn asked(request: &str) -> Result<String, String> {
    let style_of = |n: usize| match n {
        0 => Style::Er,
        1 => Style::Sc,
        _ => Style::Rsc,
    };
    // `n` forms, each its length in characters on a line of its own and its
    // text, at the start of `body`: them, and what is after.
    let forms_of = |n: usize, mut body: &str| -> Result<(Vec<String>, String), String> {
        let mut forms = Vec::new();
        for _ in 0..n {
            let (len, rest) = body.split_once('\n').ok_or("a malformed transformer request")?;
            let len = len.parse::<usize>().map_err(|_| "a malformed transformer request")?;
            let split = rest.char_indices().nth(len).map_or(rest.len(), |(i, _)| i);
            forms.push(rest[..split].to_string());
            body = &rest[split..];
        }
        Ok((forms, body.to_string()))
    };
    // `%forms N\n` and N phase-1 forms: checked, compiled and run in their
    // namespace (`for-syntax!`, the expander written in FX-26's).
    if let Some(rest) = request.strip_prefix("%forms ") {
        let (head, body) = rest.split_once('\n').ok_or("a malformed transformer request")?;
        let n = head.parse::<usize>().map_err(|_| "a malformed transformer request")?;
        let (forms, _) = forms_of(n, body)?;
        return with_forms_checked(&forms).map(|_| "#u".to_string());
    }
    if let Some(rest) = request.strip_prefix("%define ") {
        let (head, body) = rest.split_once('\n').ok_or("a malformed transformer request")?;
        let mut words = head.split(' ').map(|w| w.parse::<usize>());
        let (Some(Ok(style)), Some(Ok(n))) = (words.next(), words.next()) else {
            return Err("a malformed transformer request".into());
        };
        let (forms, code) = forms_of(n, body)?;
        return define(style_of(style), &code, &forms).map(|_| "#u".to_string());
    }
    let Some(rest) = request.strip_prefix("%apply ") else { return Err("not a transformer request".into()) };
    let (head, body) = rest.split_once('\n').ok_or("a malformed transformer request")?;
    // Its style, the expansion's tag (`K.N`), its code's length, how many
    // phase-1 forms.
    let mut words = head.split(' ');
    let mut number = || words.next().map(|w| w.parse::<usize>());
    let style = number();
    let made = words.next().map(str::to_string);
    let mut number = || words.next().map(|w| w.parse::<usize>());
    let (Some(Ok(style)), Some(made), Some(Ok(length)), Some(Ok(n))) = (style, made, number(), number()) else {
        return Err("a malformed transformer request".into());
    };
    let (forms, body) = forms_of(n, body)?;
    let body = body.as_str();
    let style = style_of(style);
    let split = body.char_indices().nth(length).map_or(body.len(), |(i, _)| i);
    let (code, form) = (&body[..split], &body[split..]);
    with_session(&forms, |rt, p| {
        let mut interner = std::mem::take(&mut rt.interner);
        let read = fixpt_read::Reader::new(form, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX26, &mut interner).read();
        rt.interner = interner;
        let d = match read {
            Ok(Some(d)) => fixpt_runtime::port::syntax_to_value(rt, &d),
            _ => return Err("the form is not read".into()),
        };
        let base = rt.heap.push_root(d);
        let g = p.transformer(rt, style.ty(), &key(style, code), &helpers(code));
        let d = rt.heap.root_at(base);
        rt.heap.pop_roots_to(base);
        let out = crate::phase1::call_transformer(rt, p, &g?, style, d, &made)?;
        Ok(fixpt_runtime::write_value(&rt.heap, out))
    })
}

/// `asked` made what the runtime's syscall for the expander written in
/// FX-26 calls (`fixpt_runtime::syscall::PROCEDURAL`).
pub fn install() {
    let _ = fixpt_runtime::syscall::PROCEDURAL.set(asked);
}

/// `code` with the prelude's procedures bound around it, as locals.
pub(crate) fn helpers(code: &str) -> String {
    format!(
        "(let ((make-syntactic-closure %make-syntactic-closure) (identifier? %identifier?) (identifier=? %identifier=?)) {code})"
    )
}


/// `x`'s name as where its alias's macro was defined, if `x` is an alias:
/// every `%~K.N:` taken off.
pub fn alias_base(x: &str) -> Option<&str> {
    let mut s = x;
    let mut any = false;
    while let Some(rest) = s.strip_prefix("%~") {
        let Some(c) = rest.find(':') else { break };
        if c == 0 || !rest[..c].bytes().all(tag_byte) {
            break;
        }
        s = &rest[c + 1..];
        any = true;
    }
    any.then_some(s)
}

/// Whether `b` may be in an expansion's tag, `K.N` (`Macros::expansion_begun`):
/// a form's key, `H`, `H-1` or `mH`, and a count.
fn tag_byte(b: u8) -> bool {
    b.is_ascii_digit() || matches!(b, b'.' | b'-' | b'm')
}

/// The tag of the expansion that made alias `x`, its outermost `%~T:`'s
/// `T`.
pub(crate) fn alias_made(x: &str) -> Option<&str> {
    let rest = x.strip_prefix("%~")?;
    let t = &rest[..rest.find(':')?];
    (!t.is_empty() && t.bytes().all(tag_byte)).then_some(t)
}

/// `x`'s alias, made by the expansion of tag `tag`.
pub(crate) fn alias(x: &str, tag: &str) -> String {
    format!("%~{tag}:{x}")
}

/// What a syntactic-closure transformer gave, `s`, its closures opened: in
/// environment `macro_env` (else the use's), each name an alias (expansion
/// of tag `tag`) or as written; a closure's form in its own environment, its
/// free names in the one around it; a quoted datum as it is.
pub(crate) fn closed(s: &Syn, macro_env: bool, tag: &str, interner: &mut Interner) -> R<Syn> {
    match &s.view() {
        V::Symbol(x) if macro_env => {
            let n = alias(interner.name(*x), tag);
            Ok(Syn::named(s.at(), &n, interner))
        }
        V::List { items, tail } => {
            let head = items.first().and_then(|h| h.sym()).map(|h| interner.name(h).to_string());
            if head.as_deref() == Some("quote") {
                return Ok(s.clone());
            }
            if head.as_deref() == Some(CLOSURE) {
                let [_, env, free, form] = &items[..] else {
                    return Err(FxError::at(s.at(), "a syntactic closure is `(%sc env (free …) form)`"));
                };
                let inner = match env.sym().map(|e| interner.name(e)) {
                    Some(USE_ENV) => false,
                    Some(MACRO_ENV) => true,
                    _ => return Err(FxError::at(env.at(), "a syntactic closure's environment is one a transformer was given")),
                };
                let free: Vec<Sym> = match &free.view() {
                    V::Nil => Vec::new(),
                    _ => free.list().and_then(|l| l.iter().map(|x| x.sym()).collect()).ok_or_else(|| FxError::at(free.at(), "a syntactic closure's free names are a list of names"))?,
                };
                return opened(form, inner, macro_env, &free, tag, interner);
            }
            let items = items.iter().map(|i| closed(i, macro_env, tag, interner)).collect::<R<Vec<_>>>()?;
            let tail = match tail {
                Some(t) => Some(closed(t, macro_env, tag, interner)?),
                None => None,
            };
            Ok(Syn::of_list(s.at(), &items, tail))
        }
        _ => Ok(s.clone()),
    }
}

/// A closure's form, `s`, closed in environment `inner`, its `free` names
/// in `outer`.
fn opened(s: &Syn, inner: bool, outer: bool, free: &[Sym], tag: &str, interner: &mut Interner) -> R<Syn> {
    match &s.view() {
        V::Symbol(x) if free.contains(x) => closed(s, outer, tag, interner),
        V::Symbol(_) => closed(s, inner, tag, interner),
        V::List { items, tail } => {
            let head = items.first().and_then(|h| h.sym()).map(|h| interner.name(h).to_string());
            if matches!(head.as_deref(), Some("quote") | Some(CLOSURE)) {
                return closed(s, inner, tag, interner);
            }
            let items = items.iter().map(|i| opened(i, inner, outer, free, tag, interner)).collect::<R<Vec<_>>>()?;
            let tail = match tail {
                Some(t) => Some(opened(t, inner, outer, free, tag, interner)?),
                None => None,
            };
            Ok(Syn::of_list(s.at(), &items, tail))
        }
        _ => Ok(s.clone()),
    }
}

/// What a transformer gave, `s`, each alias that is a keyword's name made
/// the keyword (`is_keyword`: a form's, a description's word, a macro's),
/// which nothing binds, so nothing could capture; and every alias quoted
/// made its name, a symbol as data.
pub(crate) fn keywords(s: &Syn, is_keyword: &dyn Fn(&str) -> bool, interner: &mut Interner) -> Syn {
    match &s.view() {
        V::Symbol(x) => match alias_base(interner.name(*x)) {
            Some(b) if is_keyword(b) => {
                let b = b.to_string();
                Syn::named(s.at(), &b, interner)
            }
            _ => s.clone(),
        },
        V::List { items, tail } => {
            let quoted = items.first().and_then(|h| h.sym()).is_some_and(|h| {
                let n = interner.name(h);
                matches!(n, "quote" | "quasiquote") || alias_base(n).is_some_and(|b| matches!(b, "quote" | "quasiquote"))
            });
            if quoted {
                return Syn::of_list(s.at(), &items.iter().map(|i| unaliased(i, interner)).collect::<Vec<_>>(), tail.as_ref().map(|t| unaliased(t, interner)));
            }
            Syn::of_list(s.at(), &items.iter().map(|i| keywords(i, is_keyword, interner)).collect::<Vec<_>>(), tail.as_ref().map(|t| keywords(t, is_keyword, interner)))
        }
        V::Vector(xs) => Syn::vector(s.at(), &xs.iter().map(|i| keywords(i, is_keyword, interner)).collect::<Vec<_>>()),
        _ => s.clone(),
    }
}

/// `s` with every alias its name.
fn unaliased(s: &Syn, interner: &mut Interner) -> Syn {
    match &s.view() {
        V::Symbol(x) => match alias_base(interner.name(*x)) {
            Some(b) => {
                let b = b.to_string();
                Syn::named(s.at(), &b, interner)
            }
            None => s.clone(),
        },
        V::List { items, tail } => {
            Syn::of_list(s.at(), &items.iter().map(|i| unaliased(i, interner)).collect::<Vec<_>>(), tail.as_ref().map(|t| unaliased(t, interner)))
        }
        V::Vector(xs) => Syn::vector(s.at(), &xs.iter().map(|i| unaliased(i, interner)).collect::<Vec<_>>()),
        _ => s.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::{alias_base, alias_made};

    #[test]
    fn an_alias_is_its_base_name_marked() {
        assert_eq!(alias_base("%~3:let"), Some("let"));
        assert_eq!(alias_base("%~7:%~3:x"), Some("x"));
        assert_eq!(alias_base("let"), None);
        assert_eq!(alias_base("%x:3"), None);
        assert_eq!(alias_base("%~:x"), None);
        assert_eq!(alias_made("%~7:%~3:x"), Some("7"));
        assert_eq!(alias_base("%~m12-1.4:%~5.2:x"), Some("x"));
        assert_eq!(alias_made("%~m12-1.4:%~5.2:x"), Some("m12-1.4"));
        assert_eq!(alias_made("x"), None);
    }
}
