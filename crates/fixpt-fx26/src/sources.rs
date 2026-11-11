//! Where compiled code came from, for a debugger's lines
//! (`fixpt_native::jitdebug`): each text a session compiles is a source,
//! numbered (`fixpt_heap::regcode::set_source`), and a register word made
//! from it says, by that number, where each expression's code starts (a
//! place, as the compilers' `place_of`: a character in the text compiled,
//! or past a billion times a module file's number, in that file).
//!
//! The text compiled is written from the program's syntax, often inside
//! more (`(lambda () …)`, `(the T …)`): so a source keeps the form it was
//! written from, as written, with where each datum went
//! (`fixpt_read::write_syntax_mapped`); a place is found in the form's text
//! in the text compiled, and so the datum it is in, and the datum's span
//! where it was read: in the file the session runs, or a module file it
//! loaded. Kept per thread: the session's, which also makes the
//! debugger's objects (`jitdebug::flush`).

use fixpt_read::{FileId, Span};
use std::cell::RefCell;
use std::rc::Rc;

/// A file, as a source's places are found in it: its name and text.
pub type File = Rc<(String, String)>;

/// A text compiled: it, the form written into it and where each datum
/// went, the file the session runs, and the module files it had loaded.
struct Source {
    text: String,
    form: Option<(String, Vec<(usize, usize, Span)>)>,
    file: Option<File>,
    loaded: Vec<(FileId, File)>,
    /// Where the form's text starts in the text compiled, once found.
    base: std::cell::OnceCell<Option<i64>>,
}

thread_local! {
    static SOURCES: RefCell<Vec<Source>> = const { RefCell::new(Vec::new()) };
}

/// Whether sources are kept: a driver says so, when a debugger may ask.
static WANTED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Sources kept from now on (`register`).
pub fn want() {
    WANTED.store(true, std::sync::atomic::Ordering::Relaxed);
}

pub fn wanted() -> bool {
    WANTED.load(std::sync::atomic::Ordering::Relaxed)
}

/// Numbers below this are no source of this registry's (0: none).
const FIRST: u32 = 2;

/// `text`, about to be compiled, as a source: its number, for
/// `set_source`. A driver that runs native code tells `jitdebug` of
/// [`resolve`].
pub fn register(text: &str, form: Option<(String, Vec<(usize, usize, Span)>)>, file: Option<File>, loaded: Vec<(FileId, File)>) -> u32 {
    SOURCES.with(|s| {
        let mut s = s.borrow_mut();
        s.push(Source { text: text.to_string(), form, file, loaded, base: std::cell::OnceCell::new() });
        s.len() as u32 - 1 + FIRST
    })
}

/// The file and line of `place` in source `id`, if known; a datum a
/// macro made, at its use in a text as written, the outermost
/// (`docs/research/macro-provenance.md`), not its template.
pub fn resolve(id: u32, place: i64) -> Option<(String, u32)> {
    if place < 0 || id < FIRST {
        return None;
    }
    SOURCES.with(|s| {
        let s = s.borrow();
        let src = s.get((id - FIRST) as usize)?;
        // In a module file: its character.
        if place >= 1_000_000_000 {
            let (k, ch) = (place / 1_000_000_000, (place % 1_000_000_000) as usize);
            let f = &src.loaded.iter().find(|(id, _)| id.0 as i64 == 1000 + k)?.1;
            return Some((f.0.clone(), line_of_char(&f.1, ch)));
        }
        let span = datum_span(src, place)?;
        let span = match fixpt_read::expansion_trace(span).last() {
            Some(e) => e.at,
            None => span,
        };
        span_line(src, span)
    })
}

/// What made the code at `place` in source `id`, if a macro did: its
/// template's file and line, then each use's, out, as `fixpt_place_at`
/// says a provenance (`jitdebug::set_describer`); none if no macro did.
pub fn describe(id: u32, place: i64) -> Option<String> {
    if !(0..1_000_000_000).contains(&place) || id < FIRST {
        return None;
    }
    SOURCES.with(|s| {
        let s = s.borrow();
        let src = s.get((id - FIRST) as usize)?;
        let span = datum_span(src, place)?;
        let trace = fixpt_read::expansion_trace(span);
        if trace.is_empty() {
            return None;
        }
        let at = |sp: Span| span_line(src, sp).map_or_else(|| "where not known".to_string(), |(f, l)| format!("{f}:{l}"));
        let mut out = format!("made by a macro: template {}", at(span));
        for e in &trace {
            out.push_str(&format!(", used at {}", at(e.at)));
        }
        Some(out)
    })
}

/// The span of the innermost datum of source `src`'s form at character
/// `place` of its text.
fn datum_span(src: &Source, place: i64) -> Option<Span> {
    let byte = src.text.char_indices().nth(place as usize).map_or(src.text.len(), |(b, _)| b);
    let (form, map) = src.form.as_ref()?;
    // Where the form is in the text: the form itself, else the largest
    // list of it found there (a definition's value, inside `the`).
    let base = (*src.base.get_or_init(|| {
        let mut lists: Vec<(usize, usize)> = map.iter().filter(|&&(a, _, _)| form[a..].starts_with('(')).map(|&(a, b, _)| (a, b)).collect();
        lists.sort_by_key(|&(a, b)| std::cmp::Reverse(b - a));
        lists.iter().find_map(|&(a, b)| src.text.find(&form[a..b]).map(|at| at as i64 - a as i64))
    }))?;
    let at = byte as i64 - base;
    // The innermost datum that starts there or before and holds it.
    let &(_, _, span) = map.iter().filter(|&&(a, b, _)| a as i64 <= at && at < b as i64).max_by_key(|&&(a, _, _)| a)?;
    Some(span)
}

/// The file and line where `span` starts, in source `src`'s files.
fn span_line(src: &Source, span: Span) -> Option<(String, u32)> {
    let file = if span.file == FileId(0) { src.file.as_ref()? } else { &src.loaded.iter().find(|(id, _)| *id == span.file)?.1 };
    Some((file.0.clone(), line_of_byte(&file.1, span.start as usize)))
}

fn line_of_byte(text: &str, byte: usize) -> u32 {
    text.as_bytes()[..byte.min(text.len())].iter().filter(|&&b| b == b'\n').count() as u32 + 1
}

fn line_of_char(text: &str, ch: usize) -> u32 {
    let byte = text.char_indices().nth(ch).map_or(text.len(), |(b, _)| b);
    line_of_byte(text, byte)
}
