//! Where compiled code came from, for a debugger's lines
//! (`fixpt_native::jitdebug`): a session's texts are a source, numbered
//! (`fixpt_heap::regcode::set_source`), and a register word made in it
//! says, by that number, where each expression's code starts: a place, as
//! the compilers' `place_of` and the syntax handed to the front end written
//! in FX-26 have it (`docs/research/heap-syntax.md`), a character past its
//! file's base (the program's text from 0, a module file's past a billion
//! times its number); or a provenance's id, a macro's code's, which
//! `jitdebug` takes to its use's place itself (`note_chain`). Kept per
//! thread: the session's, which also makes the debugger's objects
//! (`jitdebug::flush`).

use fixpt_read::FileId;
use std::cell::RefCell;
use std::rc::Rc;

/// A file, as a source's places are found in it: its name and text.
pub type File = Rc<(String, String)>;

/// A session's texts: the file it runs, and the module files it had loaded.
struct Source {
    file: Option<File>,
    loaded: Vec<(FileId, File)>,
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

/// The texts code about to be compiled is placed in, as a source: its
/// number, for `set_source`; the last one's, if they are the same texts. A
/// driver that runs native code tells `jitdebug` of [`resolve`].
pub fn register(file: Option<File>, loaded: Vec<(FileId, File)>) -> u32 {
    SOURCES.with(|s| {
        let mut s = s.borrow_mut();
        let same = |src: &Source| {
            src.file.as_ref().map(Rc::as_ptr) == file.as_ref().map(Rc::as_ptr)
                && src.loaded.len() == loaded.len()
                && src.loaded.iter().zip(&loaded).all(|(a, b)| a.0 == b.0 && Rc::ptr_eq(&a.1, &b.1))
        };
        if !s.last().is_some_and(same) {
            s.push(Source { file, loaded });
        }
        s.len() as u32 - 1 + FIRST
    })
}

/// The file and line of `place` in source `id`, if known.
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
        let f = src.file.as_ref()?;
        Some((f.0.clone(), line_of_char(&f.1, place as usize)))
    })
}

fn line_of_char(text: &str, ch: usize) -> u32 {
    let byte = text.char_indices().nth(ch).map_or(text.len(), |(b, _)| b);
    text.as_bytes()[..byte].iter().filter(|&&b| b == b'\n').count() as u32 + 1
}
