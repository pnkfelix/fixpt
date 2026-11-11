//! The bootstrap program (`crate::bootstrap_program`) compiled by the
//! compiler written in FX-26 to one cellular word, with register code or
//! not: what the tests of the native compilers compare word by word. The
//! compile is a minute and more in a debug build, the same in each of
//! them, so it is kept: the word copied into a heap of its own and written
//! as an image in the cache directory (`fasl::cache_dir`, the front end's),
//! keyed by the sources (`FIXPT_BUILD_HASH`), the program and whether it
//! has register code, and read back by the next. `fixpt prewarm` makes both
//! before a run of the tests, so that none of them waits on it (`TODO.md`
//! §167, item 4); a lock on the file makes one compile while the others
//! wait, if none did.

use fixpt_heap::{Heap, Value};
use fixpt_read::FileId;
use std::path::PathBuf;

/// Where the image of the compile is kept, if anywhere: none with
/// `FIXPT_NO_CACHE`, as for the front end's own caches.
fn image_path(registers: bool) -> Option<PathBuf> {
    use std::hash::{Hash, Hasher};
    if std::env::var_os("FIXPT_NO_CACHE").is_some() {
        return None;
    }
    let mut key = std::collections::hash_map::DefaultHasher::new();
    (env!("FIXPT_BUILD_HASH"), crate::bootstrap_program(), registers).hash(&mut key);
    let dir = crate::fasl::cache_dir()?;
    std::fs::create_dir_all(&dir).ok()?;
    Some(dir.join(format!("bootstrap-compiled-{:016x}.img", key.finish())))
}

/// The compile, in `sc`'s heap: read from its image if one is kept, else
/// made (and kept). `sc` is a session with the pieces written in FX-26
/// loaded (`Fx26Session::load_own_pieces`).
pub fn bootstrap_compiled(sc: &mut fixpt_scheme::Session, registers: bool) -> fixpt_scheme::Handle {
    let Some(path) = image_path(registers) else { return compiled(sc, registers) };
    let lock = std::fs::File::create(path.with_extension("lock")).expect("a lock file");
    lock.lock().expect("locked");
    if let Ok(bytes) = std::fs::read(&path)
        && let Ok(from) = fixpt_heap::image::load_trusted(&bytes)
    {
        let root = from.roots_slice()[0];
        return sc.make(|m| m.heap().copy_graph_from(&from, root));
    }
    let word = compiled(sc, registers);
    sc.make(|m| {
        let mut alone = Heap::new();
        let w = m.get(word);
        let copy = alone.copy_graph_from(m.heap(), w);
        alone.push_root(copy);
        let tmp = path.with_extension(format!("tmp{}", std::process::id()));
        if std::fs::write(&tmp, fixpt_heap::image::dump_packed(&alone)).is_ok() {
            let _ = std::fs::rename(&tmp, &path);
        }
        Value::NULL
    });
    // Those of other builds, unused for a day, let go.
    let day = std::time::Duration::from_secs(24 * 3600);
    if let Some(dir) = path.parent() {
        for e in std::fs::read_dir(dir).into_iter().flatten().flatten() {
            let old = e.metadata().and_then(|m| m.modified()).ok().and_then(|t| t.elapsed().ok()).is_some_and(|a| a > day);
            if old && e.file_name().to_string_lossy().starts_with("bootstrap-compiled-") {
                let _ = std::fs::remove_file(e.path());
            }
        }
    }
    word
}

/// The compile itself.
fn compiled(sc: &mut fixpt_scheme::Session, registers: bool) -> fixpt_scheme::Handle {
    let text = crate::bootstrap_program();
    let facts = crate::syn::rust_facts(sc, FileId(0), &text).expect("checks");
    let compile = if registers { crate::syn::compile_to_word_with_registers } else { crate::syn::compile_to_word };
    compile(sc, FileId(0), &text, facts).expect("parses").expect("compiles")
}

/// Both compiles kept now (`fixpt prewarm`), each in a session of its own
/// made as the tests make theirs (`tests/common`'s `front_end_session`),
/// at once: how long each took, or why it failed.
pub fn prewarm() -> Vec<(bool, Result<f64, String>)> {
    std::thread::scope(|s| {
        let each: Vec<_> = [false, true]
            .into_iter()
            .map(|registers| {
                s.spawn(move || {
                    let started = std::time::Instant::now();
                    let mut f = crate::session::Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).map_err(|e| e.to_string())?;
                    f.scheme.runtime_unrooted().front_end_run_word =
                        Some(if fixpt_native::CELLULAR_AVAILABLE { fixpt_native::cellular::run_word_registers } else { fixpt_engine::cellular::run_word });
                    f.front_end_compiled = true;
                    f.load_own_pieces().map_err(|e| e.to_string())?;
                    f.scheme.engine.set_step_limit(None);
                    f.scheme.scope(|sc| {
                        bootstrap_compiled(sc, registers);
                    });
                    Ok(started.elapsed().as_secs_f64())
                })
            })
            .collect();
        [false, true].into_iter().zip(each).map(|(r, h)| (r, h.join().unwrap_or_else(|_| Err("panicked".to_string())))).collect()
    })
}
