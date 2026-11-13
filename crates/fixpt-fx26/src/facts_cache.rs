//! What the checker written in Rust finds of a text, for the compiler
//! written in FX-26 (`syn::rust_facts_in`), kept: a minute and more of a
//! debug build's checking, the same each time the same text is compiled
//! (the front end's, the bootstrap program's, by many tests and the
//! prewarm). Kept as the facts found ([`FormFacts`], plain data: each
//! expression's, by where it is, ground), not as heap values, in the cache
//! directory (`fasl::cache_dir`), keyed by all a check depends on: the
//! text, its convention, whether a runtime's, the facts' keys
//! (`ids::mode`), and the build (`FIXPT_BUILD_HASH`, the module files built
//! in among its sources). Only of a check that read nothing from disk
//! (`reads`), so that nothing else can have changed what it found; none
//! with `FIXPT_NO_CACHE`, as for the front end's own caches.

use crate::rust_facts::FormFacts;
use std::path::PathBuf;

/// Where the facts of `text`, so checked, are kept, if anywhere.
fn path(text: &str, conv: crate::ast::Conv, syscalls: bool) -> Option<PathBuf> {
    use std::hash::{Hash, Hasher};
    if std::env::var_os("FIXPT_NO_CACHE").is_some() {
        return None;
    }
    let mut key = std::collections::hash_map::DefaultHasher::new();
    (env!("FIXPT_BUILD_HASH"), text, format!("{conv:?}"), syscalls, crate::ids::mode() as i64).hash(&mut key);
    let dir = crate::fasl::cache_dir()?;
    std::fs::create_dir_all(&dir).ok()?;
    Some(dir.join(format!("facts-{:016x}.bin", key.finish())))
}

/// The facts of `text`, checked so: read back if kept, else found by
/// `check` and, if it read nothing from disk, kept.
pub(crate) fn found(text: &str, conv: crate::ast::Conv, syscalls: bool, check: impl FnOnce() -> crate::R<FormFacts>) -> crate::R<FormFacts> {
    let at = path(text, conv, syscalls);
    if let Some(found) = at.as_ref().and_then(|p| std::fs::read(p).ok()).and_then(|b| FormFacts::from_bytes(&b)) {
        return Ok(found);
    }
    let reads = crate::reads::count();
    let found = check()?;
    if let Some(at) = at
        && crate::reads::count() == reads
    {
        let tmp = at.with_extension(format!("tmp{}", std::process::id()));
        if std::fs::write(&tmp, found.to_bytes()).is_ok() && std::fs::rename(&tmp, &at).is_ok() {
            crate::session::note_made(&at);
        }
        sweep(&at);
    }
    Ok(found)
}

/// Those of other builds, unused for a day, let go.
fn sweep(kept: &std::path::Path) {
    let day = std::time::Duration::from_secs(24 * 3600);
    let Some(dir) = kept.parent() else { return };
    for e in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let old = e.metadata().and_then(|m| m.modified()).ok().and_then(|t| t.elapsed().ok()).is_some_and(|a| a > day);
        if old && e.file_name().to_string_lossy().starts_with("facts-") {
            let _ = std::fs::remove_file(e.path());
        }
    }
}
