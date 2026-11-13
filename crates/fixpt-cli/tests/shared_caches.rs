//! A debug and a release build of the same sources share their caches
//! (`TODO.md` §265): the build hash that names and keys them leaves out the
//! profile (`fixpt-fx26/build.rs`), so either reads what the other's
//! `fixpt prewarm` made. Sound only while the two make the same bytes:
//! here, a prewarm made afresh, in a cache of its own, compared file by
//! file with the shared cache, where the other profile's prewarm made that
//! (`prewarm-BUILD.made-by`). Where this profile's made it, nothing is
//! compared: the other's suite compares, before a push runs both. As the
//! suites' steps go, a debug prewarm first, a release build compares (some
//! 12 s); a release suite alone first, the debug one (some 80 s).

use std::path::Path;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

#[test]
fn a_debug_and_a_release_prewarm_make_the_same_caches() {
    let shared = fixpt_fx26::fasl::cache_dir().expect("a cache directory");
    let build = fixpt_fx26::session::build_hash();
    let marker = shared.join(format!("prewarm-{build}.made-by"));
    let made_by = std::fs::read_to_string(&marker).unwrap_or_else(|e| panic!("{}: {e}: no prewarm made this build's caches", marker.display()));
    let profile = if cfg!(debug_assertions) { "debug" } else { "release" };
    // Made by this profile's: the other's suite compares.
    if made_by == profile {
        return;
    }
    // This profile's prewarm of the same sources, in a cache of its own.
    let own = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("shared-caches-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&own);
    std::fs::create_dir_all(&own).expect("made");
    let out = std::process::Command::new(FIXPT).arg("prewarm").env("XDG_CACHE_HOME", &own).output().expect("fixpt runs");
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let made = own.join("fixpt");
    let mut files: Vec<_> = std::fs::read_dir(&made).expect("its cache").flatten().map(|e| e.file_name()).collect();
    files.sort();
    let mut differ = Vec::new();
    for name in &files {
        let n = name.to_string_lossy();
        // The marker says which made them, the lock files nothing.
        if n.ends_with(".made-by") || n.ends_with(".lock") {
            continue;
        }
        let mine = std::fs::read(made.join(name)).expect("readable");
        match std::fs::read(shared.join(name)) {
            Ok(theirs) if theirs == mine => {}
            Ok(theirs) => differ.push(format!("{n}: {} bytes here, {} there, first at byte {}", mine.len(), theirs.len(), mine.iter().zip(&theirs).position(|(a, b)| a != b).unwrap_or(mine.len().min(theirs.len())))),
            Err(e) => differ.push(format!("{n}: not in the shared cache ({e})")),
        }
    }
    assert!(files.len() >= 8, "a prewarm made only {files:?}");
    assert!(differ.is_empty(), "a {profile} prewarm made other caches than the {made_by} one did:\n{}", differ.join("\n"));
    let _ = std::fs::remove_dir_all(&own);
}
