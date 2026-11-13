//! A debug and a release build of the same sources share their caches
//! (`TODO.md` §265): the build hash that names and keys them leaves out the
//! profile (`fixpt-fx26/build.rs`), so either reads what the other made.
//! Sound only while the two make the same bytes: here, a prewarm made
//! afresh, in a cache of its own, compared file by file with each shared
//! cache the other profile made (`FILE.made-by`, written beside each as it
//! is written, `session::note_made`). Where this profile made them all,
//! nothing is compared: the other's suite compares, before a push runs
//! both. As the suites' steps go, a release prewarm first, the debug one
//! compares (some 80 s); a debug prewarm first, a release one (some 12 s).

use std::path::Path;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

#[test]
fn a_debug_and_a_release_prewarm_make_the_same_caches() {
    let shared = fixpt_fx26::fasl::cache_dir().expect("a cache directory");
    let profile = if cfg!(debug_assertions) { "debug" } else { "release" };
    // This profile's prewarm of the same sources, in a cache of its own: its
    // files by name, the same names as the shared cache's.
    let own = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("shared-caches-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&own);
    std::fs::create_dir_all(&own).expect("made");
    let made_by = |name: &str| std::fs::read_to_string(shared.join(format!("{name}.made-by"))).ok();
    // Nothing of this build's the other profile made (its front end's caches,
    // named for the build): nothing to compare, and no prewarm.
    let this = format!("front-end-{}-", fixpt_fx26::session::build_hash());
    let names = |dir: &Path| -> Vec<String> {
        let mut ns: Vec<String> = std::fs::read_dir(dir).into_iter().flatten().flatten().map(|e| e.file_name().to_string_lossy().into_owned()).collect();
        ns.retain(|n| !n.ends_with(".made-by") && !n.ends_with(".lock") && !n.contains(".tmp"));
        ns.sort();
        ns
    };
    if !names(&shared).iter().any(|n| n.starts_with(&this) && made_by(n).is_some_and(|m| m != profile)) {
        return;
    }
    let out = std::process::Command::new(FIXPT).arg("prewarm").env("XDG_CACHE_HOME", &own).output().expect("fixpt runs");
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let made = own.join("fixpt");
    let files = names(&made);
    assert!(files.len() >= 8, "a prewarm made only {files:?}");
    let (mut compared, mut differ) = (0, Vec::new());
    for n in &files {
        // Only what the other profile made: this profile's own is the
        // other suite's to compare.
        let Some(maker) = made_by(n).filter(|m| m != profile) else { continue };
        let mine = std::fs::read(made.join(n)).expect("readable");
        match std::fs::read(shared.join(n)) {
            Ok(theirs) if theirs == mine => compared += 1,
            Ok(theirs) => differ.push(format!("{n}, the {maker} build's: {} bytes here, {} there, first at byte {}", mine.len(), theirs.len(), mine.iter().zip(&theirs).position(|(a, b)| a != b).unwrap_or(mine.len().min(theirs.len())))),
            Err(e) => differ.push(format!("{n}: not readable in the shared cache ({e})")),
        }
    }
    assert!(differ.is_empty(), "a {profile} prewarm made other caches than the other profile did:\n{}", differ.join("\n"));
    assert!(compared > 0, "the other profile made caches, and none of them is one a prewarm makes");
    let _ = std::fs::remove_dir_all(&own);
}
