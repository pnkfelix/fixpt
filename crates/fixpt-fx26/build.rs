//! `cfg(optimized)`, for tests too slow without optimization: the ones that
//! run every word of the front end are ignored in an unoptimized build, and
//! run in an optimized one with debug assertions on (the `checked` profile)
//! as in release.
//!
//! `FIXPT_BUILD_HASH`: a hash of the sources of every crate that makes or
//! runs the front end's cache, and of the build (profile, target, features),
//! which keys the cache (`front_end_cache`), so that every executable built
//! from the same sources so shares one: the CLI and each test binary.

use std::hash::{Hash, Hasher};
use std::path::Path;

/// The crates the front end's image depends on, by their directories next to
/// this one, and what in each.
const CRATES: [&str; 8] = ["fixpt-read", "fixpt-heap", "fixpt-memmgmt", "fixpt-engine", "fixpt-runtime", "fixpt-scheme", "fixpt-native", "fixpt-fx26"];
const PARTS: [&str; 4] = ["src", "stencils", "build.rs", "Cargo.toml"];

fn main() {
    println!("cargo::rustc-check-cfg=cfg(optimized)");
    if std::env::var("OPT_LEVEL").is_ok_and(|o| o != "0") {
        println!("cargo::rustc-cfg=optimized");
    }
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("in crates/");
    let mut h = std::collections::hash_map::DefaultHasher::new();
    for c in CRATES {
        for part in PARTS {
            let p = crates.join(c).join(part);
            if p.exists() {
                println!("cargo::rerun-if-changed={}", p.display());
                hash_tree(&p, &mut h);
            }
        }
    }
    let lock = crates.parent().expect("a workspace").join("Cargo.lock");
    println!("cargo::rerun-if-changed={}", lock.display());
    hash_tree(&lock, &mut h);
    let mut build: Vec<_> = std::env::vars()
        .filter(|(k, _)| k.starts_with("CARGO_FEATURE_") || k.starts_with("CARGO_CFG_") || ["PROFILE", "OPT_LEVEL", "DEBUG", "TARGET"].contains(&k.as_str()))
        .collect();
    build.sort();
    build.hash(&mut h);
    println!("cargo::rustc-env=FIXPT_BUILD_HASH={:016x}", h.finish());
}

/// `p`'s name and contents, and a directory's entries' in order, into `h`.
fn hash_tree(p: &Path, h: &mut impl Hasher) {
    p.file_name().hash(h);
    if p.is_dir() {
        let mut entries: Vec<_> = std::fs::read_dir(p).expect("readable").map(|e| e.expect("an entry").path()).collect();
        entries.sort();
        for e in entries {
            hash_tree(&e, h);
        }
    } else {
        std::fs::read(p).expect("readable").hash(h);
    }
}
