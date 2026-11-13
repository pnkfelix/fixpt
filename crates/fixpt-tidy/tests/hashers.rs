//! No hash map or set is seeded (`fixpt-hash`): iterated, a seeded one
//! goes in an order of each process's own, and what is made of that order
//! (an image's lists, the order code is compiled in) with it, so that two
//! runs of a build, or a debug and a release build, made different caches
//! of the same sources. Each is `fixpt_hash`'s, or names a hasher of its own
//! (`WordHasher`, `IdHasher`) where it names the standard type; none is the
//! standard one's `RandomState`.

use std::path::{Path, PathBuf};

fn sources(dir: &Path, out: &mut Vec<PathBuf>) {
    for e in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())).flatten() {
        let p = e.path();
        if p.is_dir() {
            sources(&p, out);
        } else if p.extension().is_some_and(|x| x == "rs") {
            out.push(p);
        }
    }
}

#[test]
fn no_hash_map_is_seeded() {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut files = Vec::new();
    sources(&crates, &mut files);
    let mut found = Vec::new();
    // The standard types by their paths, alone or among a `use`'s.
    let standard = |code: &str| {
        let mut rest = code;
        while let Some(at) = rest.find("std::collections::") {
            rest = &rest[at + "std::collections::".len()..];
            let named = if rest.starts_with('{') { &rest[..rest.find('}').unwrap_or(rest.len())] } else { rest };
            let word = |w: &str| named.starts_with(w) || named.contains(&format!(" {w}")) || named.contains(&format!("{{{w}"));
            if word("HashMap") || word("HashSet") {
                return true;
            }
        }
        false
    };
    let this = Path::new(file!()).file_name().expect("a file");
    for path in files.iter().filter(|p| !p.components().any(|c| c.as_os_str() == "fixpt-hash" || c.as_os_str() == "target") && p.file_name() != Some(this)) {
        let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let mut before = "";
        for (n, line) in text.lines().enumerate() {
            let code = line.split("//").next().unwrap_or("");
            // One the line names its hasher of; `RandomState` only where a
            // comment just above says it is seeded on purpose (no map's).
            let seeded = (standard(code) && !code.contains("Hasher")) || (code.contains("RandomState") && !before.contains("Seeded on purpose"));
            if seeded {
                found.push(format!("{}:{}: {}", path.display(), n + 1, line.trim()));
            }
            before = line;
        }
    }
    assert!(found.is_empty(), "seeded hash maps (use `fixpt_hash`'s):\n{}", found.join("\n"));
}
