//! The checker written in Rust reads from disk only through
//! `fixpt_fx26::reads`, which counts each read: what a check found is kept
//! (`facts_cache`) only if it read nothing, so a read past it would let a
//! changed file go unseen. In the checker's files, before their tests: no
//! file read but by `reads::read_file`, and a mapped file opened only just
//! after `reads::note()`.

use std::path::Path;

/// The files the checker's code is in: whatever a check may run.
const CHECKER: &[&str] = &[
    "parse.rs", "top.rs", "check.rs", "infer.rs", "modules.rs", "modorder.rs", "kinds.rs", "sizes.rs", "specs.rs", "convention.rs",
    "syscall.rs", "ids.rs", "rust_facts.rs", "fasl.rs", "syn.rs", "lemma.rs", "logic.rs",
];

#[test]
fn the_checker_reads_only_through_reads() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("../fixpt-fx26/src");
    let mut files: Vec<_> = CHECKER.iter().map(|f| src.join(f)).collect();
    files.extend(std::fs::read_dir(src.join("macros")).expect("the macros' directory").flatten().map(|e| e.path()));
    let mut found = Vec::new();
    for path in files.iter().filter(|p| p.extension().is_some_and(|e| e == "rs")) {
        let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let mut before = "";
        for (n, line) in text.lines().enumerate() {
            if line.trim_start().starts_with("#[cfg(test)]") {
                break;
            }
            let read = ["fs::read(", "read_to_string(", "File::open(", "read_dir("].iter().any(|r| line.contains(r));
            let mapped = line.contains("Mapped::open(") && !before.contains("reads::note()");
            if read || mapped {
                found.push(format!("{}:{}: {}", path.display(), n + 1, line.trim()));
            }
            before = line;
        }
    }
    assert!(found.is_empty(), "reads past `reads`:\n{}", found.join("\n"));
}
