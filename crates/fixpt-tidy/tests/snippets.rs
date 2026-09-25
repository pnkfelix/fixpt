//! No long Scheme or FX programs inside Rust string literals: see the crate
//! documentation for the rule and why.

use std::path::Path;

#[test]
fn no_long_snippets_are_embedded_in_rust() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let crates = root.join("crates");
    let mut found = Vec::new();
    for file in fixpt_tidy::rust_files(&crates) {
        let src = std::fs::read_to_string(&file).expect("readable");
        let rel = file.strip_prefix(&root).unwrap_or(&file);
        found.extend(fixpt_tidy::check_source(rel, &src));
    }
    let report: Vec<String> = found.iter().map(ToString::to_string).collect();
    assert!(
        found.is_empty(),
        "{} snippets are too long to embed; move each to a file beside its test and \
         `include_str!` it:\n{}",
        found.len(),
        report.join("\n")
    );
}
