//! A bloblet's fields named by their layout, not by number, outside the
//! files allowed: see `fixpt_tidy::fields` for the rule and why.

use fixpt_tidy::fields::{findings, parse_allowed};
use fixpt_tidy::rust_files;
use std::path::Path;

#[test]
fn fields_are_named_by_their_layout() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let allowed = parse_allowed(include_str!("../raw-fields-allowed.txt"));
    let mut wrong = Vec::new();
    for file in rust_files(&root.join("crates")) {
        let rel = file.strip_prefix(&root).unwrap_or(&file).to_string_lossy().to_string();
        if allowed.iter().any(|a| if a.ends_with('/') { rel.starts_with(a.as_str()) } else { rel == *a }) {
            continue;
        }
        for f in findings(&std::fs::read_to_string(&file).expect("readable")) {
            wrong.push(format!("{rel}:{}: {} (a value by `bloblet_value`, `product_field`, `sum_tag`, …)", f.line, f.what));
        }
    }
    assert!(wrong.is_empty(), "{} fields named by number:\n{}", wrong.len(), wrong.join("\n"));
}
