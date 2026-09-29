//! FX program files within the size limits, or no worse than their debt:
//! see `fixpt_tidy::fx_size` for the rule and why.

use fixpt_tidy::fx_size::{check, fx_files, parse_debt, Size};
use std::path::Path;

#[test]
fn fx_files_stay_within_their_limits() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let files: Vec<(String, Size)> = fx_files(&root)
        .into_iter()
        .map(|f| {
            let rel = f.strip_prefix(&root).unwrap_or(&f).to_string_lossy().to_string();
            (rel, Size::of(&std::fs::read_to_string(&f).expect("readable")))
        })
        .collect();
    let debt = parse_debt(include_str!("../fx-size-debt.txt"));
    let wrong = check(&files, &debt);
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
