//! FX program files within the size limits, or no worse than their debt:
//! see `fixpt_tidy::fx_size` for the rule and why.

use fixpt_tidy::fx_size::{check, fx_files, parse_debt, parse_exempt, Size};
use std::path::Path;

#[test]
fn fx_files_stay_within_their_limits() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let text = include_str!("../fx-size-debt.txt");
    let exempt = parse_exempt(text);
    let files: Vec<(String, Size)> = fx_files(&root)
        .into_iter()
        .map(|f| f.strip_prefix(&root).unwrap_or(&f).to_string_lossy().to_string())
        .filter(|rel| !exempt.iter().any(|p| rel.starts_with(p.as_str())))
        .filter_map(|rel| {
            let text = std::fs::read_to_string(root.join(&rel)).expect("readable");
            // A file that asks to be passed over (`fixpt_tidy::ignored`).
            (!fixpt_tidy::ignored(&text)).then(|| (rel, Size::of(&text)))
        })
        .collect();
    let debt = parse_debt(text);
    let wrong = check(&files, &debt);
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A file asks to be passed over by a line of its leading comment block.
#[test]
fn a_file_may_ask_to_be_ignored() {
    assert!(fixpt_tidy::ignored(";; fixpt-tidy: ignore\n(f)\n"));
    assert!(fixpt_tidy::ignored(";;; A scratch file.\n;;; fixpt-tidy: ignore, kept for reference\n\n(f)\n"));
    // Only before its first form, and only as the line says it.
    assert!(!fixpt_tidy::ignored("(f)\n;; fixpt-tidy: ignore\n"));
    assert!(!fixpt_tidy::ignored(";; see fixpt-tidy: ignore, elsewhere\n(f)\n"));
    assert!(!fixpt_tidy::ignored("(f)\n"));
}

/// A test program's first line, its expectation, may be any width; no other
/// line may.
#[test]
fn an_expectation_line_may_be_wide() {
    let wide = "x".repeat(120);
    assert_eq!(Size::of(&format!(";; ! {wide}\n(f)\n")).long, 0);
    assert_eq!(Size::of(&format!(";; => {wide}\n")).long, 0);
    assert_eq!(Size::of(&format!("(f)\n;; ! {wide}\n")).long, 1);
    assert_eq!(Size::of(&format!(";; {wide}\n")).long, 1);
}
