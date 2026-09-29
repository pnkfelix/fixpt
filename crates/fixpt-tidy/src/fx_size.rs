//! **An FX program file stays small enough to read** (the user's limits,
//! 2026-09-29): at most [`MAX_LINES`] lines, each at most [`MAX_COLUMNS`]
//! characters. The limits are met by factoring: a line that runs long is
//! usually deep nesting, which a named subroutine extracted from it cures;
//! a file that runs long is usually several modules, which split at their
//! seams. Never by re-wrapping lines to fit.
//!
//! Files over the limits when the rule came are listed, with how far over
//! they are, in `fx-size-debt.txt`; a listed file may not get worse, and its
//! entry must come down as it gets better, until it goes. Some are exempt
//! for good, each by a line `exempt PREFIX` there (the user's, 2026-09-29):
//! benchmarks that are one file by design, and test inputs whose size is
//! their point.

use std::path::{Path, PathBuf};

/// The most lines an `.fx` file may have.
pub const MAX_LINES: usize = 1000;

/// The most characters a line of an `.fx` file may have.
pub const MAX_COLUMNS: usize = 100;

/// A file's size: its lines, and how many of them are too long.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size {
    pub lines: usize,
    pub long: usize,
}

impl Size {
    pub fn of(text: &str) -> Size {
        let lines: Vec<&str> = text.lines().collect();
        Size { lines: lines.len(), long: lines.iter().filter(|l| l.chars().count() > MAX_COLUMNS).count() }
    }

    /// Within the limits.
    pub fn fits(self) -> bool {
        self.lines <= MAX_LINES && self.long == 0
    }
}

/// Every `.fx` file under `root`, but in `target`, `.git`, `.claude` and
/// downloaded papers.
pub fn fx_files(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else { continue };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                if path.file_name().is_some_and(|n| !matches!(n.to_str(), Some("target" | ".git" | ".claude" | "papers"))) {
                    stack.push(path);
                }
            } else if path.extension().is_some_and(|e| e == "fx") {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

/// The debt file's entries: a path from the repository's root, its lines,
/// and its long lines, one to a line; `#` starts a comment.
pub fn parse_debt(text: &str) -> Vec<(String, Size)> {
    text.lines()
        .map(|l| l.split('#').next().unwrap_or("").trim())
        .filter(|l| !l.is_empty() && !l.starts_with("exempt "))
        .filter_map(|l| {
            let mut w = l.split_whitespace();
            let path = w.next()?.to_string();
            let lines = w.next()?.parse().ok()?;
            let long = w.next()?.parse().ok()?;
            Some((path, Size { lines, long }))
        })
        .collect()
}

/// The debt file's exempt prefixes: a file whose path starts with one is
/// not measured.
pub fn parse_exempt(text: &str) -> Vec<String> {
    text.lines()
        .map(|l| l.split('#').next().unwrap_or("").trim())
        .filter_map(|l| l.strip_prefix("exempt ").map(|p| p.trim().to_string()))
        .collect()
}

/// What is wrong, for each file: over the limits and not listed; listed and
/// worse than its entry; listed and better (the entry must come down); or
/// listed and not found.
pub fn check(files: &[(String, Size)], debt: &[(String, Size)]) -> Vec<String> {
    let mut out = Vec::new();
    for (path, size) in files {
        match debt.iter().find(|(p, _)| p == path) {
            None if !size.fits() => out.push(format!(
                "{path}: {} lines, {} over {MAX_COLUMNS} columns; the limits are {MAX_LINES} and none: extract subroutines, or split the file",
                size.lines, size.long
            )),
            None => {}
            Some((_, owed)) if size.lines > owed.lines.max(MAX_LINES) || size.long > owed.long => out.push(format!(
                "{path}: {} lines, {} long, worse than its debt ({}, {}): extract subroutines rather than add to it",
                size.lines, size.long, owed.lines, owed.long
            )),
            Some((_, owed)) if size.lines.max(MAX_LINES) < owed.lines.max(MAX_LINES) || size.long < owed.long => out.push(format!(
                "{path}: now {} lines, {} long, better than its debt ({}, {}): lower its entry in fx-size-debt.txt{}",
                size.lines,
                size.long,
                owed.lines,
                owed.long,
                if size.fits() { ", or remove it" } else { "" }
            )),
            Some(_) => {}
        }
    }
    for (path, _) in debt {
        if !files.iter().any(|(p, _)| p == path) {
            out.push(format!("{path}: in fx-size-debt.txt, but not found"));
        }
    }
    out
}
