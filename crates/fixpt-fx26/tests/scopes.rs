//! The binding structure the expander's walk finds, held to the checkers'
//! (`docs/research/binding-shapes.md`, step 1): every test program, its
//! local value binders renamed as the walk finds their scopes
//! (`Checker::alpha_renamed`), means what it meant.

use fixpt_fx26::Checker;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

fn programs(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir).expect("a directory").map(|e| e.expect("an entry").path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            programs(&p, out);
        } else if p.extension().is_some_and(|e| e == "fx") {
            out.push(p);
        }
    }
}

/// Every test program walked: what the walk refuses, by its message, with
/// the first program that has it. A program the front end does not read
/// (a module file's parameters, a load it cannot find) is not counted.
#[test]
fn every_program_is_walked() {
    let root = Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs"));
    let mut files = Vec::new();
    programs(root, &mut files);
    let mut refused: BTreeMap<String, (usize, String)> = BTreeMap::new();
    let (mut walked, mut unread, mut renamings, mut module_files) = (0, 0, 0, 0);
    let mut differ = Vec::new();
    for f in &files {
        let text = std::fs::read_to_string(f).expect("readable");
        let mut c = Checker::new();
        c.base_dir = f.parent().map(|d| d.to_path_buf());
        // Unread or refused as a whole: a module file, one written to be
        // refused; the checker's refusal, not the walk's, is what it says.
        if let Err(e) = fixpt_fx26::compare::check_with_rust_checker(&mut c, &text) {
            if std::env::var("SCOPES_SHOW_UNREAD").is_ok() {
                eprintln!("unread {}: {}", f.strip_prefix(root).unwrap_or(f).display(), e.message.chars().take(100).collect::<String>());
            }
            unread += 1;
            // A module file, read as a program, that its load checks:
            // walked, not checked again.
            let file = f.file_name().expect("a name").to_string_lossy();
            if text.lines().any(|l| l.starts_with("(module-parameters")) && c_types(f, &format!("(define %m (load-module \"{file}\"))")).is_ok() {
                let mut c = Checker::new();
                c.base_dir = f.parent().map(|d| d.to_path_buf());
                match c.alpha_renamed(&text) {
                    Ok(_) => module_files += 1,
                    Err(e) => {
                        let name = f.strip_prefix(root).unwrap_or(f).display().to_string();
                        refused.entry(e.message.chars().take(90).collect()).or_insert((0, name)).0 += 1;
                    }
                }
            }
            continue;
        }
        let types = c_types(f, &text);
        let mut c = Checker::new();
        c.base_dir = f.parent().map(|d| d.to_path_buf());
        match c.alpha_renamed(&text) {
            Ok(forms) => {
                walked += 1;
                let renamed = forms.join("\n");
                renamings += renamed.matches('%').count().saturating_sub(text.matches('%').count());
                let again = c_types(f, &renamed).map(|ts| ts.iter().map(|t| unrenamed(t)).collect()).map_err(|e| unrenamed(&e));
                let types = types.clone().map(|ts| ts.iter().map(|t| unrenamed(t)).collect::<Vec<_>>()).map_err(|e| unrenamed(&e));
                if again != types {
                    let name = f.strip_prefix(root).unwrap_or(f).display().to_string();
                    differ.push(format!("{name}: {types:?}\n  renamed: {again:?}"));
                }
            }
            Err(e) => {
                let key: String = e.message.chars().take(90).collect();
                let name = f.strip_prefix(root).unwrap_or(f).display().to_string();
                let entry = refused.entry(key).or_insert((0, name));
                entry.0 += 1;
            }
        }
    }
    let shown: Vec<String> = refused.iter().map(|(m, (n, first))| format!("{n:4} {m}  (first: {first})")).collect();
    eprintln!("{walked} walked, {unread} unread or refused by the checker, {} refused", refused.values().map(|v| v.0).sum::<usize>());
    eprintln!("{renamings} names renamed; {} programs differ; {module_files} module files walked", differ.len());
    assert!(refused.is_empty(), "the walk refuses:\n{}", shown.join("\n"));
    assert!(differ.is_empty(), "renamed, these mean something else:\n{}", differ.join("\n"));
}

/// What the Rust checker says of program `text`, from `f`'s directory:
/// each form's type, or its refusal.
fn c_types(f: &Path, text: &str) -> Result<Vec<String>, String> {
    let mut c = Checker::new();
    c.base_dir = f.parent().map(|d| d.to_path_buf());
    fixpt_fx26::compare::check_with_rust_checker(&mut c, text).map_err(|e| String::from(e.message))
}

/// `s` with the renaming's `%k` suffixes taken off: what a type names, as
/// it was written.
fn unrenamed(s: &str) -> String {
    let mut out = String::new();
    let mut chars = s.chars().peekable();
    let mut prev_name = false;
    while let Some(c) = chars.next() {
        // A name a procedural macro made, numbered for the run.
        if c == '~' && out.ends_with('%') {
            out.push(c);
            while chars.peek().is_some_and(|d| d.is_ascii_digit()) {
                chars.next();
            }
            continue;
        }
        if c == '%' && prev_name && chars.peek().is_some_and(|d| d.is_ascii_digit()) {
            while chars.peek().is_some_and(|d| d.is_ascii_digit()) {
                chars.next();
            }
            continue;
        }
        prev_name = !c.is_whitespace() && !"()[]\"`".contains(c);
        out.push(c);
    }
    out
}

/// The walk over a directory of FX-26 outside the tests, named by
/// `FIXPT_WALK_DIR`: what it refuses, by message. Run by hand
/// (`cargo test --test scopes -- --ignored`).
#[test]
#[ignore]
fn a_directory_is_walked() {
    let Ok(dir) = std::env::var("FIXPT_WALK_DIR") else { return };
    let mut files = Vec::new();
    programs(Path::new(&dir), &mut files);
    let mut refused: BTreeMap<String, (usize, String)> = BTreeMap::new();
    let mut walked = 0;
    for f in &files {
        let Ok(text) = std::fs::read_to_string(f) else { continue };
        if std::env::var("FIXPT_WALK_SAY").is_ok() {
            eprintln!("walking {}", f.display());
        }
        let mut c = Checker::new();
        c.base_dir = f.parent().map(|d| d.to_path_buf());
        match c.alpha_renamed(&text) {
            Ok(_) => walked += 1,
            Err(e) => {
                let at = text.get(..e.span.start as usize).map_or(0, |t| t.lines().count());
                refused.entry(e.message.chars().take(90).collect()).or_insert((0, format!("{}:{at}", f.display()))).0 += 1;
            }
        }
    }
    eprintln!("{walked} of {} walked", files.len());
    for (m, (n, first)) in &refused {
        eprintln!("{n:4} {m}  (first: {first})");
    }
}
