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

/// The walk written in FX-26 (`macros-walk.fx`) finds the scopes the Rust
/// one finds: each test program the checker accepts, expanded by the Rust
/// expander, its local value binders renamed by each walk, the same.
#[test]
fn the_two_walks_agree() {
    let root = Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs"));
    let mut files = Vec::new();
    programs(root, &mut files);
    let mut s = fixpt_fx26::session::Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).expect("starts");
    let (mut compared, mut differ) = (0, Vec::new());
    for f in &files {
        let text = std::fs::read_to_string(f).expect("readable");
        let mut c = Checker::new();
        c.base_dir = f.parent().map(|d| d.to_path_buf());
        if fixpt_fx26::compare::check_with_rust_checker(&mut c, &text).is_err() {
            continue;
        }
        let mut c = Checker::new();
        c.base_dir = f.parent().map(|d| d.to_path_buf());
        let (Ok(forms), Ok(rust)) = (c.expanded_written(&text), Checker::new().alpha_renamed(&text)) else { continue };
        let fx = s.own_program_walked(&forms.join("\n")).unwrap_or_else(|e| vec![format!("walk: {}", e.message)]);
        compared += 1;
        let same = |a: &str, b: &str| normal(a) == normal(b);
        if fx.len() != rust.len() || fx.iter().zip(&rust).any(|(a, b)| !same(a, b)) {
            let first = fx.iter().zip(&rust).find(|(a, b)| !same(a, b)).map(|(a, b)| format!("FX-26 {a}\n  Rust  {b}")).unwrap_or_else(|| format!("{} forms against {}", fx.len(), rust.len()));
            differ.push(format!("{}: {first}", f.display()));
        }
    }
    eprintln!("{compared} programs compared, {} differ", differ.len());
    assert!(differ.is_empty(), "the walks differ:\n{}", differ.iter().take(10).cloned().collect::<Vec<_>>().join("\n"));
}

/// The records the FX-26 expander writes (`macros-shapes.fx`'s `shaped`)
/// are the Rust one's: each test program the checker accepts, each of its
/// top-level forms as the Rust checker shaped it, and as FX-26 shapes it
/// given the same form unshaped.
#[test]
fn the_two_expanders_write_the_same_records() {
    let root = Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs"));
    let mut files = Vec::new();
    programs(root, &mut files);
    let mut s = fixpt_fx26::session::Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).expect("starts");
    let (mut compared, mut differ) = (0, Vec::new());
    for f in &files {
        let text = std::fs::read_to_string(f).expect("readable");
        let mut c = Checker::new();
        c.base_dir = f.parent().map(|d| d.to_path_buf());
        c.keep_shapes_seen();
        if fixpt_fx26::compare::check_with_rust_checker(&mut c, &text).is_err() {
            continue;
        }
        let seen = c.shapes_seen();
        if !seen.iter().any(|(_, after)| after.contains("#:relied")) {
            continue;
        }
        // Each form as FX-26 shapes it, in order, those declared ahead
        // too, which the Rust checker does not shape.
        let before: Vec<&str> = seen.iter().map(|(b, _)| b.as_str()).collect();
        let fx = s.own_program_shaped(&before.join("\n"), f.parent().map(|d| d.to_path_buf())).unwrap_or_else(|e| vec![format!("shape: {}", e.message)]);
        compared += 1;
        let same = |a: &str, b: &str| b.is_empty() || normal(a) == normal(b);
        if fx.len() != seen.len() || fx.iter().zip(&seen).any(|(a, (_, b))| !same(a, b)) {
            let first = fx.iter().zip(&seen).find(|(a, (_, b))| !same(a, b)).map(|(a, (_, b))| format!("FX-26 {a}\n  Rust  {b}")).unwrap_or_else(|| format!("{} forms against {}", fx.len(), seen.len()));
            differ.push(format!("{}: {first}", f.display()));
        }
    }
    eprintln!("{compared} programs compared, {} differ", differ.len());
    for d in &differ {
        eprintln!("{d}");
    }
    assert!(differ.is_empty(), "the records differ in {} programs", differ.len());
}

/// The forms of the file named by `FIXPT_SHAPED_FILE`, after expansion,
/// shaped by each expander, written. Run by hand (`cargo test --test scopes
/// -- --ignored`).
#[test]
#[ignore]
fn a_file_is_shaped() {
    let Ok(path) = std::env::var("FIXPT_SHAPED_FILE") else { return };
    let text = std::fs::read_to_string(&path).expect("readable");
    let mut c = Checker::new();
    c.base_dir = std::path::Path::new(&path).parent().map(|d| d.to_path_buf());
    c.keep_shapes_seen();
    let checked = fixpt_fx26::compare::check_with_rust_checker(&mut c, &text);
    eprintln!("Rust checks: {:?}", checked.as_ref().err().map(|e| &e.message));
    let seen = c.shapes_seen();
    let before: Vec<&str> = seen.iter().map(|(b, _)| b.as_str()).collect();
    let mut s = fixpt_fx26::session::Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).expect("starts");
    let fx = s.own_program_shaped(&before.join("\n"), std::path::Path::new(&path).parent().map(|d| d.to_path_buf())).unwrap_or_else(|e| vec![format!("shape: {}", e.message)]);
    for (k, (_, after)) in seen.iter().enumerate() {
        eprintln!("Rust  {after}\nFX-26 {}", fx.get(k).map_or("(none)", |s| s.as_str()));
    }
}

/// Form text `t` read and written again by the Rust reader, its strings
/// emptied and its aliases' expansion numbers taken out: two writers'
/// spellings of one form alike (the FX-26 one escapes nothing in a string),
/// and two expansions' counts (`%~N:x` is `%~:x`) the same.
fn normal(t: &str) -> String {
    let mut interner = fixpt_read::Interner::default();
    let written = match fixpt_read::Reader::new(t, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX26, &mut interner).read_all() {
        Ok(forms) => forms.iter().map(|f| fixpt_read::write_syntax(&unstrung(f), &interner)).collect::<Vec<_>>().join(" "),
        Err(_) => t.to_string(),
    };
    let mut out = String::new();
    let mut rest = written.as_str();
    while let Some(i) = rest.find("%~") {
        out.push_str(&rest[..i + 2]);
        rest = rest[i + 2..].trim_start_matches(|c: char| c.is_ascii_digit());
    }
    out.push_str(rest);
    out
}

/// `s` with each string empty.
fn unstrung(s: &fixpt_read::Syntax) -> fixpt_read::Syntax {
    use fixpt_read::Datum;
    let datum = match &s.datum {
        Datum::Str(_) => Datum::Str(String::new()),
        Datum::List { items, tail } => Datum::List { items: items.iter().map(unstrung).collect(), tail: tail.as_ref().map(|t| Box::new(unstrung(t))) },
        d => d.clone(),
    };
    fixpt_read::Syntax::new(s.span, datum)
}

/// Probe: the FX-26 walk of the forms in `FIXPT_WALK_TEXT`'s file.
#[test]
#[ignore]
fn a_text_is_walked() {
    let Ok(paths) = std::env::var("FIXPT_WALK_TEXT") else { return };
    let mut s = fixpt_fx26::session::Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).expect("starts");
    for path in paths.split(',') {
        let text = std::fs::read_to_string(path).expect("readable");
        let t = std::time::Instant::now();
        let fx = s.own_program_walked(&text).unwrap_or_else(|e| vec![format!("walk: {}", e.message)]);
        for f in &fx {
            eprintln!("{}", f.chars().take(60).collect::<String>());
        }
        eprintln!("{path}: {:?}", t.elapsed());
    }
}

/// Probe: the Rust checker alone on the file `FIXPT_RUST_CHECK` names.
#[test]
#[ignore]
fn a_text_rust_checks() {
    let Ok(path) = std::env::var("FIXPT_RUST_CHECK") else { return };
    let text = std::fs::read_to_string(&path).expect("readable");
    let mut c = Checker::new();
    match fixpt_fx26::compare::check_with_rust_checker(&mut c, &text) {
        Ok(out) => out.iter().for_each(|l| eprintln!("{l}")),
        Err(e) => eprintln!("refused at {}: {}", e.span.start, e.message),
    }
}
