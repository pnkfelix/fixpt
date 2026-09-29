//! The lint on lists written pair by pair (`fixpt_tidy::cons_chain`).

use fixpt_read::SyntaxProfile;
use fixpt_tidy::cons_chain::cons_chains;

#[test]
fn chains_are_found() {
    let found = cons_chains(include_str!("sexp/cons-chain-sample.fx"), SyntaxProfile::FX26).expect("reads");
    let seen: Vec<(usize, usize)> = found.iter().map(|f| (f.line, f.elements)).collect();
    assert_eq!(seen, [(2, 3), (3, 3), (3, 2)], "{found:?}");
}

/// How many chains each FX file in the repository has, for the rewrite.
#[test]
#[ignore = "a report: cargo test -p fixpt-tidy --test cons_chain -- --ignored --nocapture"]
fn report() {
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
    let mut stack = vec![std::path::PathBuf::from(root)];
    let mut rows = Vec::new();
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap().flatten() {
            let p = e.path();
            let name = p.file_name().unwrap().to_string_lossy().into_owned();
            if p.is_dir() && !name.starts_with('.') && name != "target" {
                stack.push(p);
            } else if name.ends_with(".fx") {
                let text = std::fs::read_to_string(&p).unwrap();
                if let Ok(found) = cons_chains(&text, SyntaxProfile::FX26)
                    && !found.is_empty()
                {
                    rows.push(format!("{:4} {}", found.len(), p.strip_prefix(root).unwrap().display()));
                }
            }
        }
    }
    rows.sort();
    eprintln!("{}", rows.join("\n"));
}

/// The front end written in FX-26 writes its lists with `list`, or says why
/// not.
#[test]
fn the_front_end_has_none() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../fixpt-fx26/src");
    let mut paths: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
    paths.sort();
    let mut report = Vec::new();
    for p in paths {
        let text = std::fs::read_to_string(&p).unwrap();
        for f in cons_chains(&text, SyntaxProfile::FX26).unwrap_or_else(|e| panic!("{}: {e}", p.display())) {
            report.push(format!("{}:{}:{}: {} pairs, where `list` would do", p.display(), f.line, f.col, f.elements));
        }
    }
    assert!(report.is_empty(), "lists written pair by pair (`list`, or `; cons-chain:` and why):\n{}", report.join("\n"));
}
