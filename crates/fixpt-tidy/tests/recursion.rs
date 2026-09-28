//! The lint on self-calls not in tail position that step an index
//! (`fixpt_tidy::recursion`): on cases, and on the front end written in
//! FX-26, which has none.

use fixpt_read::SyntaxProfile;
use fixpt_tidy::recursion::index_recursion;

#[test]
fn loops_written_as_recursion_are_found() {
    let found = index_recursion(include_str!("sexp/recursion-sample.fx"), SyntaxProfile::FX26).expect("reads");
    let names: Vec<&str> = found.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, ["upto", "go"], "{found:?}");
}

/// Each such loop in the front end is a stack as deep as its data: the
/// assembler's once overflowed on the largest word (`n-code-list`).
#[test]
fn the_front_end_has_none() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../fixpt-fx26/src");
    let mut paths: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
    paths.sort();
    let mut report = Vec::new();
    for p in paths {
        let text = std::fs::read_to_string(&p).unwrap();
        let found = index_recursion(&text, SyntaxProfile::FX26).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
        for f in found {
            report.push(format!("{}:{}:{}: `{}` calls itself, not in tail position, stepping an index", p.display(), f.line, f.col, f.name));
        }
    }
    assert!(report.is_empty(), "loops written as recursion (make each a loop, with an accumulator):\n{}", report.join("\n"));
}
