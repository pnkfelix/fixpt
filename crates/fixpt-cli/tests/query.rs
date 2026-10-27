//! `fixpt query` and the REPL's `,query` (`docs/fx26.md`, "Queries"): the
//! definitions of a program that answer a question about types and
//! effects, on `programs/query/`.

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

fn program(name: &str) -> String {
    format!("{}/../fixpt-fx26/tests/programs/query/{name}", env!("CARGO_MANIFEST_DIR"))
}

/// `fixpt query` of `programs/query/name`: each answer's name, `may` before
/// those that may.
fn names(name: &str, query: &str) -> Vec<String> {
    let mut args = vec!["query".to_string(), program(name)];
    args.extend(query.split(' ').map(String::from));
    let out = Command::new(FIXPT).args(&args).output().expect("fixpt runs");
    assert!(out.status.success(), "{query}: {}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|l| if l.starts_with("; and may") { "may".to_string() } else { l.split(" : ").next().unwrap_or(l).to_string() })
        .collect()
}

/// Seven shapes, as the customer given each sees it: what makes a `t`
/// from nothing, what needs one to give one, and what takes one for
/// nothing back. A callback given a maker and a taker both makes one from
/// nothing and takes one for nothing.
#[test]
fn makers_transformers_and_takers() {
    assert_eq!(names("shapes.fx", "constructs t"), ["make", "lend", "lend-both"]);
    assert_eq!(names("shapes.fx", "transforms t"), ["step", "lend-step"]);
    assert_eq!(names("shapes.fx", "returns t"), ["make", "step", "lend", "lend-step", "lend-both"]);
    assert_eq!(names("shapes.fx", "consumes t"), ["take", "drain", "lend-both"]);
    assert_eq!(names("shapes.fx", "uses t"), ["make", "take", "step", "drain", "lend", "lend-step", "lend-both"]);
    assert_eq!(names("shapes.fx", "uses other"), ["unrelated"]);
}

/// An effect's atoms in a definition's own effect, and one whose region is
/// a variable as one that may; and what may write what a counter holds,
/// itself or through the procedure it returns.
#[test]
fn effects_and_mutation() {
    assert_eq!(names("effects.fx", "effect (write @ed)"), ["bump!", "may", "clear!"]);
    assert_eq!(names("effects.fx", "effect (maxeff (read @ed) (write @ed))"), ["bump!"]);
    assert_eq!(names("effects.fx", "effect (write @elsewhere)"), ["poke!", "may", "clear!"]);
    assert_eq!(names("effects.fx", "mutates counter"), ["bump!", "bumper"]);
}

/// At the REPL: a file loaded and a form typed, each answer where it is.
#[test]
fn at_the_repl() {
    use std::io::Write;
    let mut child = Command::new(FIXPT)
        .args(["fx26"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("fixpt runs");
    let input = format!(",load {}\n(define* again (subr pure (t) t) (lambda (x) x))\n,query transforms t\n", program("shapes.fx"));
    child.stdin.take().expect("piped").write_all(input.as_bytes()).expect("written");
    let out = child.wait_with_output().expect("ran");
    let text = String::from_utf8_lossy(&out.stdout);
    let answers: Vec<&str> = text.lines().map(|l| l.trim_start_matches("fx26> ")).filter(|l| l.contains("  ; ")).collect();
    assert_eq!(answers.len(), 3, "{text}");
    assert!(answers[0].contains("step : ") && answers[0].ends_with("shapes.fx:10:1"), "{answers:?}");
    assert!(answers[2].contains("again : ") && answers[2].ends_with("<fx26:1>:1:1"), "{answers:?}");
}
