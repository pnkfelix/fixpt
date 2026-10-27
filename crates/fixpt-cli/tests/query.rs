//! `fixpt query` and the REPL's `,query` (`docs/fx26.md`, "Queries"): the
//! definitions of a program that answer a question about types and
//! effects, on `programs/query/`.

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

fn program(name: &str) -> String {
    format!("{}/../fixpt-fx26/tests/programs/query/{name}", env!("CARGO_MANIFEST_DIR"))
}

/// `fixpt query` of `programs/query/name`: each answer's name, `may` before
/// those that may, and `local` before local names bound to a polymorphic
/// definition instantiated so that they answer, each with the definition
/// it is in.
fn names(name: &str, query: &str) -> Vec<String> {
    let mut args = vec!["query".to_string(), program(name)];
    args.extend(query.split(' ').map(String::from));
    let out = Command::new(FIXPT).args(&args).output().expect("fixpt runs");
    assert!(out.status.success(), "{query}: {}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|l| match l {
            _ if l.starts_with("; and may") => "may".to_string(),
            _ if l.starts_with("; and local names bound") => "local".to_string(),
            _ if l.starts_with("; and local names in scope") => "around".to_string(),
            _ => {
                let name = l.split(" : ").next().unwrap_or(l);
                match l.split_once(", in ") {
                    Some((_, inside)) => format!("{name} in {}", inside.split(", ").next().unwrap_or(inside)),
                    None => name.to_string(),
                }
            }
        })
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
    assert_eq!(names("effects.fx", "effect (maxeff (read @ed) (write @ed))"), ["bump!"]);
    assert_eq!(names("effects.fx", "effect (write @elsewhere)"), ["poke!", "may", "clear!"]);
    assert_eq!(names("effects.fx", "mutates counter"), ["bump!", "bumper", "reset!", "zero!"]);
}

/// Local names bound to a polymorphic definition instantiated at a type or
/// an effect that answers, where it, as it is, does not: `clear!` at `@ed`,
/// any type's identity at `counter`. A call, unnamed, is not one.
#[test]
fn locals_instantiated_so() {
    assert_eq!(names("effects.fx", "effect (write @ed)"), ["bump!", "reset!", "zero!", "may", "clear!", "local", "wipe in reset!"]);
    assert_eq!(names("effects.fx", "transforms counter"), ["again", "local", "keep in again"]);
}

/// `around`: the local names in scope at a place, or bound anywhere in a
/// definition, as well: `again`'s parameter `k`, in its body and its
/// `let`'s, and not before it. `keep` is listed once, as instantiated.
#[test]
fn locals_around_a_context() {
    assert_eq!(names("effects.fx", "transforms counter around again"), ["again", "local", "keep in again"]);
    assert_eq!(names("effects.fx", "uses counter around again"), names("effects.fx", "uses counter").into_iter().chain(["around".into(), "k in again".into()]).collect::<Vec<String>>());
    let at = |line_col: &str| format!("uses counter around {}:{line_col}", program("effects.fx"));
    let plain = names("effects.fx", "uses counter");
    let with_k: Vec<String> = plain.iter().cloned().chain(["around".into(), "k in again".into()]).collect();
    assert_eq!(names("effects.fx", &at("28:30")), with_k);
    assert_eq!(names("effects.fx", &at("28:51")), with_k);
    assert_eq!(names("effects.fx", &at("27:1")), plain);
    assert_eq!(names("effects.fx", "effect (write @ed) around zero!"), names("effects.fx", "effect (write @ed)"));
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
