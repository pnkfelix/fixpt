//! The Rust front end's syntax is tenured, and while it is lent a
//! collection is of the nursery alone (`docs/research/typed-macros.md`,
//! "Decided: transformers in the front end's heap", decision 3): so a
//! procedural macro's transformer's call may collect, the expander holding
//! its syntax raw. `FIXPT_LENT_COLLECT=1` collects the nursery before and
//! after each call (`heap_syn::collect_young_if_asked`); every procedural
//! macro program says the same with it, and, in a build with debug
//! assertions, every piece of syntax used is checked tenured.

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// `fixpt check` of `path`, with `env` set: what it printed and said.
fn checked(path: &std::path::Path, env: &[(&str, &str)]) -> String {
    let dir = path.parent().expect("a directory");
    let mut c = Command::new(FIXPT);
    c.current_dir(dir).args(["check", &path.to_string_lossy()]);
    for (k, v) in env {
        c.env(k, v);
    }
    let out = c.output().expect("runs");
    String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr)
}

#[test]
fn the_procedural_programs_say_the_same_collected_around_each_transformer() {
    let dir = format!("{}/../fixpt-fx26/tests/programs/procedural", env!("CARGO_MANIFEST_DIR"));
    let mut ps: Vec<_> = std::fs::read_dir(&dir).expect("a directory").filter_map(|e| e.ok().map(|e| e.path())).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
    ps.sort();
    assert!(ps.len() > 10, "{} programs", ps.len());
    for p in ps {
        assert_eq!(checked(&p, &[]), checked(&p, &[("FIXPT_LENT_COLLECT", "1")]), "{}", p.display());
    }
}

/// The knob collects: a program of one transformer's call makes minor
/// collections with it, none without (the front end warm).
#[test]
fn the_knob_collects() {
    let p = std::path::PathBuf::from(format!("{}/../fixpt-fx26/tests/programs/procedural/aif-er.fx", env!("CARGO_MANIFEST_DIR")));
    let minors = |env: &[(&str, &str)]| checked(&p, env).lines().filter(|l| l.contains("gc minor")).count();
    // The first run after a build compiles the front end, which collects.
    checked(&p, &[]);
    assert_eq!(minors(&[("FIXPT_GC_TRACE", "1")]), 0);
    assert!(minors(&[("FIXPT_GC_TRACE", "1"), ("FIXPT_LENT_COLLECT", "1")]) > 0);
}
