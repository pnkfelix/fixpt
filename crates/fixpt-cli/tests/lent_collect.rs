//! The Rust front end's syntax is tenured, and while it is lent a
//! collection is of the nursery alone (`docs/research/typed-macros.md`,
//! "Decided: transformers in the front end's heap", decision 3): so a
//! procedural macro's transformer's call may collect, the expander holding
//! its syntax raw. `FIXPT_LENT_COLLECT=1` collects the nursery before and
//! after each call (`heap_syn::collect_young_if_asked`); every procedural
//! macro program says the same with it, and, in a build with debug
//! assertions, every piece of syntax used is checked tenured. Checked
//! (`fixpt check`: the Rust checker's own heap, its transformers run in
//! the transformers' session) and run (`fixpt eval`: a session's checker,
//! its transformers run in the session's runtime's phase-1 namespace, on
//! the heap its syntax is in, collected before and after inside the call).

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// `fixpt check` of `path`, with `env` set: what it printed and said.
fn checked(path: &std::path::Path, env: &[(&str, &str)]) -> String {
    fixpt("check", path, env)
}

/// `fixpt eval` of `path`, as [`checked`].
fn run(path: &std::path::Path, env: &[(&str, &str)]) -> String {
    fixpt("eval", path, env)
}

fn fixpt(how: &str, path: &std::path::Path, env: &[(&str, &str)]) -> String {
    let dir = path.parent().expect("a directory");
    let mut c = Command::new(FIXPT);
    c.current_dir(dir).args([how, &path.to_string_lossy()]);
    for (k, v) in env {
        c.env(k, v);
    }
    let out = c.output().expect("runs");
    String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr)
}

fn programs() -> Vec<std::path::PathBuf> {
    let dir = format!("{}/../fixpt-fx26/tests/programs/procedural", env!("CARGO_MANIFEST_DIR"));
    let mut ps: Vec<_> = std::fs::read_dir(&dir).expect("a directory").filter_map(|e| e.ok().map(|e| e.path())).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
    ps.sort();
    assert!(ps.len() > 10, "{} programs", ps.len());
    ps
}

#[test]
fn the_procedural_programs_say_the_same_collected_around_each_transformer() {
    for p in programs() {
        assert_eq!(checked(&p, &[]), checked(&p, &[("FIXPT_LENT_COLLECT", "1")]), "{}", p.display());
    }
}

#[test]
fn the_procedural_programs_run_the_same_collected_inside_each_call_in_phase_1() {
    for p in programs() {
        assert_eq!(run(&p, &[]), run(&p, &[("FIXPT_LENT_COLLECT", "1")]), "{}", p.display());
    }
}

/// In a session, the knob collects the session's heap inside the call,
/// which only the phase-1 namespace's call does: so the transformer ran
/// there, not in the transformers' session.
#[test]
fn a_session_runs_its_transformers_in_its_own_runtime() {
    let p = std::path::PathBuf::from(format!("{}/../fixpt-fx26/tests/programs/procedural/aif-er.fx", env!("CARGO_MANIFEST_DIR")));
    let minors = |env: &[(&str, &str)]| run(&p, env).lines().filter(|l| l.contains("gc minor")).count();
    run(&p, &[]);
    // Two calls, each collected on either side (one of them in place of
    // what the nursery's filling would have made).
    let (quiet, asked) = (minors(&[("FIXPT_GC_TRACE", "1")]), minors(&[("FIXPT_GC_TRACE", "1"), ("FIXPT_LENT_COLLECT", "1")]));
    assert!(asked >= 4 && asked > quiet, "{quiet} minor collections, {asked} with the knob");
    assert!(run(&p, &[]).contains("(6 0)"));
}

/// The knob collects: a program of two transformers' calls makes more
/// minor collections with it than without (the front end warm; without
/// it, what the FX-26 checker's phase-1 namespace allocates may make one).
#[test]
fn the_knob_collects() {
    let p = std::path::PathBuf::from(format!("{}/../fixpt-fx26/tests/programs/procedural/aif-er.fx", env!("CARGO_MANIFEST_DIR")));
    let minors = |env: &[(&str, &str)]| checked(&p, env).lines().filter(|l| l.contains("gc minor")).count();
    // The first run after a build compiles the front end, which collects.
    checked(&p, &[]);
    let (quiet, asked) = (minors(&[("FIXPT_GC_TRACE", "1")]), minors(&[("FIXPT_GC_TRACE", "1"), ("FIXPT_LENT_COLLECT", "1")]));
    assert!(asked > quiet, "{quiet} minor collections, {asked} with the knob");
}
