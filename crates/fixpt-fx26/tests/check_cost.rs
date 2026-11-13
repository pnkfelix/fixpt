//! What the checkers cost, not only what they say (`TODO.md` §266): each of
//! `tests/programs/cost/`, a type that shares much, checked by both
//! checkers in about the time its size takes. Each is a diamond forty
//! levels deep, made by a functor applied again and again (a macro's
//! chain of them), as a program's own sharing would be: each level's type
//! made of the level below's, twice. The FX-26 checker's `k-kept-reading`
//! once walked a type by the path to it, not the types seen, so a type
//! reached two ways was walked again: the same answers, which no
//! comparison of the two checkers could tell apart, and twice the time a
//! level, 2^40 steps here. A program's first line says what to expect:
//! `;; ! message`, refused with that message; else, checked.

mod common;

use fixpt_fx26::Checker;

/// How long a check may take, both checkers, on a machine as loaded as a
/// suite's: some 0.1 s in release, 0.3 s in debug, at forty
/// levels; the walk by the path would take 2^40 steps.
const DEADLINE: std::time::Duration = std::time::Duration::from_secs(if cfg!(debug_assertions) { 30 } else { 10 });

/// Both checkers on `program`; they must agree. What they said, or the
/// refusal's message.
fn both(program: &str) -> Result<Vec<String>, String> {
    let fx26 = common::with_own(|s| s.check_with_own_checker(program)).expect("the FX-26 front end reads it").map_err(|e| e.message.to_string());
    let rust = fixpt_fx26::compare::check_with_rust_checker(&mut Checker::new(), program).map_err(|e| e.message.to_string());
    let canon = |r: Result<Vec<String>, String>| {
        r.map(|ls| ls.iter().map(|l| fixpt_fx26::compare::canonical(l)).collect::<Vec<_>>()).map_err(|m| fixpt_fx26::compare::canonical(&m))
    };
    let (fx26, rust) = (canon(fx26), canon(rust));
    assert_eq!(fx26, rust, "the checkers disagree");
    fx26
}

#[test]
fn types_that_share_much_check_in_the_time_their_size_takes() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/cost");
    let mut files: Vec<_> = std::fs::read_dir(dir).expect("the programs").flatten().map(|e| e.path()).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
    files.sort();
    assert!(files.len() >= 7, "only {files:?}");
    for path in files {
        let text = std::fs::read_to_string(&path).expect("readable");
        let refused = text.lines().next().and_then(|l| l.strip_prefix(";; ! ")).map(str::to_string);
        // On a thread of its own, so that a check that does not end fails
        // the test rather than hanging it; its session its own too.
        let (send, recv) = std::sync::mpsc::channel();
        let (program, started) = (text.clone(), std::time::Instant::now());
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(move || {
                let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| both(&program)));
                let _ = send.send(r);
            })
            .expect("a thread");
        let name = path.file_name().expect("a name").to_string_lossy().into_owned();
        let said = match recv.recv_timeout(DEADLINE) {
            Ok(Ok(said)) => said,
            Ok(Err(_)) => panic!("{name}: the checkers disagree, or one failed (above)"),
            Err(_) => panic!("{name}: not checked within {DEADLINE:?}: a walk that grows with the paths through a type, not its size"),
        };
        match (refused, said) {
            (None, Ok(_)) => {}
            (Some(m), Err(e)) => assert!(e.contains(&m), "{name}: refused, but as {e:?}, not {m:?}"),
            (None, Err(e)) => panic!("{name}: refused: {e}"),
            (Some(m), Ok(_)) => panic!("{name}: checked, where {m:?} was expected"),
        }
        eprintln!("{name}: {:.3} s", started.elapsed().as_secs_f64());
    }
}
