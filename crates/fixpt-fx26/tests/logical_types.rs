//! `allof` and `anyof` (`docs/research/logical-types.md` §8.5): `allof`,
//! one procedure with each member's type, its body checked against each
//! member, a call taking every member it fits (U1); `anyof`, a true union,
//! whose members may overlap (U2). Each program in `programs/allof` and
//! `programs/anyof` says on its first line what it gives, `;; => value`, or
//! what its refusal says, `;; ! words`.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

fn programs_do_as_they_say(sub: &str, least: usize) {
    let dir = format!("{}/tests/programs/{sub}", env!("CARGO_MANIFEST_DIR"));
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    let mut wrong = Vec::new();
    for path in &names {
        let text = std::fs::read_to_string(path).unwrap();
        let first = text.lines().next().unwrap_or("");
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        let got = match s.run_program(&text) {
            Ok(Ok(v)) => Ok(v),
            Ok(Err(e)) => Err(e.to_string()),
            Err(e) => Err(e.message),
        };
        let ok = match (first.strip_prefix(";; => "), first.strip_prefix(";; ! "), &got) {
            (Some(want), _, Ok(v)) => v == want,
            // Refused by both alike, not by one of them.
            (_, Some(want), Err(e)) => e.contains(want) && !e.contains("checkers disagree"),
            _ => false,
        };
        if !ok {
            wrong.push(format!("{}: says `{first}`, gives {got:?}", path.display()));
        }
    }
    assert!(names.len() >= least, "only {} programs", names.len());
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn allof_programs_do_as_they_say() {
    programs_do_as_they_say("allof", 6);
}

#[test]
fn anyof_programs_do_as_they_say() {
    programs_do_as_they_say("anyof", 6);
}
