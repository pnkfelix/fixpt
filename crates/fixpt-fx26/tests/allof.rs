//! `allof`, one procedure with each member's type (`docs/research/logical-types.md`
//! §8.5, U1): its body checked against each member, a call taking every
//! member it fits. Each program in `programs/allof` says on its first line
//! what it gives, `;; => value`, or what its refusal says, `;; ! words`.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

#[test]
fn allof_programs_do_as_they_say() {
    let dir = format!("{}/tests/programs/allof", env!("CARGO_MANIFEST_DIR"));
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
            (_, Some(want), Err(e)) => e.contains(want),
            _ => false,
        };
        if !ok {
            wrong.push(format!("{}: says `{first}`, gives {got:?}", path.display()));
        }
    }
    assert!(names.len() >= 6, "only {} programs", names.len());
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
