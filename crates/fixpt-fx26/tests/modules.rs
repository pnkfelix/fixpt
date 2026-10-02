//! First-class modules, stage M1 (`docs/research/first-class-modules.md`):
//! each program in `programs/modules` says on its first line what it gives,
//! `;; => value`, or what its refusal says, `;; ! words`, lowered. Kept in
//! files: the checker written in FX-26 has no modules yet (M2), and the
//! tests compare both checkers on every literal program in these sources.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

#[test]
fn module_programs_do_as_they_say() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/modules");
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    let (mut wrong, mut seen) = (Vec::new(), 0);
    for path in names {
        let text = std::fs::read_to_string(&path).unwrap();
        let first = text.lines().next().unwrap_or("");
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        let got = match s.run_program(&text) {
            Ok(Ok(v)) => Ok(v),
            Ok(Err(e)) => Err(e.to_string()),
            Err(e) => Err(e.message),
        };
        seen += 1;
        let ok = match (first.strip_prefix(";; => "), first.strip_prefix(";; ! "), &got) {
            (Some(want), _, Ok(v)) => v == want,
            (_, Some(want), Err(e)) => e.contains(want),
            _ => false,
        };
        if !ok {
            wrong.push(format!("{}: says `{first}`, gives {got:?}", path.display()));
        }
    }
    assert!(seen >= 10, "only {seen} programs");
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
