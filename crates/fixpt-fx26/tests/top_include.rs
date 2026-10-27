//! A top-level `include` (the user's, 2026-10-27, Heist's problem F): each
//! program in `programs/top-include` says on its first line what it gives,
//! `;; => value`, or what its refusal says, `;; ! words`, run as a session
//! runs it, each front end given the forms the `include` is made; and both
//! checkers agree on it, the FX-26 one told what each `include` gives, as
//! `fixpt check` tells it.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

fn programs() -> Vec<std::path::PathBuf> {
    let dir = format!("{}/tests/programs/top-include", env!("CARGO_MANIFEST_DIR"));
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    names
}

#[test]
fn top_level_includes_do_as_they_say() {
    let mut wrong = Vec::new();
    for path in programs() {
        let text = std::fs::read_to_string(&path).unwrap();
        let first = text.lines().next().unwrap_or("");
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        s.checker.base_dir = path.parent().map(|d| d.to_path_buf());
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
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn both_checkers_agree_on_top_level_includes() {
    let mut wrong = Vec::new();
    for path in programs() {
        let text = std::fs::read_to_string(&path).unwrap();
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        s.checker.base_dir = path.parent().map(|d| d.to_path_buf());
        fixpt_fx26::syn::set_load_base(path.parent().map(|d| d.to_path_buf()));
        let (fx26, rust) = fixpt_fx26::compare::both_checkers(&mut s, &text).expect("both check");
        let same = match (&fx26, &rust) {
            (Ok(a), Ok(b)) => a == b,
            (Err(a), Err(b)) => a.message == b.message && a.span == b.span,
            _ => false,
        };
        if !same {
            wrong.push(format!("{}: FX-26 {fx26:?}, Rust {rust:?}", path.display()));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
