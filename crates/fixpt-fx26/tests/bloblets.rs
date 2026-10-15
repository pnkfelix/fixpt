//! Bloblets (`docs/fx26.md`, "Bloblets"): each program in
//! `programs/bloblet` whose first line says what it gives, `;; => value`,
//! or what its refusal says, `;; ! words`, does so, lowered. The others
//! are compared only, by `checker.rs` and `compiler.rs`. Those that fail
//! at run time are in `programs/bloblet-errors`, which the compilers' tests
//! do not read: each machine says a run-time error in its own words.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

#[test]
fn bloblet_programs_do_as_they_say() {
    let dir = |d: &str| format!("{}/tests/programs/{d}", env!("CARGO_MANIFEST_DIR"));
    let mut names: Vec<_> = ["bloblet", "bloblet-errors"]
        .iter()
        .flat_map(|d| std::fs::read_dir(dir(d)).unwrap().map(|e| e.unwrap().path()))
        .collect();
    names.sort();
    let (mut wrong, mut seen) = (Vec::new(), 0);
    for path in names {
        let text = std::fs::read_to_string(&path).unwrap();
        let first = text.lines().next().unwrap_or("");
        let (gives, refused) = (first.strip_prefix(";; => "), first.strip_prefix(";; ! "));
        if gives.is_none() && refused.is_none() {
            continue;
        }
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        let got = match s.run_program(&text) {
            Ok(Ok(v)) => Ok(v),
            Ok(Err(e)) => Err(e.to_string()),
            Err(e) => Err(e.message),
        };
        seen += 1;
        let ok = match (gives, refused, &got) {
            (Some(want), _, Ok(v)) => v == want,
            (_, Some(want), Err(e)) => e.contains(want),
            _ => false,
        };
        if !ok {
            wrong.push(format!("{}: says `{first}`, gives {got:?}", path.display()));
        }
    }
    assert!(seen >= 7, "only {seen} programs");
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// An index shown within a flat array's length by the facts in scope is
/// recorded (`NodeFacts::in_bounds`, `TODO.md` §77, N5c): `total`'s, under
/// a test against `blobref-length`; not `main`'s `(blobref-index s 4)`,
/// which nothing shows below the length.
#[test]
fn indices_shown_in_bounds() {
    let text = include_str!("programs/bloblet/flat-bounds.fx");
    let mut c = fixpt_fx26::Checker::new();
    let forms = c.read_in(fixpt_read::FileId(0), text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    for (f, done) in forms.iter().zip(done) {
        if !done {
            c.top_all(f).expect("checks");
        }
    }
    let indices: Vec<_> = c
        .facts
        .datum
        .keys()
        .filter(|e| matches!(c.arena.exp_at(**e), fixpt_fx26::ast::Exp::Bloblet { op: fixpt_fx26::ast::BlobletOp::RefIndex, .. }))
        .collect();
    assert_eq!(indices.len(), 2, "two indices");
    assert_eq!(c.facts.in_bounds.len(), 1, "one shown in bounds: {:?}", c.facts.in_bounds);
}
