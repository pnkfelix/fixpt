//! Both front ends' expanders (`macros.rs`, `macros.fx`) on each program in
//! `programs/macros`: what each checker finds of the program expanded, or
//! where and why each refuses it, the same. An expander's refusal is its
//! front end's (the FX-26 one's, its parse's). What follows an error's
//! first line, the uses that made the text it is in, the FX-26 front end
//! does not say yet; nor do the refusals of the checker's own of macros.

use fixpt_engine::Backend;
use fixpt_fx26::compare;
use fixpt_fx26::session::Fx26Session;

/// The checker's refusals of macros the FX-26 one does not make yet.
const NOT_YET: &[&str] = &["import-macro-name.fx", "include-macro-name.fx", "macro-over-global.fx", "with-shadows-macro.fx", "with-shadows-macro-nested.fx"];

#[test]
fn both_expanders_agree_on_macro_programs() {
    let dir = format!("{}/tests/programs/macros", env!("CARGO_MANIFEST_DIR"));
    let mut names: Vec<_> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    let mut wrong = Vec::new();
    // One session for all: each program is read from the standard
    // environment's state, which says no macros are defined (`macros-at!`).
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for path in names {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        if NOT_YET.contains(&name.as_str()) {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        s.checker.base_dir = path.parent().map(|d| d.to_path_buf());
        fixpt_fx26::syn::set_load_base(path.parent().map(|d| d.to_path_buf()));
        let mut c = s.fresh_checker();
        let rust = compare::canonical_checked(compare::check_with_rust_checker(&mut c, &text));
        let fx26 = match compare::both_checkers(&mut s, &text) {
            Ok((fx26, _)) => fx26,
            Err(e) => Err(e),
        };
        let same = match (&fx26, &rust) {
            (Ok(a), Ok(b)) => a == b,
            (Err(a), Err(b)) => a.message == b.message && (a.span.start, a.span.end) == (b.span.start, b.span.end),
            _ => false,
        };
        if !same {
            wrong.push(format!("{name}: FX-26 {fx26:?}, Rust {rust:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
