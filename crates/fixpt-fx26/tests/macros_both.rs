//! Both front ends' expanders (`macros.rs`, `macros.fx`) on each program in
//! `programs/macros`, and those importing a file's macros: what each checker finds of the program expanded, or
//! where and why each refuses it, the same. An expander's refusal is its
//! front end's (the FX-26 one's, its parse's), and an error is the same
//! with each use of a macro that made the text it is in (`same_error`).

use fixpt_engine::Backend;
use fixpt_fx26::compare;
use fixpt_fx26::session::Fx26Session;

#[test]
fn both_expanders_agree_on_macro_programs() {
    agree(&format!("{}/tests/programs/macros", env!("CARGO_MANIFEST_DIR")), "");
}

/// The programs of `fixpt-cli`'s `import-with-syntax` tests, `main*.fx`
/// (the rest are the files they import).
#[test]
fn both_expanders_agree_on_a_files_macros() {
    agree(&format!("{}/../fixpt-cli/tests/programs/import-with-syntax", env!("CARGO_MANIFEST_DIR")), "main");
}

/// Each program in `programs/macros` with its macros' signatures left out,
/// to be inferred: both front ends infer the same, as each finds of the
/// program, or each refuses it, the same.
#[test]
fn both_expanders_infer_alike() {
    agree_as(&format!("{}/tests/programs/macros", env!("CARGO_MANIFEST_DIR")), "", unsigned);
}

/// Program `text` with each `(define-syntax name σ (syntax-rules …))`'s `σ`
/// left out.
fn unsigned(text: &str) -> String {
    let mut interner = fixpt_read::Interner::default();
    let Ok(forms) = fixpt_read::Reader::new(text, fixpt_read::FileId(1), fixpt_read::SyntaxProfile::FX26, &mut interner).read_all() else { return text.to_string() };
    let mut out = String::new();
    for f in forms {
        let f = match f.as_proper_list() {
            Some([h, n, _, rules]) if h.as_symbol().is_some_and(|h| interner.name(h) == "define-syntax") => fixpt_read::Syntax::list(f.span, vec![h.clone(), n.clone(), rules.clone()]),
            _ => f,
        };
        out.push_str(&fixpt_read::write_syntax(&f, &interner));
        out.push('\n');
    }
    out
}

/// Both front ends on each program in `dir` whose name starts with `prefix`.
fn agree(dir: &str, prefix: &str) {
    agree_as(dir, prefix, |t| t.to_string());
}

/// Both front ends on each program in `dir` whose name starts with
/// `prefix`, as `made` makes it.
fn agree_as(dir: &str, prefix: &str, made: fn(&str) -> String) {
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.file_name().unwrap().to_string_lossy().starts_with(prefix)).collect();
    names.sort();
    let mut wrong = Vec::new();
    // One session for all: each program is read from the standard
    // environment's state, which says no macros are defined (`macros-at!`).
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for path in names {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let text = made(&std::fs::read_to_string(&path).unwrap());
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
            (Err(a), Err(b)) => compare::same_error(a, b),
            _ => false,
        };
        if !same {
            wrong.push(format!("{name}: FX-26 {fx26:?}, Rust {rust:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
