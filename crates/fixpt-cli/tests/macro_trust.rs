//! A use a template made is not aligned with its macro's signature again as
//! it is expanded (`docs/research/typed-macros.md`, "Decided: a use a
//! template made is not aligned again"): `FIXPT_MACRO_RECHECK=1` aligns it
//! anyway, and every macro program in the tests says the same either way,
//! no such use refused (which would be a fault in the binding-shape check).

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// `fixpt check` of `path`, `FIXPT_MACRO_RECHECK` set to `recheck`: what it
/// printed and said.
fn checked(path: &std::path::Path, recheck: &str) -> String {
    let dir = path.parent().expect("a directory");
    let out = Command::new(FIXPT).current_dir(dir).args(["check", &path.to_string_lossy()]).env("FIXPT_MACRO_RECHECK", recheck).output().expect("runs");
    String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr)
}

fn programs(dir: &str) -> Vec<std::path::PathBuf> {
    let dir = if dir == "import-with-syntax" { format!("{}/tests/programs/{dir}", env!("CARGO_MANIFEST_DIR")) } else { format!("{}/../fixpt-fx26/tests/programs/{dir}", env!("CARGO_MANIFEST_DIR")) };
    let mut ps: Vec<_> = std::fs::read_dir(&dir).expect("a directory").filter_map(|e| e.ok().map(|e| e.path())).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
    ps.sort();
    ps
}

fn same_either_way(dir: &str) {
    let ps = programs(dir);
    assert!(ps.len() > 10, "{dir}: {} programs", ps.len());
    for p in ps {
        let (trusting, rechecking) = (checked(&p, "0"), checked(&p, "1"));
        assert!(!rechecking.contains("binding-shape check"), "{}: a use a template made refused:\n{rechecking}", p.display());
        assert_eq!(trusting, rechecking, "{}", p.display());
    }
}

#[test]
fn the_macro_programs_say_the_same_rechecked() {
    same_either_way("macros");
}

#[test]
fn the_procedural_programs_say_the_same_rechecked() {
    same_either_way("procedural");
}

/// A file's macros, imported (`import-with-syntax`), their uses of each
/// other renamed as the importer has them (`Action::MacroHead`).
#[test]
fn the_imported_macro_programs_say_the_same_rechecked() {
    same_either_way("import-with-syntax");
}

#[test]
fn a_recheck_that_is_neither_0_nor_1_is_refused() {
    let p = programs("macros").into_iter().find(|p| p.ends_with("loop-deep.fx")).expect("loop-deep.fx");
    let said = checked(&p, "2");
    assert!(said.contains("`FIXPT_MACRO_RECHECK` is `2`: it is 0 or 1"), "{said}");
}

/// A procedural macro's contract held to by default, and not where
/// `FIXPT_MACRO_CONTRACTS=0` says (`typed-macros.md`, "Decided: procedural
/// macros checked by their contracts"): a transformer that places its body
/// outside the binder its contract says is refused; let be, the body's `x`
/// is the global's.
#[test]
fn contracts_are_held_to_unless_turned_off() {
    let p = format!("{}/../fixpt-fx26/tests/programs/procedural/contract-scope.fx", env!("CARGO_MANIFEST_DIR"));
    let run = |contracts: &str| {
        let out = Command::new(FIXPT).args(["eval", &p]).env("FIXPT_MACRO_CONTRACTS", contracts).output().expect("runs");
        String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr)
    };
    let held = run("1");
    assert!(held.contains("its expansion places `x` where its contract does not put it in `x`'s scope"), "{held}");
    let off = run("0");
    assert!(off.lines().last().is_some_and(|l| l.starts_with("104 : int")), "{off}");
    let wrong = run("yes");
    assert!(wrong.contains("`FIXPT_MACRO_CONTRACTS` is `yes`: it is 0 or 1"), "{wrong}");
}
