//! What reaches the native convention (`fx-regs-rsjit-nativecc`), as the
//! code `FIXPT_SYMBOLS` names shows: kayak's compiler ran 25 times slower
//! for want of each (`TODO.md` §121).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// `text` run natively: its output, and the names of the code it made.
fn run(name: &str, text: &str) -> (String, String) {
    let dir = std::env::temp_dir().join(format!("fixpt-native-reach-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (program, syms) = (dir.join("p.fx"), dir.join("syms"));
    std::fs::write(&program, text).unwrap();
    let out = Command::new(FIXPT)
        .args(["--fx26-machine", "fx-regs-rsjit-nativecc", "eval", program.to_str().unwrap()])
        .env("FIXPT_SYMBOLS", &syms)
        .output()
        .expect("fixpt runs");
    let names = std::fs::read_to_string(&syms).unwrap_or_default();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    (String::from_utf8_lossy(&out.stdout).into_owned(), names)
}

fn has_native(names: &str, prefix: &str) -> bool {
    names.lines().any(|l| l.splitn(3, ' ').nth(2).is_some_and(|n| n.starts_with(&format!("native {prefix}"))))
}

/// An accessor of a record of more fields than a leaf has registers: its
/// `tagcase` loads only the field it uses, so it has register code, and is
/// native (a module holding one was cellular, all of it).
#[test]
fn a_wide_records_accessor_is_native() {
    let (out, names) = run("wide", include_str!("programs/native-reach/wide-accessor.fx"));
    assert!(out.contains("8 : int"), "{out}");
    assert!(!out.contains("not in the native convention"), "{out}");
    assert!(has_native(&names, "big-8"), "no native `big-8`:\n{names}");
}

/// A closure cellular code makes, where no native code is running (a
/// definition held cellular by `stay-cellular`), is compiled natively as it
/// is made, not adapted: native code calls it with no call-out to a
/// cellular machine.
#[test]
fn a_closure_cellular_code_makes_is_native() {
    let (out, names) = run("made", include_str!("programs/native-reach/made-closure.fx"));
    assert!(out.contains("5000 : int"), "{out}");
    assert!(has_native(&names, "adder@"), "no native `adder`:\n{names}");
}

/// `n` values bound by `let*`, each `base` plus its place: the
/// bindings, and their names.
fn bindings(prefix: &str, base: &str, n: usize) -> (String, Vec<String>) {
    let names: Vec<String> = (0..n).map(|i| format!("{prefix}{i}")).collect();
    (names.iter().enumerate().map(|(i, v)| format!("({v} (+ {base} {i}))")).collect::<Vec<_>>().join(" "), names)
}

/// A sum of `xs`: chains of 20 added left to right, and their sums so.
/// (One chain 520 deep takes the checker a minute; a balanced tree, more
/// temporaries than a leaf has registers.)
fn sum(xs: &[String]) -> String {
    let chain = |xs: &[String]| xs[1..].iter().fold(xs[0].clone(), |acc, x| format!("(+ {acc} {x})"));
    chain(&xs.chunks(20).map(chain).collect::<Vec<_>>())
}

/// A closure of more values than a load reaches on arm64 (`ldur`, 32;
/// one `sub` and a load, about 510): native, as on x86_64, where there
/// was never a limit. The second's 520 values are two procedures' (a
/// frame holds about 500).
#[test]
fn a_wide_closure_is_native() {
    let (a, mut xs) = bindings("a", "n", 40);
    xs.push("x".into());
    let wide = format!("(define wide-sum (subr pure (int) int)\n  (lambda (n) (let* ({a} (f (lambda ((x int)) {}))) (f 1))))\n(wide-sum 10)\n", sum(&xs));
    let (out, names) = run("wide-closure", &wide);
    assert!(out.contains("1181 : int"), "{out}");
    assert!(!out.contains("not in the native convention"), "{out}");
    assert!(has_native(&names, "wide-sum/f@"), "no native closure:\n{names}");

    let ((a, mut xs), (b, ys)) = (bindings("a", "n", 260), bindings("b", "y", 260));
    xs.extend(ys);
    xs.push("x".into());
    let far = format!(
        "(define far-sum (subr pure (int) int)\n  (lambda (n) (let* ({a} (g (lambda ((y int)) (let* ({b} (f (lambda ((x int)) {}))) (f 1))))) (g 100))))\n(far-sum 10)\n",
        sum(&xs)
    );
    let (out, names) = run("far-closure", &far);
    assert!(out.contains("95941 : int"), "{out}");
    assert!(!out.contains("not in the native convention"), "{out}");
    assert!(has_native(&names, "far-sum/g/f@"), "no native closure:\n{names}");
}
