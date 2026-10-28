//! A file that makes a module (`load-input`, a `lambda` around a `module`)
//! in native code, as Heist's editor makes each of its files (2026-10-28):
//! its maker's frame holds every item, more than 4080 bytes, and an item
//! that is a procedure returns a closure over more than eight values,
//! made in a leaf. By either compiler to the native convention; neither
//! falls back to cellular code. On arm64, the one written in Rust
//! (`DONE.md` §153); the one written in FX-26 makes only x86_64's.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// Items in a large maker: past what a frame of 4080 bytes holds, and a
/// module of more fields than arm64's displacements reach.
const MANY: usize = 600;

#[test]
fn a_large_module_maker_runs_natively() {
    on("fx-regs-rsjit-nativecc", MANY);
}

/// The same where the compiler written in FX-26 makes each procedure's code.
#[cfg(target_arch = "x86_64")]
#[test]
fn a_large_module_maker_runs_natively_by_fx26() {
    on("fx-regs-fxjit-nativecc", MANY);
}

/// A small one: only the closure over more than eight values, in a leaf.
#[test]
fn a_leaf_makes_a_closure_over_many_natively() {
    on("fx-regs-rsjit-nativecc", 12);
    if cfg!(target_arch = "x86_64") {
        on("fx-regs-fxjit-nativecc", 12);
    }
}

/// `(+ x1 (+ x2 … xn))`.
fn sum(xs: &[String]) -> String {
    match xs {
        [x] => x.clone(),
        [x, rest @ ..] => format!("(+ {x} {})", sum(rest)),
        [] => "0".into(),
    }
}

fn on(machine: &str, items: usize) {
    let dir = std::env::temp_dir().join(format!("fixpt-module-makers-{machine}-{items}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let base = "(lambda () (module (define b0 100) (define* b1 (subr pure (int) int) (lambda (x) (+ x 1)))))\n";
    let mut maker = String::from("(lambda ((m-base (load-input-moduleof \"base.fx\")))\n(module\n(hide (include m-base))\n");
    for i in 0..items {
        maker += &format!("(define v{i} {i})\n");
    }
    // A leaf whose value is a closure over four parameters, nine items and
    // an included name and procedure: fourteen values.
    let captured: Vec<String> = ["a", "b", "c", "d", "x", "b0"].iter().map(|s| s.to_string()).chain((0..9).map(|i| format!("v{i}"))).collect();
    maker += &format!(
        "(define* pick (subr pure (int int int int) (subr pure (int) int))\n  (lambda (a b c d) (lambda (x) (b1 {}))))\n",
        sum(&captured)
    );
    maker += &format!("(define* last (subr pure () int) (lambda () v{}))\n))\n", items - 1);
    let main = "(define m-base ((load-input \"base.fx\")))\n\
                (define m ((load-input \"maker.fx\") m-base))\n\
                (((with m pick) 1 2 3 4) 5)\n\
                ((with m last))\n";
    std::fs::write(dir.join("base.fx"), base).unwrap();
    std::fs::write(dir.join("maker.fx"), maker).unwrap();
    std::fs::write(dir.join("main.fx"), main).unwrap();
    let out = Command::new(FIXPT)
        .args(["--fx26-machine", machine, "eval", dir.join("main.fx").to_str().unwrap()])
        .output()
        .expect("fixpt runs");
    let _ = std::fs::remove_dir_all(&dir);
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    assert!(out.status.success(), "{text}");
    assert!(!text.contains("not in the native convention yet"), "{text}");
    // 1+2+3+4+5, 100, 0+…+8, and one; the last item.
    let values: Vec<&str> = text.lines().filter(|l| l.contains(" : int")).filter_map(|l| l.split(" : ").next()).collect();
    assert_eq!(values[values.len() - 2..], ["152", &(items - 1).to_string()[..]], "{text}");
}
