//! Strings at a region, `(stringof r)` (the user's, 2026-10-28;
//! `docs/fx26.md`, "Strings at a region"): `programs/run/stringof.fx` on
//! each machine FX-26 runs on, the evaluator written in FX-26 among them,
//! each giving the same values; and UTF-8 text, `utf8` (`TODO.md` §306),
//! `programs/run/utf8.fx`, so; and an offset refused alike on each, the
//! native code's own reads (ASCII only) leaving it to the primitive.

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// The machines: the stencils only where this build found a nightly
/// compiler and the native convention's where it is.
fn machines() -> Vec<&'static str> {
    let stencils = !fixpt_native::stencil::opt_levels().is_empty();
    [
        "rs-scheme-vm",
        "fx-ast-eval",
        "fx-cells-rsinterp",
        "fx-cells-asminterp",
        "fx-cells-rsjit-cellcc",
        "fx-cells-fxjit-cellcc",
        "fx-cells-stencils-cellcc",
        "fx-regs-rsjit-cellcc",
        "fx-regs-rsjit-nativecc",
        "fx-regs-fxjit-cellcc",
        "fx-regs-fxjit-nativecc",
    ]
    .into_iter()
    .filter(|m| stencils || !m.contains("stencils"))
    .filter(|m| fixpt_native::NATIVE_CONVENTION_AVAILABLE || !m.ends_with("nativecc"))
    .collect()
}

/// What `fixpt --machine machine eval` of program `run/NAME` says, each
/// line as far as its type.
fn values(machine: &str, name: &str) -> Vec<String> {
    let path = format!("{}/../fixpt-fx26/tests/programs/run/{name}", env!("CARGO_MANIFEST_DIR"));
    let out = Command::new(FIXPT).args(["--machine", machine, "eval", &path]).output().expect("fixpt runs");
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    text.lines().map(|l| l.split(" : ").next().unwrap_or(l).to_string()).collect()
}

#[test]
fn strings_at_a_region_on_every_machine() {
    let want = [
        "joined",
        "upcased!",
        "\"abcdéfg\"",
        "#t",
        "\"HELLO, WORLD\"",
        "(#\\b #\\c #\\b)",
        "#t",
        "#utf8\"é!\"",
    ];
    let runs: Vec<_> = machines().into_iter().map(|m| (m, std::thread::spawn(move || values(m, "stringof.fx")))).collect();
    for (m, t) in runs {
        assert_eq!(t.join().expect("ran"), want, "{m}");
    }
}

#[test]
fn utf8_text_on_every_machine() {
    let want = [
        "t",
        "walk",
        "4",
        "8",
        "(#\\a #\\é #\\😀 #\\z)",
        "#utf8\"é😀\"",
        "\"😀z\"",
        "(#t #f #t #f)",
        "#t",
        "1",
        "4",
    ];
    let runs: Vec<_> = machines().into_iter().map(|m| (m, std::thread::spawn(move || values(m, "utf8.fx")))).collect();
    for (m, t) in runs {
        assert_eq!(t.join().expect("ran"), want, "{m}");
    }
}

/// A `utf8` read at an offset no character starts at, refused, on every
/// machine as the primitive refuses it: the native code's fast paths
/// (`TODO.md` §306) read a character of one byte in range, and leave the
/// rest to it. A bignum, a negative offset, the end, inside `é`.
#[test]
fn utf8_offsets_refused_on_every_machine() {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("utf8-refused");
    std::fs::create_dir_all(&dir).expect("a directory");
    let cases = [
        ("ref-inside", "utf8-ref", "2", "char", "utf8: the offset is inside a character"),
        ("next-inside", "utf8-next", "2", "nat", "utf8: the offset is inside a character"),
        ("ref-end", "utf8-ref", "8", "char", "utf8 index out of range (length 8)"),
        ("next-end", "utf8-next", "8", "nat", "utf8 index out of range (length 8)"),
        ("ref-negative", "utf8-ref", "-1", "char", "utf8 index out of range (length 8)"),
        ("ref-bignum", "utf8-ref", "1180591620717411303424", "char", "expected an exact integer that fits a machine word"),
        ("ref-last", "utf8-ref", "7", "char", "#\\z"),
        ("next-last", "utf8-next", "7", "nat", "8"),
    ];
    let mut runs = Vec::new();
    for (name, op, k, ty, want) in cases {
        let path = dir.join(format!("{name}.fx"));
        let text = format!(
            "(define t (string->utf8 \"a\\xe9;\\x1F600;z\"))\n\
             (define* f (subr (maxeff spin) (utf8 int) {ty}) (lambda (u k) ({op} u k)))\n(f t {k})\n"
        );
        std::fs::write(&path, text).expect("written");
        for m in machines() {
            let path = path.clone();
            let run = std::thread::spawn(move || {
                let out = Command::new(FIXPT).args(["--machine", m]).arg("eval").arg(&path).output().expect("fixpt runs");
                format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
            });
            runs.push((name, m, want, run));
        }
    }
    for (name, m, want, run) in runs {
        let out = run.join().expect("ran");
        let last = out.lines().last().unwrap_or("");
        assert!(last.contains(want), "{name} on {m}: {out}");
    }
}
