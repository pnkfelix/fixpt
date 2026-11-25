//! Strings at a region, `(stringof r)` (the user's, 2026-10-28;
//! `docs/fx26.md`, "Strings at a region"): `programs/run/stringof.fx` on
//! each machine FX-26 runs on, the evaluator written in FX-26 among them,
//! each giving the same values; and UTF-8 text, `utf8` (`TODO.md` §306),
//! `programs/run/utf8.fx`, so, and `#utf8"…"`, `run/utf8-literals.fx`;
//! and an offset refused alike on each, the
//! native code's own reads (ASCII only) leaving it to the primitive; and
//! views into bytes and into a string (`TODO.md` §310), `run/views.fx`.

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
        "count",
        "(3 1 4)",
        "s",
        "#utf8\"é😀\"",
        "(2 6)",
        "\"é😀\"",
        "#t",
        "(#\\a #\\é #\\😀 #\\z)",
        "w",
        "#utf8\"world\"",
        "(5 5)",
        "(#\\w #\\o #\\r #\\l #\\d)",
    ];
    let runs: Vec<_> = machines().into_iter().map(|m| (m, std::thread::spawn(move || values(m, "utf8.fx")))).collect();
    for (m, t) in runs {
        assert_eq!(t.join().expect("ran"), want, "{m}");
    }
}

/// UTF-8 text written in the program, `#utf8"…"` (`TODO.md` §306):
/// `programs/run/utf8-literals.fx` alike on every machine, a constant made
/// once.
#[test]
fn utf8_literals_on_every_machine() {
    let want = [
        "t",
        "#utf8\"aé😀z\"",
        "(4 8)",
        "#t",
        "#\\e",
        "#utf8\"quoted\"",
        "d",
        "9",
        "(#t #f)",
        "once",
        "#t",
        "#utf8\"\"",
        "#\\λ",
        "3",
    ];
    let runs: Vec<_> = machines().into_iter().map(|m| (m, std::thread::spawn(move || values(m, "utf8-literals.fx")))).collect();
    for (m, t) in runs {
        assert_eq!(t.join().expect("ran"), want, "{m}");
    }
}

/// A bytevector written as text, `#u8"…"`, beside `#u8(…)`:
/// `programs/run/byte-strings.fx` alike on every machine, a constant made
/// once, written back as `#u8(…)`.
#[test]
fn byte_strings_on_every_machine() {
    let want = [
        "t",
        "#u8(97 98 128 255 10 92 122)",
        "7",
        "#t",
        "65",
        "#u8(113 117 111 116 101 100)",
        "d",
        "9",
        "(#t #f)",
        "once",
        "#t",
        "#u8()",
        "#t",
        "2",
        "-1",
    ];
    let runs: Vec<_> = machines().into_iter().map(|m| (m, std::thread::spawn(move || values(m, "byte-strings.fx")))).collect();
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
    // Each case's text, `t` or a slice of it, its operation, offset and
    // result type, and what the run's last line says.
    let slice = "(utf8-slice t 1 7)";
    let cases = [
        ("ref-inside", "t", "utf8-ref", "2", "char", "utf8: the offset is inside a character"),
        ("next-inside", "t", "utf8-next", "2", "nat", "utf8: the offset is inside a character"),
        ("ref-end", "t", "utf8-ref", "8", "char", "utf8 index out of range (length 8)"),
        ("next-end", "t", "utf8-next", "8", "nat", "utf8 index out of range (length 8)"),
        ("ref-negative", "t", "utf8-ref", "-1", "char", "utf8 index out of range (length 8)"),
        ("ref-bignum", "t", "utf8-ref", "1180591620717411303424", "char", "expected an exact integer that fits a machine word"),
        ("ref-last", "t", "utf8-ref", "7", "char", "#\\z"),
        ("next-last", "t", "utf8-next", "7", "nat", "8"),
        // A slice's offsets are its own (`TODO.md` §310).
        ("slice-ref-inside", slice, "utf8-ref", "1", "char", "utf8: the offset is inside a character"),
        ("slice-ref-end", slice, "utf8-ref", "6", "char", "utf8 index out of range (length 6)"),
        ("slice-ref-first", slice, "utf8-ref", "0", "char", "#\\é"),
    ];
    let mut runs = Vec::new();
    for (name, text, op, k, ty, want) in cases {
        let path = dir.join(format!("{name}.fx"));
        let text = format!(
            "(define t (string->utf8 \"a\\xe9;\\x1F600;z\"))\n\
             (define* f (subr (maxeff spin) (utf8 int) {ty}) (lambda (u k) ({op} u k)))\n(f {text} {k})\n"
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

/// Views into bytes and into a string (`TODO.md` §310), `programs/run/views.fx`:
/// a whole buffer where a view is wanted, slices and their pieces, a
/// slice seeing its owner's writes, the copies, on every machine alike.
#[test]
fn views_on_every_machine() {
    let want = [
        "s",
        "len",
        "12",
        "w",
        "\"world\"",
        "5",
        "#\\w",
        "\"or\"",
        "(#t #t #f)",
        "\"world\"",
        "\"orl\"",
        "#utf8\"world\"",
        "seen",
        "#\\z",
        "bv",
        "bs",
        "#u8(7 7)",
        "2",
        "7",
        "#t",
        "#u8(7 7)",
        "#u8(7)",
        "#utf8\"bc\"",
        "fb",
        "u",
        "#utf8\"héllo\"",
        "(5 6)",
        "#utf8\"é\"",
        "1",
        "#utf8\"llo\"",
    ];
    let runs: Vec<_> = machines().into_iter().map(|m| (m, std::thread::spawn(move || values(m, "views.fx")))).collect();
    for (m, t) in runs {
        assert_eq!(t.join().expect("ran"), want, "{m}");
    }
}
