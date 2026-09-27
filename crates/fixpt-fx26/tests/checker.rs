//! The checker written in FX-26 (`src/check.fx`), reading and parsing with
//! the reader and the parser written in FX-26, against the Rust checker on
//! the same programs (`PLAN.md` §11, step 10).

use fixpt_fx26::session::compile_program_as;

/// Where byte `at` of the front end is, as `file:line:column`.
fn locate(at: usize) -> String {
    let parts = [
        ("eager-reader.fx", fixpt_fx26::EAGER_READER),
        ("parser.fx", fixpt_fx26::PARSER),
        ("table.fx", fixpt_fx26::TABLE),
        ("check.fx", fixpt_fx26::CHECKER),
        ("evaluator.fx", fixpt_fx26::EVALUATOR),
        ("layout.fx", fixpt_fx26::LAYOUT),
        ("standard.fx", fixpt_fx26::STANDARD_OPS),
        ("compile.fx", fixpt_fx26::COMPILER),
        ("arm64.fx", fixpt_fx26::ARM64),
        ("native-layout.fx", fixpt_fx26::NATIVE_LAYOUT),
        ("native.fx", fixpt_fx26::NATIVE),
    ];
    let mut start = 0;
    for (name, text) in parts {
        if at <= start + text.len() {
            let before = &text[..at - start];
            let line = before.matches('\n').count() + 1;
            let col = before.len() - before.rfind('\n').map_or(0, |i| i + 1) + 1;
            return format!("{name}:{line}:{col}");
        }
        start += text.len() + 1;
    }
    format!("byte {at}")
}

#[test]
fn the_checker_checks() {
    if let Err(e) = compile_program_as(&fixpt_fx26::front_end(), "fx:") {
        panic!("{}: {}", locate(e.span.start as usize), e.message);
    }
}

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_fx26::{Checker, Top};
use fixpt_read::FileId;

/// An effect's atoms in a fixed order: the two checkers keep theirs in
/// orders of their own (Rust's follows symbols' interning).
fn canonical(s: &str) -> String {
    let mut out = String::new();
    let mut rest = s;
    while let Some(i) = rest.find("(maxeff ") {
        out.push_str(&rest[..i]);
        let inner = &rest[i + "(maxeff ".len()..];
        let (mut depth, mut end, mut items, mut start) = (0, inner.len(), Vec::new(), 0);
        for (j, c) in inner.char_indices() {
            match c {
                '(' => depth += 1,
                ')' if depth == 0 => {
                    end = j;
                    break;
                }
                ')' => depth -= 1,
                ' ' if depth == 0 => {
                    items.push(&inner[start..j]);
                    start = j + 1;
                }
                _ => {}
            }
        }
        items.push(&inner[start..end]);
        items.sort();
        out.push_str(&format!("(maxeff {})", items.join(" ")));
        rest = &inner[(end + 1).min(inner.len())..];
    }
    out.push_str(rest);
    out
}

/// The Rust checker on `program`, in the same terms as the FX-26 one.
fn rust_check(program: &str) -> Result<Vec<String>, (String, u32, u32)> {
    let mut c = Checker::new();
    let fail = |e: fixpt_fx26::FxError| (e.message, e.span.start, e.span.end);
    let forms = c.read_in(FileId(0), program).map_err(fail)?;
    let done = c.declare_ahead(&forms).map_err(fail)?;
    let mut out = Vec::new();
    for (f, done) in forms.iter().zip(done) {
        if done {
            continue;
        }
        match c.top(f).map_err(fail)? {
            Top::Define { name, ty, effect, .. } => {
                out.push(format!("define {} : {} ! {}", c.interner.name(name), c.show_ty(ty), c.show_effect(&effect)))
            }
            Top::DefineRec { bindings } => {
                for (name, ty, _) in bindings {
                    out.push(format!("define {} : {} ! pure", c.interner.name(name), c.show_ty(ty)))
                }
            }
            Top::Exp(k) => out.push(format!("{} ! {}", c.show_ty(k.ty), c.show_effect(&k.effect))),
            _ => {}
        }
    }
    Ok(out)
}

/// The FX-26 checker on `program`; `None` if the FX-26 front end cannot
/// parse it.
fn fx26_check(program: &str) -> Option<Result<Vec<String>, (String, u32, u32)>> {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    fx26_check_in(&mut s, program)
}

fn fx26_check_in(s: &mut Fx26Session, program: &str) -> Option<Result<Vec<String>, (String, u32, u32)>> {
    let r = s.check_with_own_checker(program).ok()?;
    Some(r.map_err(|e| (e.message, e.span.start, e.span.end)))
}

fn canon(r: Result<Vec<String>, (String, u32, u32)>) -> Result<Vec<String>, (String, u32, u32)> {
    r.map(|ls| ls.iter().map(|l| canonical(l)).collect()).map_err(|(m, a, b)| (canonical(&m), a, b))
}

/// Both checkers; they must agree. Returns what they said.
fn both(program: &str) -> Result<Vec<String>, (String, u32, u32)> {
    let ours = canon(fx26_check(program).unwrap_or_else(|| panic!("the FX-26 front end cannot parse:\n{program}")));
    let rust = canon(rust_check(program));
    assert_eq!(ours, rust, "the checkers disagree on:\n{program}");
    ours
}

#[test]
fn small_programs() {
    assert_eq!(both("(+ 1 2)"), Ok(vec!["int ! pure".to_string()]));
    let _ = both("(define f (subr pure (int) int) (lambda (n) (if (= n 0) 1 (* n (f (- n 1)))))) (f 10)");
    let _ = both("(the (listof int @l) (cons 1 (cons 2 nil)))");
    let _ = both("(car (cons 1 #t))");
    let _ = both("(let ((r (the (ref int @r) (new 1)))) (begin (set r (+ (get r) 41)) (get r)))");
    let _ = both("(extract (product (a 1) (b \"two\")) b)");
    let _ = both("(if 1 2 3)");
    let _ = both("(+ 1 #t)");
    let _ = both("(lambda (x) x)");
}

#[test]
#[ignore = "a probe: the checker's helpers one by one"]
fn probe_helpers() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    fixpt_fx26::session::load_eager_reader(&mut s.scheme).expect("loads");
    let exprs = std::env::var("PROBE").unwrap_or_default();
    for e in exprs.split(';') {
        s.scheme.engine.set_step_limit(Some(2_000_000));
        let r = s.scheme.eval_str("<probe>", e).map(|h| s.scheme.write(h));
        eprintln!("{e} => {r:?}");
    }
}

/// Every test program, rejected ones included, both checkers, reported
/// together. Programs the FX-26 parser cannot read yet are counted.
#[test]
fn every_test_program() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let (mut report, mut unparsed, mut agreed) = (Vec::new(), Vec::new(), 0);
    for sub in ["bidirectional", "bloblet", "control", "run", "pldi89", "regions", "datum"] {
        let mut names: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
        names.sort();
        for path in names {
            let program = std::fs::read_to_string(&path).unwrap();
            let name = format!("{sub}/{}", path.file_name().unwrap().to_string_lossy());
            let Some(ours) = fx26_check(&program) else {
                unparsed.push(name);
                continue;
            };
            let (ours, rust) = (canon(ours), canon(rust_check(&program)));
            if ours == rust {
                agreed += 1;
            } else {
                report.push(format!("{name}:\n  FX-26 {ours:?}\n  Rust  {rust:?}"));
            }
        }
    }
    eprintln!("{agreed} agree; not parsed by the FX-26 front end: {unparsed:?}");
    assert!(report.is_empty(), "disagreements:\n{}", report.join("\n"));
}

/// The string literals in Rust source that look like programs: a crude
/// scanner, enough for this crate's tests.
fn literals(src: &str) -> Vec<String> {
    let (b, mut out, mut i) = (src.as_bytes(), Vec::new(), 0);
    while i < b.len() {
        if b[i..].starts_with(b"r#\"") {
            let end = src[i + 3..].find("\"#").map_or(b.len(), |e| i + 3 + e);
            out.push(src[i + 3..end].to_string());
            i = end + 2;
        } else if b[i] == b'"' && (i == 0 || b[i - 1] != b'\\') && (i == 0 || b[i - 1] != b'\'') {
            let mut s = String::new();
            let mut j = i + 1;
            while j < b.len() && b[j] != b'"' {
                if b[j] == b'\\' && j + 1 < b.len() {
                    match b[j + 1] {
                        b'n' => s.push('\n'),
                        b't' => s.push('\t'),
                        b'\n' => {
                            j += 2;
                            while j < b.len() && (b[j] == b' ' || b[j] == b'\n') {
                                j += 1;
                            }
                            continue;
                        }
                        c => s.push(c as char),
                    }
                    j += 2;
                } else {
                    let ch = src[j..].chars().next().unwrap();
                    s.push(ch);
                    j += ch.len_utf8();
                }
            }
            out.push(s);
            i = j + 1;
        } else {
            i += 1;
        }
    }
    out.into_iter().filter(|s| s.trim_start().starts_with('(') && !s.contains('{')).collect()
}

/// Every program written into this crate's tests that checks, compiled by
/// the compiler written in FX-26 and run, against the lowering.
#[test]
fn every_program_in_the_tests_compiled() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests");
    let mut programs: Vec<String> = Vec::new();
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|x| x == "rs")).collect();
    names.sort();
    for path in names {
        for l in literals(&std::fs::read_to_string(&path).unwrap()) {
            if !programs.contains(&l) && rust_check(&l).is_ok() {
                programs.push(l);
            }
        }
    }
    let mut compiler = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let (mut report, mut ran) = (Vec::new(), 0);
    for p in &programs {
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        let lowered = match s.run_program(p) {
            Ok(v) => v.unwrap_or_else(|e| format!("!! {e}")),
            Err(_) => continue,
        };
        let Ok(compiled) = compiler.compile_with_own_compiler(p) else { continue };
        ran += 1;
        // A program with no expression is `""` lowered and `#u` compiled;
        // an error is worded by whichever machine found it.
        let norm = |v: &str| {
            if v.is_empty() || v == "#u" {
                "#u".to_string()
            } else if v.starts_with("#<threaded-closure") || v == "#<procedure>" {
                "#<procedure>".to_string()
            } else if v.is_empty() || v == "#u" {
                "#u".to_string()
            } else if v.starts_with("!! ") && !v.starts_with("!! compile") && !v.starts_with("!! check") {
                "!! (an error)".to_string()
            } else {
                v.to_string()
            }
        };
        if norm(&compiled) != norm(&lowered) {
            report.push(format!("{p}\n  compiled {compiled:?}\n  lowered  {lowered:?}"));
        }
    }
    eprintln!("{} programs check; {ran} ran both ways; {} disagree", programs.len(), report.len());
    assert!(report.is_empty(), "disagreements:\n{}", report.join("\n"));
}

/// Every program written into this crate's tests, both checkers, one
/// session: what the Rust tests say is right or wrong, the FX-26 checker
/// must say the same, in the same words, at the same place.
#[test]
fn every_program_in_the_tests() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests");
    let mut programs: Vec<String> = Vec::new();
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|x| x == "rs")).collect();
    names.sort();
    for path in names {
        for l in literals(&std::fs::read_to_string(&path).unwrap()) {
            if !programs.contains(&l) {
                programs.push(l);
            }
        }
    }
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let (mut report, mut unparsed, mut agreed, mut rejected) = (Vec::new(), 0, 0, 0);
    for p in &programs {
        let Some(ours) = fx26_check_in(&mut s, p) else {
            // What the FX-26 front end cannot parse, the Rust one rejects.
            if rust_check(p).is_ok() {
                report.push(format!("{p}\n  the FX-26 front end cannot parse this; the Rust checker accepts it"));
            }
            unparsed += 1;
            continue;
        };
        let (ours, rust) = (canon(ours), canon(rust_check(p)));
        if ours == rust {
            agreed += 1;
            rejected += ours.is_err() as usize;
        } else {
            report.push(format!("{p}\n  FX-26 {ours:?}\n  Rust  {rust:?}"));
        }
    }
    eprintln!("{} programs: {agreed} agree ({rejected} of them rejected), {} disagree, {unparsed} not parsed", programs.len(), report.len());
    assert!(report.is_empty(), "disagreements:\n{}", report.join("\n"));
}

#[test]
#[ignore = "a probe: PROBE_FILE=path, both checkers, timed"]
fn probe_file() {
    let path = std::env::var("PROBE_FILE").expect("PROBE_FILE");
    let program = if path == "front-end" { fixpt_fx26::front_end() } else { std::fs::read_to_string(&path).unwrap() };
    let t = std::time::Instant::now();
    let rust = canon(rust_check(&program));
    eprintln!("Rust: {:.2} s", t.elapsed().as_secs_f64());
    let t = std::time::Instant::now();
    let ours = canon(fx26_check(&program).expect("parses"));
    eprintln!("FX-26: {:.2} s", t.elapsed().as_secs_f64());
    match (&ours, &rust) {
        (Ok(a), Ok(b)) => {
            eprintln!("{} and {} lines", a.len(), b.len());
            for (x, y) in a.iter().zip(b) {
                if x != y {
                    eprintln!("first difference:\n  FX-26 {x}\n  Rust  {y}");
                    break;
                }
            }
        }
        _ => eprintln!("FX-26 {:?}\nRust  {:?}", ours.as_ref().err(), rust.as_ref().err()),
    }
    assert_eq!(ours, rust);
}
