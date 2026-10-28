//! The checker written in FX-26 (`src/check-*.fx`), reading and parsing with
//! the reader and the parser written in FX-26, against the Rust checker on
//! the same programs (`PLAN.md` §11, step 10).

use fixpt_fx26::session::compile_program_as;

/// Where byte `at` of the front end is, as `file:line:column`.
fn locate(at: usize) -> String {
    let parts = fixpt_fx26::FRONT_END_FILES;
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

mod common;

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_fx26::Checker;
use fixpt_read::FileId;

/// The Rust checker on `program`, in the same terms as the FX-26 one.
fn rust_check(program: &str) -> Result<Vec<String>, (String, u32, u32)> {
    rust_check_in(Checker::new(), program)
}

fn rust_check_in(mut c: Checker, program: &str) -> Result<Vec<String>, (String, u32, u32)> {
    fixpt_fx26::compare::check_with_rust_checker(&mut c, program).map_err(|e| (e.message, e.span.start, e.span.end))
}

/// The FX-26 checker on `program`; `None` if the FX-26 front end cannot
/// parse it.
fn fx26_check(program: &str) -> Option<Result<Vec<String>, (String, u32, u32)>> {
    common::with_own(|s| fx26_check_in(s, program))
}

fn fx26_check_in(s: &mut Fx26Session, program: &str) -> Option<Result<Vec<String>, (String, u32, u32)>> {
    let r = s.check_with_own_checker(program).ok()?;
    Some(r.map_err(|e| (e.message, e.span.start, e.span.end)))
}

fn canon(r: Result<Vec<String>, (String, u32, u32)>) -> Result<Vec<String>, (String, u32, u32)> {
    use fixpt_fx26::compare::canonical;
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
    // Two naturals add to a natural of their sum.
    assert_eq!(both("(+ 1 2)"), Ok(vec!["(nat 3) ! pure".to_string()]));
    let _ = both("(define f (subr spin (int) int) (lambda (n) (if (= n 0) 1 (* n (f (- n 1)))))) (f 10)");
    let _ = both("(the (listof int @l) (cons 1 (cons 2 nil)))");
    let _ = both("(car (cons 1 #t))");
    let _ = both("(let ((r (the (ref int @r) (new 1)))) (begin (set r (+ (get r) 41)) (get r)))");
    let _ = both("(extract (product (a 1) (b \"two\")) b)");
    let _ = both("(if 1 2 3)");
    let _ = both("(+ 1 #t)");
    let _ = both("(lambda (x) x)");
    // A `letrec`'s body is checked against what is expected, as a `let`'s
    // is (PLAN.md Q11): `nil` in one branch knows which list it is.
    let lr = "(define* f (subr (alloc @l) (bool) (listof int @l))\n  (lambda (b) (letrec ((g (subr pure () int) (lambda () 1))) (if b nil (cons (g) nil)))))";
    assert!(both(lr).is_ok(), "{lr}");
    // A `let` passes a `poly` to its body, a `plambda` here, and must be pure.
    let pl = "(define id (poly ((t type)) (subr pure (t) t))\n  (let ((k 1)) (plambda ((t type)) (lambda (x) x))))\n((proj id int) 5)";
    assert!(both(pl).is_ok(), "{pl}");
    // An effect mismatch says, on a line of its own, what is beyond what is
    // expected.
    let dl = "(define* twice (subr pure (int) int) (lambda (n) (* 2 n)))\n(define* apply1 (subr pure ((subr pure (int) int)) int) (lambda (f) (f 1)))\n(apply1 (lambda ((n int)) (twice n)))";
    let e = both(dl).expect_err("refused");
    assert!(e.0.ends_with("\n  beyond what is expected, it has (read (globals twice))"), "{e:?}");
}

/// A text the FX-26 reader does not finish is blamed where the Rust reader
/// places it, not at 1:1 (PLAN.md Q11, `DONE.md` §15).
#[test]
fn reader_errors_say_where() {
    let at = |p: &str| common::with_own(|s| s.check_with_own_checker(p).err()).map(|e| (e.message, e.span.start));
    assert_eq!(at("(define x 1)\n(+ x 1))"), Some(("unbalanced `)`".to_string(), 20)));
    assert_eq!(at("(define x 1)\n(define y (+ x 2)\n(+ y 1)"), Some(("unterminated list, expected `)`".to_string(), 13)));
}

/// A shape conflict between a polymorphic call's result and what its context
/// expects is the error, before any binder left unsolved (`DONE.md` §20):
/// once, "argument 2 must be a t2, which is not yet known here".
#[test]
fn a_shape_conflict_is_the_error() {
    let e = both("(list 1 (cons 2 nil))").expect_err("refused");
    assert_eq!(e.0, "this is a (pairof int ? r), where a int is expected", "{e:?}");
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
    for sub in ["bidirectional", "bloblet", "control", "run", "pldi89", "regions", "datum", "recursive", "terminate", "generative", "lemmas", "sizes", "conventions", "redefine", "modules", "higher-kinds", "unions", "io", "processes", "arrows", "specs"] {
        let mut names: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
        names.sort();
        for path in names {
            let program = std::fs::read_to_string(&path).unwrap();
            let name = format!("{sub}/{}", path.file_name().unwrap().to_string_lossy());
            // A `load-module`'s path is from the program's directory, as
            // `fixpt check`'s is: else every load is "cannot read" in both,
            // and the files loaded are never compared.
            let dir = path.parent().map(|d| d.to_path_buf());
            let Some(ours) = common::with_own(|s| {
                let outer = std::mem::replace(&mut s.checker.base_dir, dir.clone());
                let r = fx26_check_in(s, &program);
                s.checker.base_dir = outer;
                r
            }) else {
                unparsed.push(name);
                continue;
            };
            let mut c = Checker::new();
            c.base_dir = dir;
            let (ours, rust) = (canon(ours), canon(rust_check_in(c, &program)));
            if ours == rust {
                agreed += 1;
            } else {
                report.push(format!("{name}:\n  FX-26 {ours:?}\n  Rust  {rust:?}"));
            }
        }
    }
    eprintln!("{agreed} agree; not parsed by the FX-26 front end: {unparsed:?}");
    assert!(report.is_empty(), "disagreements:\n{}", report.join("\n"));
    // A front end that does not load parses nothing, and so disagrees with
    // nothing: that is a failure too.
    assert!(unparsed.len() <= 5 && agreed >= 150, "only {agreed} compared; not parsed: {unparsed:?}");
}

/// What is wrong with a message's shape, if anything (`docs/fx26.md`,
/// "Messages"): its first line must stand alone, since the REPL shows only
/// that line under a form as it is typed, and later lines are indented
/// details.
fn message_shape(message: &str) -> Option<&'static str> {
    let mut lines = message.split('\n');
    let first = lines.next().unwrap_or("");
    if first.trim().is_empty() {
        Some("the first line is empty")
    } else if first.starts_with(' ') || first.ends_with(' ') {
        Some("the first line has space around it")
    } else if first.ends_with(':') {
        Some("the first line is a header, not the error")
    } else if lines.any(|l| !l.starts_with("  ") || l.trim().is_empty()) {
        Some("a later line is blank or not indented two spaces")
    } else {
        None
    }
}

/// Every refusal in the test programs, and in the tests' inline programs,
/// has a first line that stands alone. The checkers agree word for word
/// (`every_test_program`), so the Rust checker's messages speak for both.
#[test]
fn messages_have_a_usable_first_line() {
    assert!(message_shape("a is expected\n  beyond, b").is_none());
    for bad in ["", "in this definition:\n  a", "a\nb", "a\n\n  b"] {
        assert!(message_shape(bad).is_some(), "{bad:?}");
    }
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests");
    let mut programs: Vec<(String, String)> = Vec::new();
    for entry in std::fs::read_dir(format!("{dir}/programs")).unwrap() {
        let sub = entry.unwrap().path();
        let Ok(files) = std::fs::read_dir(&sub) else { continue };
        for f in files {
            let path = f.unwrap().path();
            if path.extension().is_some_and(|x| x == "fx") {
                programs.push((path.display().to_string(), std::fs::read_to_string(&path).unwrap()));
            }
        }
    }
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|x| x == "rs") {
            for l in literals(&std::fs::read_to_string(&path).unwrap()) {
                programs.push((path.display().to_string(), l));
            }
        }
    }
    let (mut refused, mut report) = (0, Vec::new());
    for (name, p) in &programs {
        if let Err((message, ..)) = rust_check(p) {
            refused += 1;
            if let Some(why) = message_shape(&message) {
                report.push(format!("{name}: {why}: {message:?}"));
            }
        }
    }
    eprintln!("{refused} refusals looked at");
    assert!(refused >= 100, "only {refused} refusals found");
    assert!(report.is_empty(), "messages whose first line does not stand alone:\n{}", report.join("\n"));
}

/// The front end's checker run as register code
/// (`Fx26Session::front_end_compiled`) says what it says run as lowered
/// Scheme, on programs that check and one that does not.
#[test]
fn the_front_end_compiled_checks_alike() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let programs = ["run/recursion.fx", "sizes/solved-by-test.fx", "sizes/solved-negative.fx", "native/many-values.fx"];
    let mut s = common::session();
    // Lowered, as every session was before `common::session`.
    let mut low = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for p in programs {
        let text = std::fs::read_to_string(format!("{dir}/{p}")).unwrap();
        let compiled = canon(fx26_check_in(&mut s, &text).expect("parses"));
        let lowered = canon(fx26_check_in(&mut low, &text).expect("parses"));
        assert_eq!(compiled, lowered, "{p}");
    }
    assert!(s.scheme.is_bound("fx26-native:check-program"), "the compiled front end was used");
    assert!(!low.scheme.is_bound("fx26-native:check-program"), "the lowered one was");
}

/// `cwcc` and the `certify-*` operations, whose rules are checked at each
/// call where they are named, are named nowhere else: bound to another name,
/// a call escaped its rule (F15: a `pure` loop through `cwcc`; F16: `(cn -3)`
/// a `nat`). Both checkers agree (`every_test_program`).
#[test]
fn second_class_operations_are_named_only_to_call() {
    for program in [include_str!("programs/control/cwcc-alias.fx"), include_str!("programs/sizes/certify-nat-alias.fx")] {
        let err = rust_check(program).expect_err("refused");
        assert!(err.0.contains("is named only to call it"), "{err:?}");
    }
    for ok in ["(cwcc (lambda ((k (subr (goto @k) (int) void))) 1))", "((proj (proj (proj cwcc @k) int) pure) (lambda ((k (subr (goto @k) (int) void))) 1))"] {
        rust_check(ok).unwrap_or_else(|e| panic!("{ok}: {e:?}"));
    }
}

/// `#%fx` (`TODO.md` §46): only `(with #%fx name)`, of a standard name;
/// a second-class operation through it only as an operator; never bound.
/// Both checkers say the same, as `every_test_program` compares.
#[test]
fn the_standard_module_is_used_only_so() {
    for (program, why) in [
        ("(with #%fx cwcc)", "is named only to call it"),
        ("(with #%fx (+ 1 2))", "names one standard binding"),
        ("(with #%fx nope)", "names one standard binding"),
        ("(let ((#%fx 1)) (with #%fx =))", "which nothing else may be"),
    ] {
        let err = both(program).expect_err(program);
        assert!(err.0.contains(why), "{program}: {err:?}");
    }
}

/// The size and union programs that say, on their first line, that they
/// are `Rejected` or `Accepted` are so, by the Rust checker (the FX-26 one
/// agrees, `every_test_program`).
#[test]
fn size_programs_as_they_say() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut wrong = Vec::new();
    let paths = ["sizes", "unions"].iter().flat_map(|d| std::fs::read_dir(format!("{dir}/{d}")).unwrap().map(|e| e.unwrap().path()));
    for path in paths {
        let program = std::fs::read_to_string(&path).unwrap();
        let refused = rust_check(&program).is_err();
        let said = if program.starts_with("; Rejected") {
            true
        } else if program.starts_with("; Accepted") {
            false
        } else {
            continue;
        };
        if refused != said {
            wrong.push(path.file_name().unwrap().to_string_lossy().to_string());
        }
    }
    assert!(wrong.is_empty(), "not as their first line says: {wrong:?}");
}

/// With `native` the program's convention (a `nativecc` machine), the
/// two checkers agree on the conventions' programs too.
#[test]
fn conventions_agree_when_native() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/conventions");
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    let mut report = Vec::new();
    let mut s = common::session();
    s.set_native_convention(true);
    for path in names {
        let program = std::fs::read_to_string(&path).unwrap();
        let ours = canon(fx26_check_in(&mut s, &program).expect("parses"));
        let rust = canon(rust_check_in(Checker::with_convention(fixpt_fx26::ast::Conv::Native), &program));
        if ours != rust {
            report.push(format!("{}:\n  FX-26 {ours:?}\n  Rust  {rust:?}", path.display()));
        }
    }
    assert!(report.is_empty(), "disagreements:\n{}", report.join("\n"));
}

/// With naming a global reading it, the two checkers agree on the globals'
/// programs.
#[test]
fn globals_agree_when_read() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/globals");
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    let mut report = Vec::new();
    let mut s = common::session();
    s.set_globals_effects(true);
    for path in names {
        let program = std::fs::read_to_string(&path).unwrap();
        let ours = canon(fx26_check_in(&mut s, &program).expect("parses"));
        let mut c = Checker::new();
        c.globals_effects = true;
        let rust = canon(rust_check_in(c, &program));
        // A local `letrec`'s globals found, through a call of a sibling.
        if path.ends_with("letrec-reads-found.fx") {
            let want = "define f : (subr (read (globals twice)) (nat) int) ! pure";
            assert!(ours.as_ref().is_ok_and(|ls| ls.iter().any(|l| l == want)), "{ours:?}");
        }
        if path.ends_with("inferred.fx") {
            let want = "define clamp : (subr (read (globals below limit)) (int) int) ! pure";
            assert!(ours.as_ref().is_ok_and(|ls| ls.iter().any(|l| l == want)), "{ours:?}");
        }
        if ours != rust {
            report.push(format!("{}:\n  FX-26 {ours:?}\n  Rust  {rust:?}", path.display()));
        }
    }
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
    let mut compiler = common::session();
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
            } else if v.starts_with("#<cellular-closure") || v == "#<procedure>" {
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
    let mut s = common::session();
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

/// Every program meant to run checks: one that stopped checking is refused
/// alike by both checkers, which the agreement above cannot tell from one
/// meant to be refused (as `run/letregion.fx` was, for years of commits,
/// once `sum` became syntax).
#[test]
fn every_program_meant_to_run_checks() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut report = Vec::new();
    // A program that declares the other machine's convention is refused
    // here, at its `define-convention`, as it is meant to be.
    let other = if cfg!(target_arch = "x86_64") { "(target arm64)" } else { "(target x86_64)" };
    for sub in ["run", "bench", "bidirectional", "native", "groups", "made-code", "made-code-x86_64"] {
        let mut names: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
        names.sort();
        for path in names {
            let program = std::fs::read_to_string(&path).unwrap();
            if program.lines().any(|l| l.trim() == other) {
                if !rust_check(&program).is_err_and(|(m, _, _)| m.contains("is not this implementation's")) {
                    report.push(format!("{sub}/{}: declares {other}, and checks", path.file_name().unwrap().to_string_lossy()));
                }
                continue;
            }
            if let Err((m, a, _)) = rust_check(&program) {
                report.push(format!("{sub}/{}: at {a}: {m}", path.file_name().unwrap().to_string_lossy()));
            }
        }
    }
    assert!(report.is_empty(), "programs meant to run that do not check:\n{}", report.join("\n"));
}

/// The two checkers summarize each expression's effect alike, for a
/// compiler (`Checker::effect_summaries`, `checked-effects`): pure, reads
/// only, or anything else, by span (in characters), the greater where two
/// expressions share one.
#[test]
fn effect_summaries_agree() {
    use std::collections::HashMap;
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut s = common::session();
    let (mut report, mut both, mut only_fx, mut only_rust) = (Vec::new(), 0, 0, 0);
    let mut programs = Vec::new();
    for sub in ["run", "bench", "bidirectional", "control", "pldi89", "datum", "modules", "higher-kinds"] {
        let mut names: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
        names.sort();
        programs.extend(names.into_iter().map(|p| (format!("{sub}/{}", p.file_name().unwrap().to_string_lossy()), std::fs::read_to_string(&p).unwrap())));
    }
    let t = std::time::Instant::now();
    for (name, program) in programs {
        // A module read from a file has spans in that file, which the Rust
        // checker's summaries do not tell apart from the program's.
        if program.contains("(load-module") {
            continue;
        }
        {
            let Ok(Ok(_)) = s.check_with_own_checker(&program) else { continue };
            let mut fx: HashMap<(u32, u32), i64> = HashMap::new();
            for (a, b, k) in s.own_effect_summaries().expect("notes") {
                let e = fx.entry((a as u32, b as u32)).or_insert(k);
                *e = (*e).max(k);
            }
            let mut c = Checker::new();
            let forms = c.read_in(FileId(0), &program).expect("reads");
            let done = c.declare_ahead(&forms).expect("declares");
            for (f, d) in forms.iter().zip(done) {
                if !d {
                    c.top_all(f).expect("checks");
                }
            }
            // Bytes to characters, as the FX-26 reader counts.
            let mut char_at = vec![0u32; program.len() + 1];
            let mut n = 0;
            for (b, ch) in program.char_indices() {
                for x in &mut char_at[b..b + ch.len_utf8()] {
                    *x = n;
                }
                n += 1;
            }
            char_at[program.len()] = n;
            let mut rust: HashMap<(u32, u32), i64> = HashMap::new();
            for ((f, a, b), k) in c.effect_summaries() {
                if f != 0 {
                    continue;
                }
                let e = rust.entry((char_at[a as usize], char_at[b as usize])).or_insert(k as i64);
                *e = (*e).max(k as i64);
            }
            for (span, k) in &fx {
                match rust.get(span) {
                    Some(r) if r == k => both += 1,
                    Some(r) => report.push(format!("{name} {span:?}: FX-26 {k}, Rust {r}")),
                    None => only_fx += 1,
                }
            }
            only_rust += rust.keys().filter(|k| !fx.contains_key(k)).count();
        }
    }
    eprintln!("effect summaries: {both} agree; noted only by FX-26 {only_fx}, only by Rust {only_rust}; {:.1} s", t.elapsed().as_secs_f64());
    assert!(both > 1000, "only {both} compared");
    assert!(report.is_empty(), "{} disagreements:\n{}", report.len(), report.iter().take(40).cloned().collect::<Vec<_>>().join("\n"));
}

/// `define-convention` (`TODO.md` §97, `docs/research/
/// declared-conventions.md`): the native convention's clauses, in any
/// order, name it; anything else is refused, alike by both checkers, at the
/// first clause by role that differs.
#[test]
fn declared_conventions_alike() {
    let clauses: Vec<&str> = fixpt_runtime::NATIVE_CONVENTION.lines().collect();
    let program = |cs: &[String]| {
        format!(
            "(define-convention kayak-arm64\n  {})\n(the (subr (conv kayak-arm64) pure (int) int) (native-procedure (seal-code (make-bloblet 8))))",
            cs.join("\n  ")
        )
    };
    let own: Vec<String> = clauses.iter().map(|c| c.to_string()).collect();
    let accepted = both(&program(&own));
    assert!(accepted.as_ref().is_ok_and(|ls| ls.last().is_some_and(|l| l.contains("(conv native)") && l.contains("(io native)"))), "{accepted:?}");
    let reversed: Vec<String> = own.iter().rev().cloned().collect();
    assert!(both(&program(&reversed)).is_ok());
    let refused = |cs: Vec<String>, says: &str| {
        let r = both(&program(&cs));
        assert!(r.as_ref().is_err_and(|(m, _, _)| m.contains(says)), "{says}: {r:?}");
    };
    let with = |f: &dyn Fn(&mut Vec<String>)| {
        let mut cs = own.clone();
        f(&mut cs);
        cs
    };
    refused(with(&|cs| cs[1] = cs[1].replace("(lost-across-calls all-but-pinned)", "(lost-across-calls all)")), "the `registers` clause is not this implementation's");
    refused(with(&|cs| cs.retain(|c| !c.starts_with("(barrier"))), "no `barrier` clause, which this implementation's convention has");
    refused(with(&|cs| cs.push("(colour blue)".into())), "has no `colour` clause");
    refused(with(&|cs| cs.push("(target arm64)".into())), "two `target` clauses");
    refused(with(&|cs| cs[0] = "(target \"arm64\")".into()), "holds names, integers and lists");
    refused(with(&|cs| cs[0] = "(target #t)".into()), "holds names, integers and lists");
    refused(with(&|cs| cs[0] = "target".into()), "a convention's clause is `(role …)`");
    // The other machine's declaration: its first clause by role that
    // differs, `code`'s (where the code distance is).
    let other = if cfg!(target_arch = "x86_64") { fixpt_runtime::NATIVE_CONVENTION_ARM64 } else { fixpt_runtime::NATIVE_CONVENTION_X86_64 };
    refused(other.lines().map(String::from).collect(), "the `code` clause is not this implementation's");
}

/// Both checkers on a runtime's own program (`--syscalls`), which may
/// declare syscalls (`docs/research/syscalls.md`).
fn both_syscalls(program: &str) -> Result<Vec<String>, (String, u32, u32)> {
    let ours = common::with_own(|s| {
        s.checker.syscalls = true;
        let r = fx26_check_in(s, program);
        s.checker.syscalls = false;
        r
    });
    let ours = canon(ours.unwrap_or_else(|| panic!("the FX-26 front end cannot parse:\n{program}")));
    let mut c = Checker::new();
    c.syscalls = true;
    let rust = canon(rust_check_in(c, program));
    assert_eq!(ours, rust, "the checkers disagree on:\n{program}");
    ours
}

/// Syscalls' declarations (`docs/research/syscalls.md`), alike in both
/// checkers: what they accept, and each refusal, at the same place.
#[test]
fn syscall_declarations_alike() {
    let ok = "(define-optional-syscall pw \"code:page-words/1\" (subr (io sys) () int))\n(syscall-available? pw)";
    let lines = both_syscalls(ok).expect("accepted");
    assert_eq!(lines, ["define pw : (subr (io sys) () int) ! pure", "bool ! (read (globals %syscall-available:pw))"]);
    // A pure one, called from a pure procedure, which stays so; its call's
    // operator noted as the plain `%syscall1` in both.
    let pure = "(define-syscall n \"test:n/1\" (subr pure (string) int))\n\
                (define* twice (subr pure (string) int) (lambda (s) (+ (n s) (n s))))";
    let lines = both_syscalls(pure).expect("accepted");
    assert_eq!(lines, ["define n : (subr pure (string) int) ! pure", "define twice : (subr (read (globals n)) (string) int) ! pure"]);
    // Only a runtime's own code declares them.
    let e = both(ok).expect_err("refused");
    assert_eq!(e.0, "syscalls are declared only by a runtime's own code");
    let refused = |program: &str, says: &str| {
        let r = both_syscalls(program);
        assert!(r.as_ref().is_err_and(|(m, _, _)| m.contains(says)), "{says}: {program}: {r:?}");
    };
    let declared = |ty: &str| format!("(define-syscall f \"test:f/1\" {ty})");
    refused("(define-syscall f \"test:f/1\")", "`(define-syscall name \"host-name\" type)`");
    refused("(define-optional-syscall f)", "`(define-optional-syscall name \"host-name\" type)`");
    refused("(define-syscall 5 \"test:f/1\" (subr (io sys) () int))", "expected a name");
    for host in ["\"test\"", "\"Test:f/1\"", "\"test:f/01\"", "\"test:f/\"", "\"test::f/1\"", "5"] {
        refused(&format!("(define-syscall f {host} (subr (io sys) () int))"), "a syscall's host name is a string");
    }
    let shape = "a syscall's type is a `subr`, or a `poly` over regions only of one";
    refused(&declared("int"), shape);
    refused(&declared("(poly ((t type)) (subr (io sys) (t) t))"), shape);
    refused(&declared("(subr (conv native) (io sys) () int)"), shape);
    let effects = "a syscall's effect holds only reads, writes and allocations of its regions";
    refused(&declared("(subr (maxeff (io sys) (goto @k)) () int)"), effects);
    refused(&declared("(subr (goto @k) () int)"), effects);
    let crossing = "a syscall takes and gives only";
    refused(&declared("(subr (io sys) ((listof int @l)) int)"), crossing);
    refused(&declared("(poly ((r region)) (subr (io sys) ((flatarrayof u64 r)) int))"), crossing);
    refused(&declared("(subr (io sys) () f64)"), crossing);
    refused(&declared("(subr (io sys) ((flatarrayof i64 @k)) int)"), "a syscall's regions are its `poly`'s");
    refused(&declared("(subr (io sys) (int int int int int int int) int)"), "a syscall takes at most 6 arguments");
    // Asked of a name declared, and only by a runtime's own code made.
    let usage = "`syscall-available?` takes the name of a syscall declared";
    refused("(define g 1)\n(syscall-available? g)", usage);
    refused("(syscall-available? 5)", usage);
    refused("(syscall-available?)", usage);
    refused("(%syscall0 \"l\" \"code:page-words/1\" \"(subr (io sys) () int)\")", "unbound variable `%syscall0`");
}

/// `native-procedure` (`TODO.md` §97) makes a native closure: its stated
/// type says so, `(conv native)` (or a name declared as it) or `fx`; the
/// program's own convention, `cellular`, is refused, and so is no type.
#[test]
fn a_made_procedure_is_native() {
    for made in [
        "(the (subr (conv native) pure (int int) int) (native-procedure (seal-code (make-bloblet 8))))",
        "(the (subr (conv fx) pure (int int) int) (native-procedure (seal-code (make-bloblet 8))))",
    ] {
        assert!(both(made).is_ok(), "{made}");
    }
    for made in [
        "(the (subr pure (int int) int) (native-procedure (seal-code (make-bloblet 8))))",
        "(the (subr (conv cellular) pure (int int) int) (native-procedure (seal-code (make-bloblet 8))))",
    ] {
        let r = both(made);
        assert!(r.as_ref().is_err_and(|(m, _, _)| m.contains("state `(conv native)`")), "{made}: {r:?}");
    }
    let r = both("(native-procedure (seal-code (make-bloblet 8)))");
    assert!(r.as_ref().is_err_and(|(m, _, _)| m.contains("`t` cannot be inferred")), "{r:?}");
    let r = both("(the int (native-procedure (seal-code (make-bloblet 8))))");
    assert!(r.as_ref().is_err_and(|(m, _, _)| m.contains("makes a procedure, of the type stated")), "{r:?}");
    let r = both("(let ((f native-procedure)) 1)");
    assert!(r.is_err(), "{r:?}");
}
