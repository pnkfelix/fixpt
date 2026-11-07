//! The parser written in FX-26 (`src/parser.fx`) makes the Rust parser's
//! trees, desugarings and spans included (`PLAN.md` §11, step 9a).

use fixpt_engine::Backend;
use fixpt_fx26::Checker;
use fixpt_fx26::ids::Kth;
use fixpt_fx26::sexp::{Chars, show_top};
use fixpt_fx26::session::Fx26Session;
use fixpt_read::FileId;

/// The Rust parser's trees for `text`, checking each form as it goes, which
/// is how the Rust side parses.
fn rust_trees(text: &str, base: i64) -> Vec<String> {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), text).expect("reads");
    c.declare_ahead(&forms).expect("declares");
    let mut c2 = Checker::new();
    let forms2 = c2.read_in(FileId(0), text).expect("reads");
    let chars = Chars::of(text);
    // The forms as read, before the Rust checker expands any into several
    // (a `define-generative`'s conversions, each at its span): a form is
    // what the FX-26 parser takes as one, and what a reading folds.
    let mut names = fixpt_read::Interner::new();
    let read = fixpt_read::Reader::new(text, FileId(0), fixpt_read::SyntaxProfile::FX26, &mut names).read_all().expect("reads");
    let mut forms: Vec<(usize, Vec<_>)> = Vec::new();
    for f in &forms2 {
        let top = c2.top(f).unwrap_or_else(|e| panic!("checks: {e}"));
        let within = |r: &fixpt_read::Syntax| r.span.start <= f.span.start && f.span.end <= r.span.end;
        let i = read.iter().position(within).unwrap_or_else(|| panic!("a form as read: {:?} in {text}", f.span));
        if forms.last().is_none_or(|(j, _)| *j != i) {
            forms.push((i, Vec::new()));
        }
        // The hidden globals of the files it loads first, defined before
        // all it makes.
        let group = &mut forms.last_mut().expect("one").1;
        let hoisted: Vec<_> = std::mem::take(&mut c2.hoisted).into_iter().map(|(t, h)| (t, h.span, true)).collect();
        let at = group.iter().position(|g: &(_, _, bool)| !g.2).unwrap_or(group.len());
        group.splice(at..at, hoisted);
        group.push((top, f.span, false));
    }
    // Each expression's key, form by form, as the process's mode makes it:
    // read in the standard environment's state, as the FX-26 parser here
    // reads it (`syn::parse_to_trees`), after `base` the parser walked before.
    let mut kth = Kth::keyed(fixpt_fx26::ids::mode(), base);
    let mut s = fixpt_fx26::ids::standard_state();
    for (i, group) in &forms {
        let tops: Vec<_> = group.iter().map(|(t, _, _)| t).collect();
        let hoisted: Vec<_> = group.iter().filter(|g| g.2).map(|(t, _, _)| t).collect();
        let loads = fixpt_fx26::ids::form_loads(&c2, &hoisted);
        s = fixpt_fx26::ids::form_reading(s, &Default::default(), &read[*i], &names, &loads);
        kth.form(&c2, s, &tops);
    }
    forms.iter().flat_map(|(_, g)| g).map(|(t, span, _)| show_top(&c2, &chars, t, *span, &kth)).collect()
}

/// `tree` without the FX-26 parser's marks of where a loaded file's
/// positions start, `[k·10⁹ (path) () ()] `: its file ids, which the Rust
/// parser keeps in spans instead (`parser.fx`, `load-base`).
fn without_file_marks(tree: &str) -> String {
    let mut out = String::new();
    let mut rest = tree;
    while let Some(i) = rest.find('[') {
        out.push_str(&rest[..i]);
        let tail = &rest[i..];
        let digits: String = tail[1..].chars().take_while(|c| c.is_ascii_digit()).collect();
        let mark = digits.parse::<u64>().is_ok_and(|n| n >= 1_000_000_000 && n % 1_000_000_000 == 0);
        match tail.find("] ").filter(|_| mark).or_else(|| tail.find(']').filter(|_| mark)) {
            Some(end) => rest = tail[end + 1..].trim_start_matches(' '),
            None => {
                out.push('[');
                rest = &tail[1..];
            }
        }
    }
    out.push_str(rest);
    out
}

/// `tree` with each place in a loaded file, `k·10⁹ + i`, as `i`: the Rust
/// parser's spans keep the file apart, and show the place in it alone. An
/// expression's place is the first two of the four numbers that end it
/// (its start and end, then its key, a number and a reading: `sexp.rs`).
fn within_files(tree: &str) -> String {
    let b = tree.as_bytes();
    let mut out = String::new();
    // `tree[..copied]` is in `out`; `run`, the numbers in a row before here.
    let (mut copied, mut run) = (0, Vec::<(usize, usize)>::new());
    let mut i = 0;
    while i < b.len() {
        if b[i].is_ascii_digit() && i > 0 && (b[i - 1] == b' ' || b[i - 1] == b'-') {
            let start = i;
            while i < b.len() && b[i].is_ascii_digit() {
                i += 1;
            }
            run.push((start, i));
            continue;
        }
        if b[i] == b')' && run.len() >= 4 && run.last().map(|r| r.1) == Some(i) {
            for &(start, end) in &run[run.len() - 4..run.len() - 2] {
                out.push_str(&tree[copied..start]);
                let n: u64 = tree[start..end].parse().unwrap_or(0);
                out.push_str(&(if n >= 1_000_000_000 { n % 1_000_000_000 } else { n }).to_string());
                copied = end;
            }
        }
        if b[i] != b' ' {
            run.clear();
        }
        i += 1;
    }
    out.push_str(&tree[copied..]);
    out
}

fn same_trees(s: &mut Fx26Session, text: &str) {
    let (ours, base) = s.parse_with_own_parser_from(text).unwrap_or_else(|e| panic!("the FX-26 parser: {e}"));
    let ours: Vec<String> = ours.iter().map(|t| within_files(&without_file_marks(t))).collect();
    let rust: Vec<String> = rust_trees(text, base).iter().map(|t| within_files(t)).collect();
    assert_eq!(ours.len(), rust.len(), "different numbers of forms");
    for (a, b) in ours.iter().zip(&rust) {
        assert_eq!(a, b, "the parsers disagree");
    }
}

#[test]
fn the_parsers_agree_on_small_programs() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for text in [
        "(+ 1 2)",
        "(define x int 5) (define y (+ x 1)) (if #t x y)",
        "(let* ((a 1) (b (+ a 1))) (and (= a b) (or #f #t) (and)))",
        "(cond ((= 1 2) 'no) (else 'yes))",
        "(the (subr pure (int bool) unit) (lambda ((x int) y) x #u))",
        "(product (a 1) (2 #\\c)) (sum t \"s\") (extract (product (a 1)) a)",
        "(tagcase (the (sumof (a int) (b (productof (1 int) (2 int)))) (sum a 1)) (a n n) (b (x y) (+ x y)))",
        "(tagcase (the (sumof (a int) (b int)) (sum a 1)) (a n n) (else r 0))",
        "(bloblet-ref (make-bloblet 0 1 2) 1)",
        "(letrec ((f (subr pure (int) int) (lambda (n) n))) (f 1))",
        "(proj (plambda ((r region)) (lambda () 1)) @q)",
        "(define-generative (box (t type +)) (productof (v t))) (down-box (up-box (product (v 1))))",
        "(define f (subr pure ((listof int const)) int) (lambda (xs) (acyclic xs (ok 1) 0)))",
    ] {
        same_trees(&mut s, text);
    }
}

#[test]
fn the_parsers_agree_on_real_programs() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for text in [
        include_str!("programs/bidirectional/twice.fx"),
        include_str!("programs/bloblet/point.fx"),
        include_str!("programs/bloblet/array-sum.fx"),
        include_str!("programs/bloblet/else-narrows.fx"),
        include_str!("programs/modules/counter.fx"),
        include_str!("programs/modules/parameter.fx"),
        include_str!("programs/modules/import.fx"),
        include_str!("programs/modules/rec.fx"),
        include_str!("programs/modules/select.fx"),
        include_str!("programs/modules/transparent.fx"),
        include_str!("programs/run/case.fx"),
        include_str!("programs/run/case-tree.fx"),
        include_str!("programs/run/standard-refs.fx"),
        include_str!("programs/sizes/fresh-temporaries.fx"),
        fixpt_fx26::TABLE,
    ] {
        same_trees(&mut s, text);
    }
}

#[test]
fn a_parse_error_says_where() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let err = s.parse_with_own_parser("(if 1 2)").expect_err("too short");
    assert_eq!(err.message, "`(if test then else)`");
    assert_eq!((err.span.start, err.span.end), (0, 8));
    let err = s.parse_with_own_parser("(cond (#t 1))").expect_err("no else");
    assert!(err.message.contains("must end with an `else`"), "{}", err.message);
}

/// A `module` or a `with` the parsers refuse, each saying the same, at the
/// same place, as the Rust checker reading it.
#[test]
fn module_parse_errors_agree() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for text in [
        "(module (define))",
        "(module 5)",
        "(module (define-rec 5))",
        "(module (define-rec (f int)))",
        "(module (define-generative (t) int))",
        "(module (define-type 3 int))",
        "(with (module (define x 1)) x)",
        "(with)",
        "(define m (module)) (with m)",
    ] {
        let ours = s.parse_with_own_parser(text).expect_err("refused");
        let mut c = Checker::new();
        let forms = c.read_in(FileId(0), text).expect("reads");
        let rust = forms.iter().find_map(|f| c.top(f).err()).expect("refused");
        assert_eq!((ours.message, ours.span.start, ours.span.end), (rust.message, rust.span.start, rust.span.end), "{text}");
    }
}

/// A `case` the parsers refuse (`TODO.md` §46), each saying the same, at
/// the same place.
#[test]
fn case_parse_errors_agree() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for text in [
        "(case)",
        "(case 1)",
        "(case 1 ((1) 2))",
        "(case 1 ((1) 2) (else 3) (else 4))",
        "(case 1 (() 2) (else 4))",
        "(case 1 (3 3) (else 4))",
        "(case 1 ((1) 2) ((1) 3) (else 4))",
        "(case 1 ((1) 2) ((a) 3) (else 4))",
        "(case 'a ((a b a) 2) (else 4))",
        "(case 1 ((#u) 2) (else 4))",
        "(case 1 ((1.5) 2) (else 4))",
        "(case 1 (((1)) 2) (else 4))",
        "(case #t ((#t #f #t) 2) (else 4))",
    ] {
        let ours = s.parse_with_own_parser(text).expect_err("refused");
        let mut c = Checker::new();
        let forms = c.read_in(FileId(0), text).expect("reads");
        let rust = forms.iter().find_map(|f| c.top(f).err()).expect("refused");
        assert_eq!((ours.message, ours.span.start, ours.span.end), (rust.message, rust.span.start, rust.span.end), "{text}");
    }
}

/// No `define-datatype` variant is named by a type form, in either parser
/// (`TODO.md` §190): `(define-datatype var (oneof symbol pat))` would be
/// one variant, `oneof`. Each of `parse.rs`'s type forms, so that
/// `parser.fx`'s list of them cannot fall behind.
#[test]
fn a_variant_named_by_a_type_form_is_refused() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for form in fixpt_fx26::parse::TYPE_FORMS {
        let text = format!("(define-datatype t (x int) ({form} int))");
        let ours = s.parse_with_own_parser(&text).expect_err(&text);
        let mut c = Checker::new();
        let rust = match c.read_in(FileId(0), &text) {
            Err(e) => e,
            Ok(forms) => forms.iter().find_map(|f| c.top(f).err()).expect(&text),
        };
        assert!(rust.message.contains("is a type form"), "{text}: {}", rust.message);
        assert_eq!((ours.message, ours.span.start, ours.span.end), (rust.message, rust.span.start, rust.span.end), "{text}");
    }
}

/// What the comparison compares, spelled out once: each expression ends
/// with where it starts and ends, its provenance, then its key, a number
/// and a reading, as the process's mode makes it (`parser-ids.fx`, the Rust
/// front end's `ids::Kth` alike); in `path`, its place in a walk that takes
/// each before what is in it, of reading 0. The `if` that `and` makes and
/// its `#f`, at one span, are 2 and 5.
#[test]
fn a_tree_as_text() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let text = "(let* ((a #t)) (and a #f))";
    let (ours, base) = s.parse_with_own_parser_from(text).expect("parses");
    let ours: Vec<String> = ours.iter().map(|t| within_files(t)).collect();
    assert_eq!(ours, rust_trees(text, base));
    // Its keys, in `path`, as written (the others are digests).
    if fixpt_fx26::ids::mode() != fixpt_fx26::ids::Mode::Path {
        return;
    }
    assert_eq!(
        ours,
        ["(t-exp (e-let ([a (e-bool #t 10 12 1 0)]) (e-if (e-var a 20 21 3 0) (e-bool #f 22 24 4 0) (e-bool #f 15 25 5 0) 15 25 2 0) 7 13 0 0))"]
    );
}

/// A session's state is of its forms, each read in the state the one before
/// left (`ids::forms_state`, `readings.fx`'s `form-reading`): the same
/// however they were split into texts. The same text parsed twice is the
/// same trees, their keys too but in `path`, whose numbers go on.
#[test]
fn a_state_is_its_forms_however_they_are_split() {
    use fixpt_fx26::ids::forms_state;
    let set = Default::default();
    let one = forms_state(9, &set, "(define x int 1)\n(f x)", &[]).expect("reads");
    let first = forms_state(9, &set, "(define x int 1)", &[]).expect("reads");
    assert_eq!(one, forms_state(first, &set, " (f x) ; again", &[]).expect("reads"));
    assert_eq!(forms_state(9, &set, "", &[]), Some(9));
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let text = "(if #t 1 2)";
    let (once, base) = s.parse_with_own_parser_from(text).expect("parses");
    let (again, after) = s.parse_with_own_parser_from(text).expect("parses");
    assert_eq!(after, base + 4);
    if fixpt_fx26::ids::mode() != fixpt_fx26::ids::Mode::Path {
        assert_eq!(once, again);
    }
}

/// Texts that read as the same trees are one reading: no space, comment or
/// spelling tells them apart, nor where they are; trees that differ are
/// not, `(a . (b c))` and `(a b c)` among them, which the parser tells
/// apart (in code the first is no expression).
#[test]
fn a_reading_is_not_of_how_its_text_is_written() {
    let r = |t: &str| fixpt_fx26::ids::reading_of(7, t).expect("reads");
    assert_eq!(r("(f #t \"A\")"), r("  ( f ; a comment\n #true \"\\x41;\" )"));
    assert_ne!(r("(a . (b c))"), r("(a b c)"));
    assert_ne!(r("(f #t)"), r("(f #f)"));
    assert_ne!(r("(f) (g)"), r("(f (g))"));
    assert_ne!(r("ab"), r("|a b|"));
    assert_eq!(r("'(6/4 #x10)"), r("'(3/2 16)"));
    assert_ne!(r("#u8(1 2)"), r("#u8(1 3)"));
    assert_ne!(r("1/2"), r("1/3"));
}

/// The digest written in FX-26 is the one in Rust, each of the trees its
/// own reader reads: each front end makes a reading alone, and they must
/// agree (`readings.fx`, `ids::reading_of`).
#[test]
fn the_readings_agree() {
    let texts = ["", "(+ 1 2)", "λx → ü #\\ü", "'(a . b) #(1 \"s\") #:k", "(-1.5 1e300 123456789012345678901234567890 -7)", "'(6/4 -1/3 #u8(1 2 255))"];
    let cases: Vec<(i64, &str)> = texts.iter().zip([0, -1, 987_654_321_012, 5, 0, 3]).map(|(t, s)| (s, *t)).collect();
    let read = |t: &str| format!("(car ((with er read-text-at) {t:?} 0))");
    let calls: Vec<String> = cases.iter().map(|(s, t)| format!("((with r reading-of) {s} {})", read(t))).collect();
    let load = |f: &str| format!("((proj (load-module \"fx26:{f}.fx\") @s @e @m @c))");
    let program = format!("(define er {})\n(define r {})\n(list {})\n", load("eager-reader"), load("readings"), calls.join(" "));
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let ours = s.run_program(&program).expect("runs").expect("checks");
    let rust: Vec<String> = cases.iter().map(|(s, t)| fixpt_fx26::ids::reading_of(*s, t).expect("reads").to_string()).collect();
    assert_eq!(ours, format!("({})", rust.join(" ")));
    // A form's, the files it loads first folded in order of their keys.
    let (form, a, b) = ("(load-module \"b.fx\")", "(define y int 2)", "(+ 1 2)");
    let file = |k: &str, t: &str| format!("(product (1 {k:?}) (2 {}))", read(t));
    let call = format!("((with r form-reading) 4 \"native\" (car {}) (list {} {}))", read(form), file("b", b), file("a", a));
    let ours = s.run_program(&format!("(define er {})\n(define r {})\n{call}\n", load("eager-reader"), load("readings"))).expect("runs").expect("checks");
    let native = fixpt_fx26::ids::Settings { native: true, ..Default::default() };
    let loads = vec![("b".to_string(), b.to_string()), ("a".to_string(), a.to_string())];
    assert_eq!(ours, fixpt_fx26::ids::forms_state(4, &native, form, &[loads]).expect("reads").to_string());
    // The standard environment's state, and a staged step's reps.
    let standard = fixpt_fx26::standard::standard_text();
    let call = format!("((with r standard-state) {})", read(&standard));
    let ours = s.run_program(&format!("(define er {})\n(define r {})\n{call}\n", load("eager-reader"), load("readings"))).expect("runs").expect("checks");
    assert_eq!(ours, fixpt_fx26::ids::standard_state().to_string());
    let bytes = |n: i64, b: u8| format!("(the (bytevectorof @t) (make-bytevector {n} (int->u8 {b})))");
    let call = format!("((with r with-reps) 5 {} (list (product (1 'a) (2 {}))))", bytes(3, 7), bytes(1, 9));
    let ours = s.run_program(&format!("(define r {})\n{call}\n", load("readings"))).expect("runs").expect("checks");
    assert_eq!(ours, fixpt_fx26::ids::with_reps(5, &[7, 7, 7], &[("a".into(), vec![9])]).to_string());
    let text = |s: &str| format!("((with r text-reading-of) -1 {s:?})");
    let ours = s.run_program(&format!("(define r {})\n{}\n", load("readings"), text("syscall x"))).expect("runs").expect("checks");
    assert_eq!(ours, fixpt_fx26::ids::text_reading_of(-1, "syscall x").to_string());
}

/// A form's reading is of the switches the checker is set to, and of the
/// files it loads first, as well as of its trees and the session's state
/// (`ids::forms_state`): what changes what a check finds changes it.
#[test]
fn a_reading_is_of_the_switches_and_the_files_loaded() {
    use fixpt_fx26::ids::{forms_state, Settings};
    let cellular = Settings::default();
    let native = Settings { native: true, ..cellular };
    let r = |s: &Settings, loads: &[(String, String)]| forms_state(3, s, "(f)", &[loads.to_vec()]).expect("reads");
    assert_ne!(r(&cellular, &[]), r(&native, &[]));
    let load = |text: &str| [("a.fx".to_string(), text.to_string())];
    assert_ne!(r(&cellular, &load("(define x int 1)")), r(&cellular, &load("(define x int 2)")));
    assert_eq!(r(&cellular, &load("(define x int 1)")), r(&cellular, &load(" (define x int 1) ; one")));
    let two = |a: &str, b: &str| [(a.to_string(), "1".to_string()), (b.to_string(), "2".to_string())];
    assert_eq!(r(&cellular, &two("a", "b")), forms_state(3, &cellular, "(f)", &[vec![two("a", "b")[1].clone(), two("a", "b")[0].clone()]]).expect("reads"));
}

/// The two checkers write their switches alike (`checked-settings`,
/// `Settings::text`), as each reading folds them.
#[test]
fn the_switches_are_written_alike() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for (native, effects, defer) in [(false, false, false), (true, true, false), (false, true, true)] {
        s.set_native_convention(native);
        s.set_globals_effects(effects);
        s.set_defer_reruns(defer);
        let ours = s.own_settings_text().expect("writes them");
        assert_eq!(ours, s.own_reading_state().settings.text());
    }
}

/// A session's state is what its checker kept: a text refused leaves it as
/// it was, so that a session that never saw it is in the same state.
#[test]
fn a_refused_text_leaves_the_state_as_it_was() {
    use fixpt_fx26::session::Strategy;
    let session = || Fx26Session::with_backend_preloaded_in(Backend::Bytecode, None, false, Strategy::Cellular).expect("starts");
    let enter = |s: &mut Fx26Session, text: &str| {
        let forms = s.read_entry("t", text).expect("reads");
        forms.iter().map(|f| s.run(f).is_ok()).all(|ok| ok)
    };
    let (mut a, mut b) = (session(), session());
    assert!(enter(&mut a, "(define x int 1)\n") && enter(&mut b, "(define x int 1)\n"));
    let before = a.own_reading_state().at;
    assert!(!enter(&mut a, "(define y bool 5)\n"));
    assert_eq!(a.own_reading_state().at, before);
    assert!(enter(&mut a, "(define z int 3)\n") && enter(&mut b, "(define z int 3)\n"));
    assert_eq!(a.own_reading_state().at, b.own_reading_state().at);
    assert_ne!(a.own_reading_state().at, before);
    // The state the checker written in FX-26 left is the one Rust makes,
    // from the standard environment's, where the first entry began.
    let settings = a.own_reading_state().settings;
    let after = |s: i64, t: &str| fixpt_fx26::ids::forms_state(s, &settings, t, &[]).expect("reads");
    let begun = fixpt_fx26::ids::standard_state();
    assert_eq!(a.own_reading_state().at, after(after(begun, "(define x int 1)\n"), "(define z int 3)\n"));
}

/// The module files built in load no cycle (`TODO.md` §71): found from
/// their text, before any checker runs, since a cycle made by a tool once
/// showed only as a parser recursing without end. Each file's
/// `(load-module "fx26:…")` and `(load-input "fx26:…")` are its edges.
#[test]
fn the_built_in_files_load_no_cycle() {
    let files: std::collections::HashMap<&str, &str> =
        fixpt_fx26::FRONT_END_MODULES.iter().chain(fixpt_fx26::FRONT_END_FILES.iter()).copied().collect();
    let loads = |text: &str| -> Vec<String> {
        let mut out = Vec::new();
        for head in ["(load-module \"fx26:", "(load-input \"fx26:"] {
            let mut rest = text;
            while let Some(i) = rest.find(head) {
                rest = &rest[i + head.len()..];
                if let Some(j) = rest.find('"') {
                    out.push(rest[..j].to_string());
                }
            }
        }
        out
    };
    // Depth first, each file's state: 1 being visited, 2 done.
    fn visit(n: &str, files: &std::collections::HashMap<&str, &str>, loads: &dyn Fn(&str) -> Vec<String>, state: &mut std::collections::HashMap<String, u8>, path: &mut Vec<String>) -> Option<Vec<String>> {
        match state.get(n) {
            Some(1) => {
                let i = path.iter().position(|p| p == n).unwrap_or(0);
                let mut chain = path[i..].to_vec();
                chain.push(n.to_string());
                return Some(chain);
            }
            Some(_) => return None,
            None => {}
        }
        state.insert(n.to_string(), 1);
        path.push(n.to_string());
        for m in loads(files.get(n).copied().unwrap_or("")) {
            if let Some(c) = visit(&m, files, loads, state, path) {
                return Some(c);
            }
        }
        path.pop();
        state.insert(n.to_string(), 2);
        None
    }
    let mut state = std::collections::HashMap::new();
    let mut names: Vec<&str> = files.keys().copied().collect();
    names.sort();
    for n in names {
        let cycle = visit(n, &files, &loads, &mut state, &mut Vec::new());
        assert!(cycle.is_none(), "the built-in files load in a cycle: {}", cycle.unwrap().join(" loads "));
    }
}
