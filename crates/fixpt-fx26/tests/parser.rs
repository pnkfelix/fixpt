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
fn rust_trees(text: &str) -> Vec<String> {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), text).expect("reads");
    c.declare_ahead(&forms).expect("declares");
    let mut c2 = Checker::new();
    let forms2 = c2.read_in(FileId(0), text).expect("reads");
    let chars = Chars::of(text);
    let mut tops = Vec::new();
    for f in &forms2 {
        let top = c2.top(f).unwrap_or_else(|e| panic!("checks: {e}"));
        // The hidden globals of the files it loads first, defined before it.
        for (t, h) in std::mem::take(&mut c2.hoisted) {
            tops.push((t, h.span));
        }
        tops.push((top, f.span));
    }
    // Which of the expressions at its span each is, the forms in order.
    let mut kth = Kth::new();
    for (t, _) in &tops {
        kth.top(&c2, t);
    }
    tops.iter().map(|(t, span)| show_top(&c2, &chars, t, *span, &kth)).collect()
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
/// parser's spans keep the file apart, and show the place in it alone; and
/// each expression's reading, its last field, as 0, as the Rust front end,
/// which numbers within the reading, says it (`parser-ids.fx`).
fn within_files(tree: &str) -> String {
    let tree = &readings_as_zero(tree);
    let mut out = String::new();
    let mut digits = String::new();
    let flush = |digits: &mut String, out: &mut String| {
        match digits.parse::<u64>() {
            Ok(n) if n >= 1_000_000_000 => out.push_str(&(n % 1_000_000_000).to_string()),
            _ => out.push_str(digits),
        }
        digits.clear();
    };
    for c in tree.chars() {
        if c.is_ascii_digit() {
            digits.push(c);
        } else {
            flush(&mut digits, &mut out);
            out.push(c);
        }
    }
    flush(&mut digits, &mut out);
    out
}

/// `tree` with the last of each run of four numbers before a `)`, an
/// expression's reading, 0 (its place's start and end, and its number, are
/// the three before).
fn readings_as_zero(tree: &str) -> String {
    let b = tree.as_bytes();
    let mut out = String::new();
    // `tree[..copied]` is in `out`; `run`, the numbers in a row before here.
    let (mut copied, mut run) = (0, Vec::<(usize, usize)>::new());
    let mut i = 0;
    while i < b.len() {
        if b[i].is_ascii_digit() && i > 0 && b[i - 1] == b' ' {
            let start = i;
            while i < b.len() && b[i].is_ascii_digit() {
                i += 1;
            }
            run.push((start, i));
            continue;
        }
        if b[i] == b')' && run.len() >= 4 && run.last().map(|r| r.1) == Some(i) {
            let (start, _) = run[run.len() - 1];
            out.push_str(&tree[copied..start]);
            out.push('0');
            copied = i;
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
    let ours = s.parse_with_own_parser(text).unwrap_or_else(|e| panic!("the FX-26 parser: {e}"));
    let ours: Vec<String> = ours.iter().map(|t| within_files(&without_file_marks(t))).collect();
    let rust: Vec<String> = rust_trees(text).iter().map(|t| within_files(t)).collect();
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
/// with where it starts and ends, its provenance, then its identity: its
/// number in a walk that takes each before what is in it, and its reading
/// (`parser-ids.fx`; 0 here, as the Rust front end says it). The `if` that
/// `and` makes and its `#f`, at one span, are 2 and 5.
#[test]
fn a_tree_as_text() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let text = "(let* ((a #t)) (and a #f))";
    let ours: Vec<String> = s.parse_with_own_parser(text).expect("parses").iter().map(|t| within_files(t)).collect();
    assert_eq!(
        ours,
        ["(t-exp (e-let ([a (e-bool #t 10 12 1 0)]) (e-if (e-var a 20 21 3 0) (e-bool #f 22 24 4 0) (e-bool #f 15 25 5 0) 15 25 2 0) 7 13 0 0))"]
    );
    assert_eq!(ours, rust_trees(text));
}

/// A reading is a digest of the session's state and the trees read, not a
/// count (`readings.fx`): the same text parsed twice is the same trees,
/// readings and all, each the reading `ids::reading_of` makes of it.
#[test]
fn a_reading_is_its_trees_not_a_count() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let text = "(if #t 1 2)";
    let once = s.parse_with_own_parser(text).expect("parses");
    assert_eq!(once, s.parse_with_own_parser(text).expect("parses"));
    let r = fixpt_fx26::ids::reading_of(0, text).expect("reads");
    assert!(once[0].ends_with(&format!(" {r}))")), "{once:?}");
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
}

/// The digest written in FX-26 is the one in Rust, each of the trees its
/// own reader reads: each front end makes a reading alone, and they must
/// agree (`readings.fx`, `ids::reading_of`).
#[test]
fn the_readings_agree() {
    let texts = ["", "(+ 1 2)", "λx → ü #\\ü", "'(a . b) #(1 \"s\") #:k", "(-1.5 1e300 123456789012345678901234567890 -7)"];
    let cases: Vec<(i64, &str)> = texts.iter().zip([0, -1, 987_654_321_012, 5, 0]).map(|(t, s)| (s, *t)).collect();
    let read = |t: &str| format!("(car ((with er read-text-at) {t:?} 0))");
    let calls: Vec<String> = cases.iter().map(|(s, t)| format!("((with r reading-of) {s} {})", read(t))).collect();
    let load = |f: &str| format!("((proj (load-module \"fx26:{f}.fx\") @s @e @m @c))");
    let program = format!("(define er {})\n(define r {})\n(list {})\n", load("eager-reader"), load("readings"), calls.join(" "));
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let ours = s.run_program(&program).expect("runs").expect("checks");
    let rust: Vec<String> = cases.iter().map(|(s, t)| fixpt_fx26::ids::reading_of(*s, t).expect("reads").to_string()).collect();
    assert_eq!(ours, format!("({})", rust.join(" ")));
    let text = |s: &str| format!("((with r text-reading-of) -1 {s:?})");
    let ours = s.run_program(&format!("(define r {})\n{}\n", load("readings"), text("syscall x"))).expect("runs").expect("checks");
    assert_eq!(ours, fixpt_fx26::ids::text_reading_of(-1, "syscall x").to_string());
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
