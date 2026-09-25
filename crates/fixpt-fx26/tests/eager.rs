//! The eager reader in FX-26 (`src/eager-reader.fx`), against the other two.
//!
//! Three readers now read the same inputs: the Rust reader in `fixpt-read`,
//! which is the reference; the Scheme eager reader it was checked against
//! (`fixpt-scheme/tests/eager.rs`); and this one, a port of the Scheme one to
//! FX-26, checked, lowered to annotated Scheme and run. The FX-26 reader
//! keeps the Scheme one's procedure names and meanings, so the same driver,
//! `EagerReader`, runs it: only the names' prefix differs.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_scheme::eager::{EagerReader, EagerStatus};

/// A session with the FX-26 reader loaded, and the Scheme one beside it.
fn session(backend: Backend) -> Fx26Session {
    let mut s = Fx26Session::with_backend(backend).expect("starts");
    let loaded = s.run_program(fixpt_fx26::EAGER_READER).expect("the reader checks");
    loaded.expect("the reader loads");
    s.scheme.eval_str("<scheme-eager>", fixpt_scheme::eager::SOURCE).expect("the Scheme reader loads");
    s.scheme.eval_str("<helper>", include_str!("programs/eager/read-all.scm")).expect("the helper loads");
    s
}

fn scheme_string(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// The FX-26 reader reads `text` to the data the Rust reader reads.
fn agree(s: &mut Fx26Session, text: &str) {
    let program = format!("(equal? (fx-data {}) (quote ({text}\n)))", scheme_string(text));
    let got = s.scheme.eval_to_string("<agree>", &program);
    assert_eq!(got.as_deref().ok(), Some("#t"), "the FX-26 reader disagrees on:\n{text}\n{got:?}");
}

const DATA: &[&str] = &[
    "(a b . c) (1 . (2 3)) () [x y] (a [b] c)",
    "\"str\\n\\t\\\\\" \"q\\\"uote\" \"\\x41;\\x3bb;\" \"line\\\n   continued\"",
    "#\\a #\\space #\\newline #\\x41 #\\( #\\) #\\; #\\λ",
    "#(1 2 (3)) #() #u8(0 1 255) #u8()",
    "'x `(a ,b ,@c) ',@d '(quote x)",
    "#t #f #true #false #T",
    "0 -1 +5 1/2 -3/4 1.5 -0.25 1e3 #x1F #b101 #o17 #e1.5 #i1/2 12345678901234567890",
    "+ - ... a.b .5 -. |a b| |weird\\|bar| a\\ b <=? ->x",
    "(a ; comment\n b) #| block #| nested |# |# c #;(ignored datum) d",
    "(define (f x) (let loop ((i 0)) (if (< i x) (loop (+ i 1)) i)))",
    "(a . b) (a b c . d)",
];

#[test]
fn it_agrees_with_the_rust_reader_on_data() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        for text in DATA {
            agree(&mut s, text);
        }
    }
}

/// The largest inputs to hand: the Scheme reader's source, and this reader's.
///
/// Under `gc-stress`, which collects at every safepoint, only their first few
/// top-level forms: feeding a whole file one character at a time performs a
/// collection for every step of every character. The shape of the check is
/// the same.
#[test]
fn it_agrees_on_whole_files() {
    let mut s = session(Backend::Bytecode);
    let forms = if cfg!(feature = "gc-stress") { 4 } else { usize::MAX };
    agree(&mut s, leading_forms(fixpt_scheme::eager::SOURCE, forms));
    agree(&mut s, leading_forms(fixpt_fx26::EAGER_READER, forms));
}

/// `text` up to the end of its `n`th top-level form, as the Rust reader
/// reads it.
fn leading_forms(text: &str, n: usize) -> &str {
    let mut interner = fixpt_read::Interner::new();
    let forms = fixpt_read::Reader::new(text, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::SCHEME, &mut interner)
        .read_all()
        .expect("reads");
    match forms.get(n.saturating_sub(1)) {
        Some(f) if n < forms.len() => &text[..f.span.end as usize],
        _ => text,
    }
}

/// Every prefix is unfinished or complete, never an error, and the FX-26
/// reader says which exactly as the Scheme one does, and as the Rust one
/// does at `Enter`.
#[test]
fn it_agrees_on_every_prefix() {
    let text = "(define (f x) \"s;(\" #\\) #| ) |# |a(b| '#(1 2) `(a ,b) (g . h))";
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        let mut fx = EagerReader::attach(&mut s.scheme, "fx:").expect("starts");
        let mut scheme = EagerReader::attach(&mut s.scheme, "").expect("starts");
        let chars: Vec<char> = text.chars().collect();
        for n in 0..=chars.len() {
            let prefix: String = chars[..n].iter().collect();
            let mine = fx.status(&mut s.scheme, &prefix, false).expect("reads");
            let theirs = scheme.status(&mut s.scheme, &prefix, false).expect("reads");
            assert_eq!(mine, theirs, "{backend:?}: {prefix:?}");
            assert!(!matches!(mine, EagerStatus::Invalid { .. }), "{backend:?}: {prefix:?}: {mine:?}");
            let at_enter = fx.status(&mut s.scheme, &prefix, true).expect("reads");
            let rust = fixpt_read::form_status(&format!("{prefix}\n"), fixpt_read::SyntaxProfile::SCHEME);
            assert_eq!(
                matches!(at_enter, EagerStatus::Incomplete),
                matches!(rust, fixpt_read::FormStatus::Incomplete),
                "{backend:?}: {prefix:?}: FX-26 {at_enter:?}, Rust {rust:?}"
            );
        }
    }
}

#[test]
fn errors_are_caught_where_the_rust_reader_catches_them() {
    let cases = [")", "(a b]", "(1 2 . )", "(. a)", "#q ", "#\\bogus ", "(\"a\" #tru )", "#(1 . 2)"];
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        let mut fx = EagerReader::attach(&mut s.scheme, "fx:").expect("starts");
        let mut scheme = EagerReader::attach(&mut s.scheme, "").expect("starts");
        for text in cases {
            let mine = fx.status(&mut s.scheme, text, false).expect("reads");
            let rust = fixpt_read::form_status(text, fixpt_read::SyntaxProfile::SCHEME);
            let at = match rust {
                fixpt_read::FormStatus::Invalid(e) => e.span.start as usize,
                other => panic!("{text:?}: the Rust reader says {other:?}"),
            };
            match &mine {
                EagerStatus::Invalid { at: got, .. } => assert_eq!(*got, at, "{backend:?}: {text:?}"),
                other => panic!("{backend:?}: {text:?} should be an error, got {other:?}"),
            }
            // Word for word what the Scheme reader says.
            assert_eq!(mine, scheme.status(&mut s.scheme, text, false).expect("reads"), "{backend:?}: {text:?}");
        }
    }
}

/// States are values: backing up and branching is going back to a
/// checkpoint, which is a continuation typed `(composable char state …)`.
#[test]
fn checkpoints_back_up_and_branch() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        let mut r = EagerReader::attach(&mut s.scheme, "fx:").expect("starts");
        let mut st = |text: &str| r.status(&mut s.scheme, text, false).expect("reads");
        assert_eq!(st("(a b"), EagerStatus::Incomplete);
        assert!(matches!(st("(a b]"), EagerStatus::Invalid { at: 4, .. }));
        assert_eq!(st("(a b"), EagerStatus::Incomplete);
        assert_eq!(st("(a b)"), EagerStatus::Complete);
        assert!(matches!(st("(a )b)"), EagerStatus::Invalid { .. }));
        assert_eq!(st("(a (b)"), EagerStatus::Incomplete);
        assert_eq!(st("(a (b))"), EagerStatus::Complete);
    }
}

/// The hole closers come from the parse stack, which is the marks of the
/// suspended continuation, read with `marks-of`.
#[test]
fn a_hole_before_the_form_is_finished() {
    let mut s = session(Backend::Bytecode);
    let mut r = EagerReader::attach(&mut s.scheme, "fx:").expect("starts");
    let mut at_enter = |text: &str| r.status(&mut s.scheme, text, true).expect("reads");
    assert_eq!(at_enter("(vector-ref (make-vector 3 0) ,help"), EagerStatus::Hole { closers: ")".into() });
    assert_eq!(at_enter("(f (g [h ,help"), EagerStatus::Hole { closers: "]))".into() });
    assert_eq!(at_enter("#(1 ,help"), EagerStatus::Hole { closers: ")".into() });
    assert_eq!(at_enter("(f ,help x"), EagerStatus::Incomplete);
    assert_eq!(at_enter("(f \",help"), EagerStatus::Incomplete);
    assert_eq!(at_enter("(f ,help)"), EagerStatus::Complete);
}

/// The parse stack itself: the same marks as the Scheme reader's.
#[test]
fn the_context_is_the_parse_stack() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        let fx = s.scheme.eval_to_string("<ctx>", "(fx-context \"(vector-ref (make-vector 3 0) \")");
        let scheme = s.scheme.eval_to_string("<ctx>", "(scheme-context \"(vector-ref (make-vector 3 0) \")");
        assert_eq!(fx.as_deref().ok(), Some("((list 0 #\\) ((make-vector 3 0) vector-ref)) (top))"), "{backend:?}");
        assert_eq!(fx.ok(), scheme.ok(), "{backend:?}");
    }
}
