//! The eager reader (`eager-reader.scm`) against the Rust reader.
//!
//! The Rust reader is the reference: it is what the conformance corpora go
//! through. So the Scheme reader must read every input to the same data, must
//! reject the same inputs at the same place, and must call the same inputs
//! unfinished — on both engines, since it runs on them.

use fixpt_engine::Backend;
use fixpt_scheme::eager::{EagerReader, EagerStatus, SOURCE};
use fixpt_scheme::Session;

/// A session with the reader loaded and a helper that reads a whole string.
fn session(backend: Backend) -> Session {
    let mut s = Session::with_backend(backend);
    s.eval_str("<eager>", SOURCE).expect("the reader loads");
    s.eval_str(
        "<helper>",
        include_str!("programs/eager/read-all.scm"),
    )
    .expect("the helper loads");
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

/// Both readers read `text` to `equal?` data.
fn agree(s: &mut Session, text: &str) {
    let program = format!("(equal? (eager-data {}) (quote ({text}\n)))", scheme_string(text));
    let got = s.eval_to_string("<agree>", &program);
    assert_eq!(got.as_deref().ok(), Some("#t"), "the readers disagree on:\n{text}\n{got:?}");
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
fn the_readers_agree_on_data() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        for text in DATA {
            agree(&mut s, text);
        }
    }
}

/// The largest inputs to hand: the prelude, and the reader's own source.
#[test]
fn the_readers_agree_on_whole_files() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        agree(&mut s, fixpt_scheme::PRELUDE);
        agree(&mut s, SOURCE);
    }
}

/// Every prefix of an input is either unfinished or complete, never an
/// error, and the two readers agree which — the property the REPL relies on
/// to decide what `Enter` does.
#[test]
fn the_readers_agree_on_every_prefix() {
    let text = "(define (f x) \"s;(\" #\\) #| ) |# |a(b| '#(1 2) `(a ,b) (g . h))";
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        let mut r = EagerReader::new(&mut s).expect("starts");
        let chars: Vec<char> = text.chars().collect();
        for n in 0..=chars.len() {
            let prefix: String = chars[..n].iter().collect();
            let eager = r.status(&mut s, &prefix, false).expect("reads");
            // `Enter` is a newline to the eager reader, which cannot know no
            // more characters are coming — so the fair comparison gives the
            // batch reader the same newline. (Without it they differ on a
            // trailing `#`, which a newline makes an error and end of input
            // leaves unfinished.)
            let rust = fixpt_read::form_status(&format!("{prefix}\n"), fixpt_read::SyntaxProfile::SCHEME);
            let rust_incomplete = matches!(rust, fixpt_read::FormStatus::Incomplete);
            let eager_at_enter = r.status(&mut s, &prefix, true).expect("reads");
            assert!(
                !matches!(eager, EagerStatus::Invalid { .. }),
                "{backend:?}: the prefix {prefix:?} is not an error, but the eager reader said {eager:?}"
            );
            assert_eq!(
                matches!(eager_at_enter, EagerStatus::Incomplete),
                rust_incomplete,
                "{backend:?}: {prefix:?}: eager {eager_at_enter:?}, rust {rust:?}"
            );
        }
    }
}

#[test]
fn errors_are_caught_at_the_character_that_makes_them() {
    let cases = [")", "(a b]", "(1 2 . )", "(. a)", "#q ", "#\\bogus ", "(\"a\" #tru )", "#(1 . 2)"];
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        let mut r = EagerReader::new(&mut s).expect("starts");
        for text in cases {
            let eager = r.status(&mut s, text, false).expect("reads");
            let rust = fixpt_read::form_status(text, fixpt_read::SyntaxProfile::SCHEME);
            // The inputs are ASCII, so a byte offset is a character index.
            let at = match rust {
                fixpt_read::FormStatus::Invalid(e) => e.span.start as usize,
                other => panic!("{text:?}: the Rust reader says {other:?}"),
            };
            match eager {
                EagerStatus::Invalid { at: got, .. } => assert_eq!(got, at, "{backend:?}: {text:?}"),
                other => panic!("{backend:?}: {text:?} should be an error, got {other:?}"),
            }
        }
    }
}

/// Both reject a bytevector element out of range. The Rust reader points at
/// the element; the eager reader's list elements carry no positions, so it
/// points at the `#u8` — the one place the two report different positions.
#[test]
fn both_reject_a_bad_bytevector_element() {
    let mut s = session(Backend::Bytecode);
    let mut r = EagerReader::new(&mut s).expect("starts");
    assert!(matches!(r.status(&mut s, "#u8(1 300)", false).expect("reads"), EagerStatus::Invalid { at: 0, .. }));
    assert!(matches!(
        fixpt_read::form_status("#u8(1 300)", fixpt_read::SyntaxProfile::SCHEME),
        fixpt_read::FormStatus::Invalid(_)
    ));
}

/// Backing up and changing course is going back to an earlier checkpoint:
/// the states are values, and resuming one twice gives two independent parses.
#[test]
fn checkpoints_back_up_and_branch() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        let mut r = EagerReader::new(&mut s).expect("starts");
        let mut st = |text: &str| r.status(&mut s, text, false).expect("reads");
        assert_eq!(st("(a b"), EagerStatus::Incomplete);
        assert!(matches!(st("(a b]"), EagerStatus::Invalid { at: 4, .. }));
        // Backspace over the mistake, and finish properly.
        assert_eq!(st("(a b"), EagerStatus::Incomplete);
        assert_eq!(st("(a b)"), EagerStatus::Complete);
        // An edit in the middle re-reads from there, not from the start.
        assert!(matches!(st("(a )b)"), EagerStatus::Invalid { .. }));
        assert_eq!(st("(a (b)"), EagerStatus::Incomplete);
        assert_eq!(st("(a (b))"), EagerStatus::Complete);
    }
}

/// `,help` written before a form is finished: the reader knows it is the
/// newest element of an open list, and what would close everything.
#[test]
fn a_hole_before_the_form_is_finished() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        let mut r = EagerReader::new(&mut s).expect("starts");
        let mut at_enter = |text: &str| r.status(&mut s, text, true).expect("reads");
        assert_eq!(at_enter("(vector-ref (make-vector 3 0) ,help"), EagerStatus::Hole { closers: ")".into() });
        assert_eq!(at_enter("(f (g [h ,help"), EagerStatus::Hole { closers: "]))".into() });
        assert_eq!(at_enter("#(1 ,help"), EagerStatus::Hole { closers: ")".into() });
        // Not the newest element, or not in a list: an ordinary unfinished form.
        assert_eq!(at_enter("(f ,help x"), EagerStatus::Incomplete);
        assert_eq!(at_enter("(f \",help"), EagerStatus::Incomplete);
        // A finished form with a hole is not this case: it is complete.
        assert_eq!(at_enter("(f ,help)"), EagerStatus::Complete);
    }
}

/// The parser's stack, read out of the suspended continuation's marks.
#[test]
fn the_context_is_the_parse_stack() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        let out = s
            .eval_to_string(
                "<ctx>",
                include_str!("programs/eager/parse-stack.scm"),
            )
            .expect("runs");
        assert_eq!(out, "((list (vector-ref (make-vector 3 0))) (top))", "{backend:?}");
    }
}
