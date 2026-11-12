//! The eager reader written in FX-26 as the REPL runs it: compiled with the
//! front end, driven by `fixpt_fx26::eager`, with no Scheme engine made
//! (`tests/eager.rs` holds it, lowered, to the Scheme reader it was ported
//! from).

use fixpt_engine::Backend;
use fixpt_fx26::eager::{Eager, Status};
use fixpt_fx26::session::Fx26Session;

fn started() -> (Fx26Session, Eager) {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let r = Eager::start(&mut s).expect("the reader starts");
    (s, r)
}

/// Where FX-26's lexical syntax differs from Scheme's, it says so where the
/// Rust reader does; every prefix of an FX-26 program is unfinished or
/// complete exactly when the Rust reader says so; and nothing of it runs on
/// a Scheme engine.
#[test]
fn the_compiled_reader_reads_as_the_rust_one() {
    let (mut s, mut r) = started();
    for text in ["[a]", "(a ]", "a]", "(a [b"] {
        let rust = fixpt_read::form_status(text, fixpt_read::SyntaxProfile::FX26);
        let fixpt_read::FormStatus::Invalid(e) = rust else { panic!("{text:?}: Rust says {rust:?}") };
        match r.status(&mut s.scheme, text, false).expect("reads") {
            Status::Invalid { at, message } => {
                assert_eq!(at, e.span.start as usize, "{text:?}");
                assert_eq!(message, e.message, "{text:?}");
            }
            other => panic!("{text:?}: {other:?}"),
        }
    }
    let text = "(define x (the unit #u)) (g #u8(1) #| ) |#)";
    let chars: Vec<char> = text.chars().collect();
    for n in 0..=chars.len() {
        let prefix: String = chars[..n].iter().collect();
        let eager = r.status(&mut s.scheme, &prefix, true).expect("reads");
        let rust = fixpt_read::form_status(&format!("{prefix}\n"), fixpt_read::SyntaxProfile::FX26);
        assert_eq!(matches!(eager, Status::Incomplete), matches!(rust, fixpt_read::FormStatus::Incomplete), "{prefix:?}: FX-26 {eager:?}, Rust {rust:?}");
    }
    assert_eq!(r.status(&mut s.scheme, "(vector-ref (make-vector 3 0) ,help", true).expect("reads"), Status::Hole { closers: ")".into() });
    assert!(s.scheme.scheme_made().is_none(), "no Scheme engine made");
}

/// The driver under collections swept through it: every nth safepoint
/// collects, for several n, so that one lands between any two calls the
/// driver makes, and a value it held across a call would be stale.
#[test]
fn the_compiled_driver_survives_collections_anywhere() {
    let text = "(define x (the unit #u)) (g #u8(1) #| ) |#) (h #";
    for every in [1, 2, 3, 5, 7] {
        let (mut s, mut r) = started();
        s.scheme.set_gc_every(every);
        let chars: Vec<char> = text.chars().collect();
        for n in 0..=chars.len() {
            let prefix: String = chars[..n].iter().collect();
            r.status(&mut s.scheme, &prefix, true).unwrap_or_else(|e| panic!("every {every}, {prefix:?}: {e}"));
        }
        assert_eq!(r.status(&mut s.scheme, text, false).expect("reads"), Status::Incomplete, "every {every}");
    }
}
