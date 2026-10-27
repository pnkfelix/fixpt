//! What more than one test of compiled code needs.
#![allow(dead_code)]

use fixpt_heap::{Heap, Value};
use std::collections::HashMap;

/// Whether words `a` and `b` are the same code: cell for cell, the words
/// they call compared the same way, and each global's cell in one standing
/// for one in the other, consistently. `pairs` is what is assumed so far.
pub fn same_code(h: &Heap, a: Value, b: Value, pairs: &mut HashMap<u64, u64>, why: &mut String) -> bool {
    if let Some(&x) = pairs.get(&a.raw()) {
        return x == b.raw() || { *why = format!("{} is matched twice", fixpt_runtime::write_value(h, a)); false };
    }
    // Code, and globals' cells, are compared by structure; anything else,
    // a literal, by how it is written.
    let code = |v: Value| {
        v.is_bloblet()
            && ["cellular-code", "cellular-closure", "bloblet", "register-code"].iter().any(|k| h.bloblet_kind(v) == fixpt_heap::layout::kind(k))
    };
    let (ka, kb) = (code(a).then(|| h.bloblet_kind(a)), code(b).then(|| h.bloblet_kind(b)));
    if ka.is_none() || kb.is_none() {
        let (wa, wb) = (fixpt_runtime::write_value(h, a), fixpt_runtime::write_value(h, b));
        if wa != wb {
            *why = format!("{wa} and {wb}");
        }
        return wa == wb;
    }
    if ka != kb {
        *why = format!("kinds {ka:?} and {kb:?}");
        return false;
    }
    pairs.insert(a.raw(), b.raw());
    // A global's cell stands for the global; what is in it depends on
    // whether the program has run.
    if ka == Some(fixpt_heap::layout::kind("bloblet")) {
        return true;
    }
    let (na, nb) = (h.bloblet_head(a).fields, h.bloblet_head(b).fields);
    if na != nb {
        *why = format!("{} fields and {}", na, nb);
        return false;
    }
    // A register word's places: where each expression's code starts.
    if ka == Some(fixpt_heap::layout::kind("register-code")) && h.register_places(a) != h.register_places(b) {
        *why = format!("{}'s places {:?} and {:?}", fixpt_runtime::write_value(h, h.bloblet_slot(a, fixpt_heap::layout::cellular::WORD_NAME)), h.register_places(a), h.register_places(b));
        return false;
    }
    // Field 1 is the trailer; the rest are values. A word's entry is
    // `docol`, or a native machine's number for its compiled code: the same
    // cells either way; a register word's, 0 or a machine's number. A word's
    // twin, its register code, is compared as code, as the word is.
    let entry = |w: Value, i: usize| {
        let v = h.bloblet_slot(w, i);
        let word = ka == Some(fixpt_heap::layout::kind("cellular-code"));
        let register = ka == Some(fixpt_heap::layout::kind("register-code"));
        let native = i == fixpt_heap::layout::cellular::WORD_ENTRY
            && (word && v.as_fixnum() >= fixpt_heap::layout::cellular::PRIMITIVES as i64 || register);
        if native { Value::fixnum(0) } else { v }
    };
    (2..=na).all(|i| same_code(h, entry(a, i), entry(b, i), pairs, why))
}

/// How many register words (twins) the code reachable from word `w` has: to
/// see that a comparison of register code compared some.
pub fn register_words(h: &Heap, w: Value, seen: &mut std::collections::HashSet<u64>) -> usize {
    if !w.is_bloblet() || !seen.insert(w.raw()) {
        return 0;
    }
    let k = h.bloblet_kind(w);
    let own = (k == fixpt_heap::layout::kind("register-code")) as usize;
    if k != fixpt_heap::layout::kind("cellular-code") && k != fixpt_heap::layout::kind("register-code") {
        return 0;
    }
    own + (2..=h.bloblet_head(w).fields).map(|i| register_words(h, h.bloblet_slot(w, i), seen)).sum::<usize>()
}

/// How far a long sweep has got, said on the terminal as it goes: at most
/// every 30 s, so a sweep that is quick says nothing. Written to `stderr`
/// itself, not by `eprintln!`, which the test harness holds until the test
/// ends.
pub struct Progress {
    what: String,
    total: usize,
    start: std::time::Instant,
    last: std::time::Instant,
}

impl Progress {
    pub fn new(what: impl Into<String>, total: usize) -> Progress {
        let now = std::time::Instant::now();
        Progress { what: what.into(), total, start: now, last: now }
    }

    /// `done` of the total are done.
    pub fn at(&mut self, done: usize) {
        if self.last.elapsed() >= std::time::Duration::from_secs(30) {
            self.last = std::time::Instant::now();
            use std::io::Write;
            let line = format!("    {}: {done} of {} ({:.0?})\n", self.what, self.total, self.start.elapsed());
            let _ = std::io::stderr().write_all(line.as_bytes());
        }
    }
}

thread_local! {
    /// This thread's session for the pieces written in FX-26: loading them
    /// is most of a check's or a compile's cost (1.3 s, against a few ms for
    /// a small program), and each program they are given begins afresh
    /// (`check-program` resets the checker; the compiler's globals only
    /// shadow), so one session serves every program a test gives them.
    static OWN: std::cell::RefCell<Option<fixpt_fx26::session::Fx26Session>> = const { std::cell::RefCell::new(None) };
    /// A second, for the evaluator written in FX-26 alone (Heist's,
    /// `FIXPT-CHANGES.md` F1): the scheduler's prompt tag is the runtime's,
    /// made once (`%sched` 12, 13), and a tag compiled code made is not one
    /// the evaluator can use, nor the other way round, so a program with
    /// processes evaluated after one compiled in the same session fails.
    static OWN_EVAL: std::cell::RefCell<Option<fixpt_fx26::session::Fx26Session>> = const { std::cell::RefCell::new(None) };
}

/// A session whose pieces written in FX-26 (checker, compilers, and what
/// else the front end has) run as register code on the hand register
/// machine, as the REPL's do, read back from their cache once made. The
/// reader stays lowered. Lowered, on the bytecode VM, they are some 30
/// times as slow: the tests that run them on every program, or every word
/// of the front end, took most of the suite's time.
/// (`the_front_end_compiled_checks_alike` compares the two.)
pub fn session() -> fixpt_fx26::session::Fx26Session {
    let mut s = fixpt_fx26::session::Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).expect("starts");
    // Where no machine code runs, on the cellular machine written in Rust.
    s.scheme.runtime_unrooted().front_end_run_word =
        Some(if fixpt_native::CELLULAR_AVAILABLE { fixpt_native::cellular::run_word_registers } else { fixpt_engine::cellular::run_word });
    s.front_end_compiled = true;
    s
}

/// [`session`], its front end loaded, and no step limit: for a test that
/// calls the front end's compilers itself.
pub fn front_end_session() -> fixpt_fx26::session::Fx26Session {
    let mut s = session();
    s.load_own_pieces().expect("loads");
    s.scheme.engine.set_step_limit(None);
    s
}

/// `f` with this thread's session for the pieces written in FX-26
/// (`session`), made on first use.
pub fn with_own<R>(f: impl FnOnce(&mut fixpt_fx26::session::Fx26Session) -> R) -> R {
    OWN.with(|s| {
        let mut s = s.borrow_mut();
        let s = s.get_or_insert_with(session);
        f(s)
    })
}

/// `f` with this thread's session for the evaluator written in FX-26 alone
/// (`OWN_EVAL`), made on first use.
pub fn with_own_eval<R>(f: impl FnOnce(&mut fixpt_fx26::session::Fx26Session) -> R) -> R {
    OWN_EVAL.with(|s| {
        let mut s = s.borrow_mut();
        let s = s.get_or_insert_with(session);
        f(s)
    })
}
