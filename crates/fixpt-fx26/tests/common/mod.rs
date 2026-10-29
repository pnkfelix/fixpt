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

/// How many shards a long test's programs are dealt into, a test for each
/// ([`sharded`]), so that nextest runs them at once (`TODO.md` §167).
pub const SHARDS: usize = 8;

/// The items of shard `k` of [`SHARDS`]: every `SHARDS`th from the `k`th,
/// so that the long and the short are spread, and a program added needs no
/// test added.
pub fn shard<T>(items: impl IntoIterator<Item = T>, k: usize) -> Vec<T> {
    items.into_iter().enumerate().filter(|(i, _)| i % SHARDS == k).map(|(_, x)| x).collect()
}

/// A module `$module` of a test for each shard of [`SHARDS`], each calling
/// `$f(k)` of the module this is used in.
#[allow(unused_macros)]
macro_rules! sharded {
    ($module:ident, $f:ident) => {
        mod $module {
            #[test]
            fn shard_0() {
                super::$f(0);
            }
            #[test]
            fn shard_1() {
                super::$f(1);
            }
            #[test]
            fn shard_2() {
                super::$f(2);
            }
            #[test]
            fn shard_3() {
                super::$f(3);
            }
            #[test]
            fn shard_4() {
                super::$f(4);
            }
            #[test]
            fn shard_5() {
                super::$f(5);
            }
            #[test]
            fn shard_6() {
                super::$f(6);
            }
            #[test]
            fn shard_7() {
                super::$f(7);
            }
            const _: () = assert!(crate::common::SHARDS == 8, "a test for each shard");
        }
    };
}
#[allow(unused_imports)]
pub(crate) use sharded;

/// The bootstrap program (`fixpt_fx26::bootstrap_program`) compiled by the
/// compiler written in FX-26 to one cellular word, with register code if
/// `registers`, in `sc`'s heap: what the tests of the native compilers
/// compare word by word. The compile is a minute and more in a debug
/// build, the same in each of them, so it is kept: the word copied into a
/// heap of its own and written as an image in the build's temporary
/// directory, keyed by the sources (`FIXPT_BUILD_HASH`), the program and
/// `registers`, and read back by the next (`TODO.md` §167). A lock on the
/// file makes one test compile while the others wait for it.
pub fn bootstrap_compiled(sc: &mut fixpt_scheme::Session, registers: bool) -> fixpt_scheme::Handle {
    use fixpt_read::FileId;
    use std::hash::{Hash, Hasher};
    let text = fixpt_fx26::bootstrap_program();
    let mut key = std::collections::hash_map::DefaultHasher::new();
    (env!("FIXPT_BUILD_HASH"), &text, registers).hash(&mut key);
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"));
    let path = dir.join(format!("bootstrap-compiled-{:016x}.img", key.finish()));
    let lock = std::fs::File::create(path.with_extension("lock")).expect("a lock file");
    lock.lock().expect("locked");
    if let Ok(bytes) = std::fs::read(&path)
        && let Ok(from) = fixpt_heap::image::load_trusted(&bytes)
    {
        let root = from.roots_slice()[0];
        return sc.make(|m| m.heap().copy_graph_from(&from, root));
    }
    let facts = fixpt_fx26::syn::rust_facts(sc, FileId(0), &text).expect("checks");
    let compile = if registers { fixpt_fx26::syn::compile_to_word_with_registers } else { fixpt_fx26::syn::compile_to_word };
    let word = compile(sc, FileId(0), &text, facts).expect("parses").expect("compiles");
    sc.make(|m| {
        let mut alone = Heap::new();
        let w = m.get(word);
        let copy = alone.copy_graph_from(m.heap(), w);
        alone.push_root(copy);
        let tmp = path.with_extension(format!("tmp{}", std::process::id()));
        if std::fs::write(&tmp, fixpt_heap::image::dump_packed(&alone)).is_ok() {
            let _ = std::fs::rename(&tmp, &path);
        }
        Value::NULL
    });
    // Those of other builds, unused for a day, let go.
    let day = std::time::Duration::from_secs(24 * 3600);
    for e in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let old = e.metadata().and_then(|m| m.modified()).ok().and_then(|t| t.elapsed().ok()).is_some_and(|a| a > day);
        if old && e.file_name().to_string_lossy().starts_with("bootstrap-compiled-") {
            let _ = std::fs::remove_file(e.path());
        }
    }
    word
}
