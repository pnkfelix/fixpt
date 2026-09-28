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
    // Field 1 is the trailer; the rest are values. A word's entry is
    // `docol`, or a native machine's number for its compiled code: the same
    // cells either way; a register word's, 0 or a machine's number. A word's
    // twin, its register code, is compared as code, as the word is.
    let entry = |w: Value, i: usize| {
        let v = h.bloblet_slot(w, i);
        let word = ka == Some(fixpt_heap::layout::kind("cellular-code"));
        let register = ka == Some(fixpt_heap::layout::kind("register-code"));
        let native = (word && v.as_fixnum() >= fixpt_heap::layout::cellular::PRIMITIVES as i64 || register)
            && i == fixpt_heap::layout::cellular::WORD_ENTRY;
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

thread_local! {
    /// This thread's session for the pieces written in FX-26: loading them
    /// is most of a check's or a compile's cost (1.3 s, against a few ms for
    /// a small program), and each program they are given begins afresh
    /// (`check-program` resets the checker; the compiler's globals only
    /// shadow), so one session serves every program a test gives them.
    static OWN: std::cell::RefCell<Option<fixpt_fx26::session::Fx26Session>> = const { std::cell::RefCell::new(None) };
}

/// `f` with this thread's session for the pieces written in FX-26, made
/// on first use.
pub fn with_own<R>(f: impl FnOnce(&mut fixpt_fx26::session::Fx26Session) -> R) -> R {
    OWN.with(|s| {
        let mut s = s.borrow_mut();
        let s = s.get_or_insert_with(|| fixpt_fx26::session::Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).expect("starts"));
        f(s)
    })
}

