//! A rep in the heap (`heap-types.md`, "Serialization"): a frozen product
//! of the symbol `type-rep` and a bytevector of the rep's binary form
//! ([`crate::binary`]). Ordinary data: a `.fasl`'s image and a heap dump
//! carry it as they carry any value.
//!
//! Its constants are, for now, in its binary form, by key; their heap
//! objects, one for each key in a session (`heap-types.md`, "Variables and
//! identity"), come with evidence by rep (its step 3).

use crate::{binary, Rep};
use fixpt_heap::{Heap, Value};

/// The tag of a rep's product.
pub const TAG: &str = "type-rep";

/// Whether every rep read is validated, from the trusted pieces too: the
/// environment variable `FIXPT_VALIDATE_REPS` set (the user's, 2026-11-01;
/// for debugging, and for tests).
pub fn validate_all() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("FIXPT_VALIDATE_REPS").is_some())
}

/// Rep `rep`, in `heap`.
pub fn to_heap(heap: &mut Heap, rep: &Rep) -> Value {
    let tag = heap.intern(TAG);
    let base = heap.push_root(tag);
    let bytes = heap.make_bytevector(&binary::encode(rep));
    heap.push_root(bytes);
    let (tag, bytes) = (heap.root_at(base), heap.root_at(base + 1));
    let v = heap.make_frozen(fixpt_heap::layout::kind("product"), &[tag, bytes]);
    heap.pop_roots_to(base);
    v
}

/// Whether `v` is a rep in `heap`.
pub fn is_rep(heap: &Heap, v: Value) -> bool {
    v.is_bloblet()
        && heap.bloblet_kind(v) == fixpt_heap::layout::kind("product")
        && heap.bloblet_len(v) == 2
        && heap.is_a(heap.product_field(v, 1), fixpt_heap::ObjType::Symbol)
        && heap.symbol_name(heap.product_field(v, 1)) == TAG
}

/// The rep `v` holds; or why not. Validated if `trusted` is false, or if
/// every rep is to be ([`validate_all`]).
pub fn from_heap(heap: &Heap, v: Value, trusted: bool) -> Result<Rep, String> {
    if !is_rep(heap, v) {
        return Err("not a rep".into());
    }
    let b = heap.product_field(v, 2);
    let bytes: Vec<u8> = (0..heap.bytevector_len(b)).map(|i| heap.bytevector_ref(b, i)).collect();
    binary::decode(&bytes, !trusted || validate_all())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Arg, Builder};

    #[test]
    fn a_rep_in_the_heap_is_itself() {
        let mut b = Builder::new();
        let int = b.name("int");
        let base = b.add("base", &[], vec![Arg::Sym(int)]);
        let rep = b.finish(base).expect("finishes").rep;
        let mut heap = Heap::new();
        let v = to_heap(&mut heap, &rep);
        assert!(is_rep(&heap, v));
        assert_eq!(from_heap(&heap, v, false).expect("reads"), rep);
        assert!(!is_rep(&heap, Value::FALSE));
    }
}
