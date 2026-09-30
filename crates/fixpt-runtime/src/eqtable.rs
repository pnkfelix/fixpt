//! Tables keyed by identity (`eqtable`, PLAN.md Q5), hashed by address.
//!
//! A collection moves objects, so an address hash goes stale at one. Each
//! table is stamped with the heap's count of collections (minor and major)
//! when its keys were last hashed; an operation that finds the count moved
//! rehashes every entry first. That is Larceny's design
//! (`src/Lib/Common/hashtable.sch`) in its simplest form: one stamp, not a
//! tablet for old keys and one for young, which would rehash only the young
//! after a minor collection. Rehashing relinks the entries it has, so it
//! allocates nothing, and allocation never collects outside a safepoint, so
//! nothing moves during an operation.
//!
//! A table is a bloblet of kind `eqtable`, its fields the stamp, the count
//! and the buckets (which it prints only the count of); `buckets` a vector of
//! chains; an entry a vector `[key, value, next]`, `next` another entry or
//! `#f`. The type is opaque to programs (`check::EQTABLE`), so nothing else
//! sees this layout.

use fixpt_heap::{Heap, Value};

const STAMP: usize = 1;
const COUNT: usize = 2;
const BUCKETS: usize = 3;
const KEY: usize = 0;
const VALUE: usize = 1;
const NEXT: usize = 2;

/// A new table, with 8 buckets.
pub fn make(heap: &mut Heap) -> Value {
    let buckets = heap.make_vector(8, Value::FALSE);
    let t = heap.make_bloblet(fixpt_heap::layout::kind("eqtable"), 3, 0, false);
    heap.set_bloblet_slot(t, STAMP, Value::fixnum(heap.collections() as i64));
    heap.set_bloblet_slot(t, COUNT, Value::fixnum(0));
    heap.set_bloblet_slot(t, BUCKETS, buckets);
    t
}

/// Which of `n` buckets `key` is in, as its address stands now.
fn bucket_of(key: Value, n: usize) -> usize {
    // SplitMix64's finalizer: addresses differ mostly in their middle bits.
    let mut z = key.raw();
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^= z >> 31;
    (z % n as u64) as usize
}

/// Every entry of `t` linked into `buckets` by its key's address now.
fn relink(heap: &mut Heap, t: Value, buckets: Value) {
    let old = heap.bloblet_slot(t, BUCKETS);
    let n = heap.obj_len(buckets);
    let mut entries = Vec::new();
    for i in 0..heap.obj_len(old) {
        let mut e = heap.obj_ref(old, i);
        while !e.is_false() {
            entries.push(e);
            e = heap.obj_ref(e, NEXT);
        }
        heap.obj_set(old, i, Value::FALSE);
    }
    for e in entries {
        let b = bucket_of(heap.obj_ref(e, KEY), n);
        let first = heap.obj_ref(buckets, b);
        heap.obj_set(e, NEXT, first);
        heap.obj_set(buckets, b, e);
    }
    heap.set_bloblet_slot(t, BUCKETS, buckets);
    heap.set_bloblet_slot(t, STAMP, Value::fixnum(heap.collections() as i64));
}

/// `t`'s entries rehashed, if a collection may have moved their keys.
fn fresh(heap: &mut Heap, t: Value) {
    if heap.bloblet_slot(t, STAMP) != Value::fixnum(heap.collections() as i64) {
        let buckets = heap.bloblet_slot(t, BUCKETS);
        relink(heap, t, buckets);
    }
}

/// The entry for `key` in `t`, and the entry before it in its chain.
fn find(heap: &mut Heap, t: Value, key: Value) -> (Option<Value>, Option<Value>) {
    fresh(heap, t);
    let buckets = heap.bloblet_slot(t, BUCKETS);
    let mut before = None;
    let mut e = heap.obj_ref(buckets, bucket_of(key, heap.obj_len(buckets)));
    while !e.is_false() {
        if heap.obj_ref(e, KEY) == key {
            return (Some(e), before);
        }
        before = Some(e);
        e = heap.obj_ref(e, NEXT);
    }
    (None, before)
}

/// `key`'s value in `t`, or `default`.
pub fn get(heap: &mut Heap, t: Value, key: Value, default: Value) -> Value {
    match find(heap, t, key).0 {
        Some(e) => heap.obj_ref(e, VALUE),
        None => default,
    }
}

pub fn has(heap: &mut Heap, t: Value, key: Value) -> bool {
    find(heap, t, key).0.is_some()
}

pub fn count(heap: &Heap, t: Value) -> i64 {
    heap.bloblet_slot(t, COUNT).as_fixnum()
}

/// `key` given `value` in `t`; the buckets doubled past two entries each.
pub fn set(heap: &mut Heap, t: Value, key: Value, value: Value) {
    if let Some(e) = find(heap, t, key).0 {
        heap.obj_set(e, VALUE, value);
        return;
    }
    let n = count(heap, t) + 1;
    heap.set_bloblet_slot(t, COUNT, Value::fixnum(n));
    let size = heap.obj_len(heap.bloblet_slot(t, BUCKETS));
    if n as usize > 2 * size {
        let bigger = heap.make_vector(2 * size, Value::FALSE);
        relink(heap, t, bigger);
    }
    let buckets = heap.bloblet_slot(t, BUCKETS);
    let b = bucket_of(key, heap.obj_len(buckets));
    let e = heap.make_vector(3, Value::FALSE);
    heap.obj_set(e, KEY, key);
    heap.obj_set(e, VALUE, value);
    let first = heap.obj_ref(buckets, b);
    heap.obj_set(e, NEXT, first);
    heap.obj_set(buckets, b, e);
}

/// `key` taken out of `t`, if it is there.
pub fn delete(heap: &mut Heap, t: Value, key: Value) {
    let (Some(e), before) = find(heap, t, key) else { return };
    let next = heap.obj_ref(e, NEXT);
    match before {
        Some(b) => heap.obj_set(b, NEXT, next),
        None => {
            let buckets = heap.bloblet_slot(t, BUCKETS);
            let b = bucket_of(key, heap.obj_len(buckets));
            heap.obj_set(buckets, b, next);
        }
    }
    let n = count(heap, t) - 1;
    heap.set_bloblet_slot(t, COUNT, Value::fixnum(n));
}
