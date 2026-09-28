//! Code in the heap's code area (`docs/object-model.md`, "A collected code
//! area"), run from its read+execute view: it reaches GC-traced fields of
//! its own bloblet PC-relatively, and the collector keeps them current.
#![allow(unsafe_code)]

use fixpt_heap::{Heap, Value, layout};
use fixpt_native::arm64::*;

/// A code bloblet of `fields` fields whose suffix is `code`, flushed.
fn code_bloblet(heap: &mut Heap, fields: usize, code: &[u32]) -> Value {
    let v = heap.make_code_bloblet(layout::kind("bloblet"), fields, code.len() * 4, false);
    let bytes: Vec<u8> = code.iter().flat_map(|i| i.to_le_bytes()).collect();
    heap.set_bloblet_bytes(v, 0, &bytes).expect("the suffix is writable");
    heap.flush_code(v);
    v
}

/// Run a code bloblet's code as a routine of no arguments and one word out.
fn run(heap: &Heap, v: Value) -> u64 {
    let at = heap.code_exec_address(v);
    // SAFETY: the bloblet's suffix is flushed code that follows the C
    // calling convention, reads only its own fields, and returns a word.
    let f: extern "C" fn() -> u64 = unsafe { std::mem::transmute(at) };
    f()
}

/// `ldr x0, <field 1>; ret`: field 1 is 8 bytes, two instructions, before
/// the first instruction. The field refers to a pair in the heap, which a
/// collection moves; the collector updates the field in place, and the code
/// reads the new reference, with no change to the code and no flush.
#[test]
fn code_reads_its_own_field_across_a_collection() {
    let mut heap = Heap::new();
    let c = code_bloblet(&mut heap, 2, &[ldr_lit(0, -2), ret()]);
    let pair = heap.cons(Value::fixnum(41), Value::fixnum(1));
    heap.set_bloblet_slot(c, 1, pair);
    heap.set_bloblet_slot(c, 2, Value::fixnum(5));
    assert_eq!(run(&heap, c), pair.raw());
    let root = heap.push_root(c);
    let mut before = pair;
    for round in 0..4 {
        heap.collect(&mut []);
        heap.verify().unwrap_or_else(|e| panic!("round {round}: {e}"));
        assert_eq!(heap.root_at(root), c, "the code bloblet does not move");
        let now = heap.bloblet_slot(c, 1);
        // The semispaces alternate, so each collection moves the pair.
        assert_ne!(now, before, "the pair moved (round {round})");
        before = now;
        let read = Value(run(&heap, c));
        assert_eq!(read, now, "the code reads the field as the collector left it");
        assert_eq!(heap.car(read), Value::fixnum(41));
    }
    heap.pop_roots_to(root);
}

/// Field 2, 16 bytes before the code: `ldr x0, <field 2>` is four
/// instructions back. Its fixnum comes back as it was stored.
#[test]
fn code_reads_a_farther_field() {
    let mut heap = Heap::new();
    let c = code_bloblet(&mut heap, 2, &[ldr_lit(0, -4), ret()]);
    heap.set_bloblet_slot(c, 2, Value::fixnum(12345));
    assert_eq!(Value(run(&heap, c)), Value::fixnum(12345));
}

/// Code no longer reachable is freed, and its room given to new code, which
/// runs as written: the reused block was flushed.
#[test]
fn freed_code_room_holds_new_code_that_runs() {
    let mut heap = Heap::new();
    let first = code_bloblet(&mut heap, 1, &[movz(0, 11, 0), ret()]);
    assert_eq!(run(&heap, first), 11);
    let at = heap.code_exec_address(first);
    heap.collect(&mut []);
    assert_eq!(heap.code_words(), (0, 0), "nothing refers to it: freed");
    let second = code_bloblet(&mut heap, 1, &[movz(0, 22, 0), ret()]);
    assert_eq!(heap.code_exec_address(second), at, "the same room");
    assert_eq!(run(&heap, second), 22, "the new code, not the old");
}
