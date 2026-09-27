//! `list_to_vec`, which every primitive that walks a list uses: it must end
//! on a cyclic list, whether the cycle is the whole list or its tail.

use fixpt_heap::{Heap, Value};

#[test]
fn list_to_vec_refuses_cycles_and_keeps_proper_lists() {
    let mut h = Heap::new();
    for n in 1..8i64 {
        let items: Vec<Value> = (0..n).map(Value::fixnum).collect();
        let l = h.list_from(&items);
        assert_eq!(h.list_to_vec(l), Some(items.clone()), "length {n}");
        // Every way to close it into a cycle: the last cell back to cell k.
        for k in 0..n {
            let l = h.list_from(&items);
            let (mut last, mut target) = (l, l);
            for _ in 1..n {
                last = h.cdr(last);
            }
            for _ in 0..k {
                target = h.cdr(target);
            }
            h.set_cdr(last, target);
            assert_eq!(h.list_to_vec(l), None, "length {n}, back to {k}");
        }
    }
    let dotted = h.cons(Value::fixnum(1), Value::fixnum(2));
    assert_eq!(h.list_to_vec(dotted), None);
}
