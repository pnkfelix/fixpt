//! Shorthands for types written often: `tupleof` and `tuple`, products
//! labelled 1, 2, …, with a `tagcase` arm that takes apart by position only
//! such a product (`TODO.md` §191); and `(listof T)`, `(listof T acyclic)`
//! (§198).

mod common;

#[test]
fn tuple_programs_do_as_they_say() {
    common::programs_do_as_they_say("tuples", 6);
}

#[test]
fn listof_programs_do_as_they_say() {
    common::programs_do_as_they_say("listof", 3);
}
