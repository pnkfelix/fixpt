//! `tupleof` and `tuple`, products labelled 1, 2, …, and a `tagcase` arm
//! that takes apart by position only such a product (`TODO.md` §191).

mod common;

#[test]
fn tuple_programs_do_as_they_say() {
    common::programs_do_as_they_say("tuples", 6);
}
