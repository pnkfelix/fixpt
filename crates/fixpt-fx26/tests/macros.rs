//! Typed hygienic macros, the prototype (`docs/research/typed-macros.md`):
//! each program in `programs/macros` says what it gives, or that it is
//! refused and why.
mod common;

#[test]
fn macro_programs_do_as_they_say() {
    common::programs_do_as_they_say("macros", 26);
}
