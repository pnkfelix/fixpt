//! Procedural macros, a prototype (`TODO.md` §228; `docs/research/
//! typed-macros.md`, "Procedural macros, prototyped"): explicit renaming
//! and syntactic closures, beside `syntax-rules`, each program in
//! `programs/procedural` saying what it gives, or that it is refused and why.
mod common;

#[test]
fn procedural_programs_do_as_they_say() {
    common::programs_do_as_they_say("procedural", 14);
}
