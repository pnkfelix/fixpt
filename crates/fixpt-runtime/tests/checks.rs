//! The heap is built with the checks of the rest of the build, whatever its
//! optimization (`Cargo.toml`'s `[profile.dev.package.fixpt-heap]`): its
//! `debug_assert!`s, and its arithmetic's overflow, are checked where this
//! crate's are.

#[test]
fn the_heap_checks_what_the_rest_of_the_build_checks() {
    let overflow = std::panic::catch_unwind(|| std::hint::black_box(u8::MAX) + std::hint::black_box(1u8)).is_err();
    assert_eq!(fixpt_heap::built_checking(), (cfg!(debug_assertions), overflow));
}
