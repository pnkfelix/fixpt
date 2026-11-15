//! How much stack the front end's checks take, held to a budget: the front
//! end's own sources, and nesting of a known depth, each checked on a thread
//! of a fixed stack (`debug_stack`, `scripts/debuggers/fixpt_gdb.py`). Each
//! checker method's frame was held to a debt too, until the front end was
//! built at opt-level 1 in a debug build (2026-11-13): then its frames are
//! nearly a release build's, and their sizes moved with what nothing
//! overflows by, so the user had it taken out (2026-11-15); these budgets
//! are what holds.

use fixpt_fx26::session::compile_program_as;

/// `f` run on a thread of `bytes` of stack.
fn in_stack<T: Send + 'static>(bytes: usize, f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new().stack_size(bytes).spawn(f).expect("a thread").join().expect("no panic, and no overflow")
}

const MIB: usize = 1 << 20;

#[test]
fn the_front_end_checks_in_three_mib() {
    // The measure (2026-11-09): a debug build needs some 2.2 MiB, a release
    // build much less.
    let budget = if cfg!(debug_assertions) { 3 * MIB } else { MIB };
    let r = in_stack(budget, || compile_program_as(&fixpt_fx26::front_end(), "fx:").map(|_| ()).map_err(|e| String::from(e.message)));
    assert_eq!(r, Ok(()));
}

#[test]
fn calls_nested_a_hundred_deep_check_in_two_mib() {
    // `(+ 1 (+ 1 … 0))`: each level a call, its argument the next.
    let depth = 100;
    let program = format!("{}0{}\n", "(+ 1 ".repeat(depth), ")".repeat(depth));
    let budget = if cfg!(debug_assertions) { 2 * MIB } else { MIB / 2 };
    let r = in_stack(budget, move || {
        fixpt_fx26::compare::check_with_rust_checker(&mut fixpt_fx26::Checker::new(), &program).map_err(|e| String::from(e.message))
    });
    assert_eq!(r.map(|v| v.len()), Ok(1));
}
