//! A session that runs no lowered code loads no Scheme of FX-26's: neither
//! its run-time environment (`runtime.scm`), which only lowered code calls,
//! nor, in time, the prelude (`TODO.md` §252: FX-26 sessions on a host of
//! their own, the Scheme engine made only where lowered code runs). Held
//! here so that nothing brings the dependence back unseen.

use fixpt_engine::Backend;
use fixpt_fx26::session::{Fx26Session, Strategy};

/// `%fx26-unit`, `runtime.scm`'s first definition: whether it was loaded.
fn runtime_loaded(s: &Fx26Session) -> bool {
    s.scheme.is_bound("%fx26-unit")
}

#[test]
fn a_compiled_program_loads_no_runtime_in_scheme() {
    let mut s = Fx26Session::with_backend_preloaded_in(Backend::Bytecode, None, false, Strategy::Cellular).expect("starts");
    assert!(!runtime_loaded(&s), "loaded as the session starts");
    let v = s.run_program("(define f (->* (int) int) (lambda (x) (* x 2)))\n(f 21)").expect("checks");
    assert_eq!(v, Ok("42".to_string()));
    assert!(!runtime_loaded(&s), "loaded by a program run compiled");
}

#[test]
fn a_lowered_program_loads_it() {
    let mut s = Fx26Session::with_backend_preloaded_in(Backend::Bytecode, None, false, Strategy::Lower).expect("starts");
    let v = s.run_program("(define f (->* (int) int) (lambda (x) (* x 2)))\n(f 21)").expect("checks");
    assert_eq!(v, Ok("42".to_string()));
    assert!(runtime_loaded(&s), "what lowered code calls");
}
