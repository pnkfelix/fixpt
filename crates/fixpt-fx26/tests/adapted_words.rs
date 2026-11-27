//! The native code `adapt` compiles for a cellular word is known by the
//! word's weak reference, whose number is good only in its own heap: one
//! thread's heaps, one after another (`fixpt compile-file`, a heap a file)
//! or both alive, each know only their own (Heist's report, 2026-11-26: a
//! later heap asked for an earlier one's numbers, out of its bounds).

use fixpt_engine::Backend;
use fixpt_fx26::session::{Fx26Session, Strategy};
use fixpt_read::FileId;

fn run(s: &mut Fx26Session, text: &str) -> Vec<String> {
    let forms = s.checking(|c| c.read_in(FileId(0), text)).expect("reads");
    forms
        .iter()
        .map(|f| match s.run(f) {
            Ok(out) => format!("{}{}", out.printed, out.value.map(|v| v.unwrap_or_default()).unwrap_or_else(|e| format!("!! {e}"))),
            Err(e) => format!("error: {}", e.message),
        })
        .collect()
}

fn run_native(rt: &mut fixpt_runtime::Runtime, closure: fixpt_heap::Value, fuel: u64) -> fixpt_fx26::session::NativeRun {
    use fixpt_fx26::session::NativeRun;
    fixpt_native::direct::with_machine(|m| match m.compile(&mut rt.heap, closure) {
        Err(why) => NativeRun::Declined(why),
        Ok(procs) => NativeRun::Ran(m.call(rt, procs[0].1, &[], fuel).map_err(|t| t.what)),
    })
    .unwrap_or_else(|e| NativeRun::Ran(Err(e)))
}

/// A session in the native convention whose front end is cellular, so that
/// what it makes is adapted, and compiled where it is (as the CLI's).
fn native_session() -> Fx26Session {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    s.strategy = Strategy::Cellular;
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_registers);
    s.scheme.runtime_unrooted().front_end_run_word = Some(fixpt_native::cellular::run_word_registers);
    s.front_end_compiled = true;
    s.set_native_convention(true);
    s.native_runner = Some(run_native);
    s.native_compiler = Some(fixpt_native::direct::compile_closure);
    s.register_code = true;
    s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
    s.scheme.runtime_unrooted().adapt = Some(fixpt_native::direct::adapt);
    s
}

const PROGRAM: &str = "(define f (subr pure (int) (subr pure (int) int)) (lambda (x) (lambda (y) (+ x y))))\n((f 1) 2)\n";

#[test]
fn each_heap_knows_only_its_own_adapted_words() {
    if !fixpt_native::NATIVE_CONVENTION_AVAILABLE {
        return;
    }
    fixpt_native::direct::compile_when_adapting(true);
    let known = |s: &mut Fx26Session| fixpt_native::direct::adapted_words_known(&s.scheme.runtime_unrooted().heap);
    let mut a = native_session();
    let out = run(&mut a, PROGRAM);
    assert!(out.last().is_some_and(|o| o.ends_with('3')), "{out:?}");
    let in_a = known(&mut a);
    assert!(in_a > 0, "nothing adapted and compiled: the test tests nothing");
    // A second heap, the first alive: none of the first's.
    let mut b = native_session();
    assert_eq!(known(&mut b), 0);
    let out = run(&mut b, PROGRAM);
    assert!(out.last().is_some_and(|o| o.ends_with('3')), "{out:?}");
    assert!(known(&mut b) > 0);
    // The first's still its own, and still runs.
    assert_eq!(known(&mut a), in_a);
    let out = run(&mut a, PROGRAM);
    assert!(out.last().is_some_and(|o| o.ends_with('3')), "{out:?}");
    // Heaps made one after another, as `compile-file`'s, each its own.
    drop((a, b));
    for round in 0..8 {
        let mut c = native_session();
        assert_eq!(known(&mut c), 0, "round {round}");
        let out = run(&mut c, PROGRAM);
        assert!(out.last().is_some_and(|o| o.ends_with('3')), "round {round}: {out:?}");
    }
    fixpt_native::direct::compile_when_adapting(false);
}
