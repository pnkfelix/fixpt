//! Processes and `par` (`docs/fx26.md`, "Processes"; kayak's request,
//! `TODO.md` §92): each program in `programs/processes` says on its first
//! line what it gives, `;; => value`, or what its refusal or failure says,
//! `;; ! words`. Each is run every way FX-26 runs: lowered to Scheme, by the
//! evaluator written in FX-26, compiled to cellular code, and compiled to
//! native code form by form, as the REPL runs it; and the ones that give a
//! value, under schedules of many orders. Both checkers agree on each
//! (`tests/checker.rs`, `every_test_program`).

mod common;

use fixpt_engine::Backend;
use fixpt_fx26::session::{Fx26Session, NativeRun, Strategy};
use fixpt_heap::Value;
use fixpt_read::FileId;

/// The programs, and what each says it gives (`Ok`) or says (`Err`).
fn programs() -> Vec<(String, String, Result<String, String>)> {
    let dir = format!("{}/tests/programs/processes", env!("CARGO_MANIFEST_DIR"));
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    names
        .into_iter()
        .map(|path| {
            let text = std::fs::read_to_string(&path).unwrap();
            let first = text.lines().next().unwrap_or("").to_string();
            let says = match (first.strip_prefix(";; => "), first.strip_prefix(";; ! ")) {
                (Some(v), _) => Ok(v.to_string()),
                (_, Some(w)) => Err(w.to_string()),
                _ => panic!("{}: its first line says nothing", path.display()),
            };
            (path.file_name().unwrap().to_string_lossy().to_string(), text, says)
        })
        .collect()
}

/// Whether `got`, a value or why there is none, is what `says` says.
fn as_said(says: &Result<String, String>, got: &Result<String, String>) -> bool {
    match (says, got) {
        (Ok(want), Ok(v)) => v == want,
        (Err(want), Err(e)) => e.contains(want.as_str()),
        _ => false,
    }
}

/// A program's last value, lowered and run on the bytecode engine, with
/// the scheduler taking its run queue in `seed`'s order.
fn lowered(text: &str, seed: Option<i64>) -> Result<String, String> {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    fixpt_runtime::sched::set_seed(&mut s.scheme.runtime_unrooted().heap, seed);
    match s.run_program(text) {
        Ok(r) => r,
        Err(e) => Err(e.message),
    }
}

/// What the pieces written in FX-26 print, as a value or why not.
fn printed(out: String) -> Result<String, String> {
    match out.strip_prefix("!! ") {
        Some(e) => Err(e.to_string()),
        None => Ok(out),
    }
}

fn run_native(rt: &mut fixpt_runtime::Runtime, closure: Value, fuel: u64) -> NativeRun {
    fixpt_native::direct::with_machine(|m| match m.compile(&mut rt.heap, closure) {
        Err(why) => NativeRun::Declined(why),
        Ok(procs) => NativeRun::Ran(m.call(rt, procs[0].1, &[], fuel).map_err(|t| t.what)),
    })
    .unwrap_or_else(|e| NativeRun::Ran(Err(e)))
}

/// A program run form by form in the native convention, as the REPL runs
/// it: its last value, or the first error.
fn native(text: &str) -> Result<String, String> {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    s.strategy = Strategy::Cellular;
    s.set_native_convention(true);
    s.native_runner = Some(run_native);
    s.native_compiler = Some(fixpt_native::direct::compile_closure);
    s.register_code = true;
    s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
    s.scheme.runtime_unrooted().adapt = Some(fixpt_native::direct::adapt);
    let forms = s.checker.read_in(FileId(0), text).map_err(|e| e.message)?;
    let mut last = Ok(String::new());
    for o in s.run_forms(&forms).map_err(|e| e.message)? {
        match o {
            Ok(o) => match o.value {
                Ok(Some(v)) => last = Ok(v),
                Ok(None) => {}
                Err(e) => return Err(e),
            },
            Err(e) => return Err(e.message),
        }
    }
    last
}

/// Every program, every way it runs: as it says.
#[test]
fn process_programs_do_as_they_say_every_way() {
    let mut wrong = Vec::new();
    let all = programs();
    assert!(all.len() >= 12, "only {} programs", all.len());
    for (name, text, says) in &all {
        let ways = [
            ("lowered", lowered(text, None)),
            ("evaluated", printed(common::with_own(|s| s.eval_with_own_evaluator(text)).expect("runs"))),
            ("compiled", printed(common::with_own(|s| s.compile_with_own_compiler(text)).expect("runs"))),
            ("native", native(text)),
        ];
        for (way, got) in ways {
            if !as_said(says, &got) {
                wrong.push(format!("{name}, {way}: says {says:?}, gives {got:?}"));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// What gives a value gives it whatever order the scheduler runs its tasks
/// in: `par`'s answer, the dataflow of I-cells, and messages each sent by
/// one sender, which arrive in the order sent.
#[test]
fn answers_hold_under_any_schedule() {
    let mut wrong = Vec::new();
    for (name, text, says) in programs().iter().filter(|(_, _, s)| s.is_ok()) {
        for seed in 1..=20 {
            let got = lowered(text, Some(seed * 7919));
            if !as_said(says, &got) {
                wrong.push(format!("{name}, seed {seed}: gives {got:?}"));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A deadlock is an error, said, not a hang: the program waits on a cell
/// no task is left to fill.
#[test]
fn a_deadlock_is_an_error() {
    let text = "(define c (icell int @c) (make-icell))\n\
                (define w (addr int @w) (spawn (box int p) (icell-put! c (receive box))))\n\
                (icell-get c)";
    for got in [lowered(text, None), native(text)] {
        assert!(got.as_ref().is_err_and(|e| e.contains("a deadlock")), "{got:?}");
    }
}

/// Arrival order is a choice when two processes send to one mailbox: under
/// schedules of different orders, the receiver sees both. That is what
/// `nondet` says of a process that receives.
#[test]
fn arrival_order_varies_with_the_schedule() {
    let text = include_str!("programs/schedules/arrival-order.fx");
    let seen: std::collections::BTreeSet<String> = (1..=20).map(|seed| lowered(text, Some(seed * 104729)).expect("runs")).collect();
    assert_eq!(seen.into_iter().collect::<Vec<_>>(), vec!["(1 2)".to_string(), "(2 1)".to_string()]);
}

/// `par`'s interference relation (P5), cell by cell: a program of two
/// branches for each pair of effects on one region, which both checkers
/// accept, or refuse as interfering, as FX's table says (`processes.rs`,
/// `interference`). Two writes, a write against a read, a fill or an await,
/// two sends (which arrives first is a choice), and two I/O effects
/// interfere; a fill against an await is dataflow; allocation interferes
/// with nothing.
#[test]
fn the_interference_table_both_checkers() {
    use fixpt_fx26::Checker;
    let defs = "(define rx (ref int @x) (new 0))\n\
                (define cx (icell int @x) (make-icell))\n\
                (define ax (addr int @x) (spawn (box int p) (begin (receive box) #u)))\n";
    let effects = [
        ("read", "(get rx)"),
        ("write", "(set rx 1)"),
        ("alloc", "(the (ref int @x) (new 0))"),
        ("init", "(icell-put! cx 1)"),
        ("await", "(icell-get cx)"),
        ("send", "(send ax 1)"),
        ("io", "(write-out \"x\")"),
    ];
    let clash = |a: &str, b: &str| {
        let pair = |x: &str, y: &str| (a == x && b == y) || (a == y && b == x);
        pair("write", "write")
            || pair("write", "read")
            || pair("write", "init")
            || pair("write", "await")
            || pair("send", "send")
            || pair("io", "io")
    };
    let mut wrong = Vec::new();
    for (i, (a, ea)) in effects.iter().enumerate() {
        for (b, eb) in &effects[i..] {
            let program = format!("{defs}(par ((u (begin {ea} 0)) (v (begin {eb} 0))) (+ u v))\n");
            let rust = fixpt_fx26::compare::check_with_rust_checker(&mut Checker::new(), &program).map_err(|e| e.message);
            let ours = common::with_own(|s| s.check_with_own_checker(&program)).expect("parses").map_err(|e| e.message);
            let refused = |r: &Result<Vec<String>, String>| r.as_ref().err().is_some_and(|m| m.contains("interfere"));
            if refused(&rust) != clash(a, b) || refused(&ours) != clash(a, b) || rust.is_err() != ours.is_err() {
                wrong.push(format!("{a} against {b}: Rust {rust:?}, FX-26 {ours:?}"));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A trap in a process fails the form whose run it was in, as a trap in the
/// program would (a failure in any process ends the run); the next form
/// runs as ever, the scheduler begun again.
#[test]
fn a_process_that_fails_fails_the_run() {
    let text = include_str!("programs/schedules/process-fails.fx");
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let forms = s.checker.read_in(FileId(0), text).expect("reads");
    let outs: Vec<Result<Option<String>, String>> = forms.iter().map(|f| s.run(f).expect("checks").value).collect();
    assert!(outs[2].as_ref().is_err_and(|e| e.contains("an i-cell written twice")), "{outs:?}");
    assert_eq!(outs[3], Ok(Some("3".to_string())), "{outs:?}");
}
