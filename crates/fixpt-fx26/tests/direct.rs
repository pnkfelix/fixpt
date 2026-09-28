//! Code in the native convention (`docs/research/native-conventions.md`,
//! step 2; `fixpt_native::direct`): first-order procedures compiled from
//! their register code, called by `bl`, on native frames, give what the
//! Rust machine gives; what they cannot do they decline.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_fx26::Checker;
use fixpt_heap::Value;
use fixpt_native::arm64::disasm::disassemble;
use fixpt_native::direct::{DirectMachine, DirectTrap};
use fixpt_read::FileId;

const FUEL: u64 = 100_000_000;

/// What a run in the native convention gave, and the Rust machine's.
struct Ran {
    direct: Result<String, String>,
    rust: String,
    /// The procedure's own instructions, one to a line.
    code: String,
    /// How many collections its run made.
    collections: u64,
    /// Words in the heap's code area in use just after the run, and after
    /// a collection then, when nothing refers to the code any more.
    code_words: (usize, usize),
}

/// `defs`, then `name` compiled in the native convention and called with
/// `args`; and `(name args…)` on the Rust machine, from the same `defs`.
fn run(defs: &str, name: &str, args: &[i64], fuel: u64) -> Ran {
    run_collecting(defs, name, args, fuel, None)
}

/// The same, collecting at every `gc_every`th safepoint if asked.
fn run_collecting(defs: &str, name: &str, args: &[i64], fuel: u64, gc_every: Option<u64>) -> Ran {
    let call = format!("({name} {})", args.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(" "));
    let rust = on_rust_machine(&format!("{defs}\n{call}"));
    Ran { rust, ..direct_in(defs, name, args, fuel, gc_every) }
}

/// The same without the Rust machine's run: for what it would not finish.
fn direct_only(defs: &str, name: &str, args: &[i64], fuel: u64) -> Ran {
    direct_in(defs, name, args, fuel, None)
}

fn direct_in(defs: &str, name: &str, args: &[i64], fuel: u64, gc_every: Option<u64>) -> Ran {
    let rust = String::new();
    let text = format!("{defs}\n{name}");
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), &text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).map(|(f, _)| c.top(f).expect("checks")).collect();
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let mut m = DirectMachine::new().expect("maps");
    s.scheme.scope(|sc| {
        let w = sc.make(|h| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(h.heap(), &c, &text);
            comp.registers = true;
            comp.program(&tops).expect("compiles")
        });
        let none = sc.make(|_| Value::NULL);
        let h = sc.call_global("%run-word", &[w, none]).expect("defines");
        // Nothing allocates from here on, so nothing moves.
        let mut closure = Value::NULL;
        sc.make(|m| {
            closure = m.get(h);
            closure
        });
        if let Some(n) = gc_every {
            sc.set_gc_every(n);
        }
        let rt = sc.runtime_unrooted();
        if std::env::var("DIRECT_SHOW").is_ok() {
            eprintln!("{}", fixpt_runtime::disasm::disassemble(&rt.heap, closure));
        }
        let procs = match m.compile(&mut rt.heap, closure) {
            Ok(p) => p,
            Err(e) => return Ran { direct: Err(format!("declined: {e}")), rust, code: String::new(), collections: 0, code_words: (0, 0) },
        };
        let p = procs[0].1;
        let code: String = m.instructions(&rt.heap, p).iter().enumerate().map(|(i, w)| disassemble(*w, i as i64) + "\n").collect();
        if std::env::var("DIRECT_SHOW").is_ok() {
            eprintln!("{code}");
        }
        let vals: Vec<Value> = args.iter().map(|a| Value::fixnum(*a)).collect();
        let before = rt.heap.gc_count;
        let direct = m.call(rt, p, &vals, fuel).map(|v| fixpt_runtime::write_value(&rt.heap, v)).map_err(|DirectTrap { what, .. }| what);
        let collections = rt.heap.gc_count - before;
        let after_run = rt.heap.code_words().0;
        rt.heap.collect(&mut []);
        Ran { direct, rust, code, collections, code_words: (after_run, rt.heap.code_words().0) }
    })
}

fn on_rust_machine(text: &str) -> String {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).map(|(f, _)| c.top(f).expect("checks")).collect();
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    s.scheme.scope(|sc| {
        let w = sc.make(|h| fixpt_fx26::cellular::Compiler::new(h.heap(), &c, text).program(&tops).expect("compiles"));
        let none = sc.make(|_| Value::NULL);
        match sc.call_global("%run-word", &[w, none]) {
            Ok(v) => sc.write(v),
            Err(e) => format!("!! {e}"),
        }
    })
}

fn bench(name: &str) -> String {
    let text = std::fs::read_to_string(format!("{}/tests/programs/bench/{name}.fx", env!("CARGO_MANIFEST_DIR"))).unwrap();
    // The definitions: everything but the last line, the call.
    let lines: Vec<&str> = text.trim_end().lines().collect();
    lines[..lines.len() - 1].join("\n")
}

/// The identity on ints is two instructions: nothing to check, no frame.
#[test]
fn the_identity_is_a_move_and_a_return() {
    let r = run("(define id (subr pure (int) int) (lambda (x) x))", "id", &[42], FUEL);
    assert_eq!(r.direct, Ok("42".into()));
    assert_eq!(r.rust, "42");
    assert_eq!(r.code, "mov x0, x1\nret\n");
}

/// Adding one is one instruction, and its check of overflow.
#[test]
fn adding_one_checks_only_overflow() {
    let r = run("(define inc (subr pure (int) int) (lambda (x) (+ x 1)))", "inc", &[41], FUEL);
    assert_eq!(r.direct, Ok("42".into()));
    assert!(r.code.starts_with("adds x0, x1, #8\nb.vs @3\nret\n"), "{}", r.code);
    let r = run("(define inc (subr pure (int) int) (lambda (x) (+ x 1)))", "inc", &[(1 << 60) - 1], FUEL);
    assert_eq!(r.direct, Err("integer overflow".into()));
    assert!(r.rust.starts_with("!!"), "{}", r.rust);
}

/// The benchmarks' procedures, as the Rust machine runs them.
#[test]
fn fib_and_tak_as_the_rust_machine_runs_them() {
    let r = run(&bench("fib"), "fib", &[20], FUEL);
    assert_eq!(r.direct, Ok(r.rust.clone()), "{}", r.code);
    let r = run(&bench("tak"), "tak", &[18, 12, 6], FUEL);
    assert_eq!(r.direct, Ok(r.rust.clone()), "{}", r.code);
}

/// Several procedures calling each other by their globals, one in tail
/// position.
#[test]
fn calls_between_procedures() {
    let defs = "(define add3 (subr pure (int int int) int) (lambda (a b c) (+ a (+ b c))))\n\
                (define f (subr pure (int) int) (lambda (n) (add3 n (+ n 1) (+ n 2))))";
    let r = run(defs, "f", &[10], FUEL);
    assert_eq!(r.direct, Ok("33".into()), "{}", r.code);
    assert_eq!(r.rust, "33");
}

/// Running out of fuel, and of stack, are traps, as on the other machines.
#[test]
fn fuel_and_stack_run_out() {
    let forever = "(define forever (subr spin (int) int) (lambda (n) (forever (+ n 1))))";
    assert_eq!(direct_only(forever, "forever", &[0], 100_000).direct, Err("out of fuel".into()));
    let deep = "(define deep (subr spin (int) int) (lambda (n) (+ 1 (deep n))))";
    assert_eq!(run(deep, "deep", &[0], FUEL).direct, Err("stack overflow".into()));
}

/// Higher-order code: a global's procedure passed as a value and called
/// through its native closure; closures made as the code runs, reading what
/// they captured; a `letrec`'s procedure, patched to capture itself.
#[test]
fn higher_order_code_and_closures() {
    let twice = "(define twice (subr pure ((subr pure (int) int) int) int) (lambda (f x) (f (f x))))\n\
                 (define inc (subr pure (int) int) (lambda (x) (+ x 1)))\n\
                 (define use (subr pure (int) int) (lambda (n) (twice inc n)))";
    let r = run(twice, "use", &[40], FUEL);
    assert_eq!(r.direct, Ok("42".into()), "{}", r.code);
    let adder = "(define add (subr pure (int) (subr pure (int) int)) (lambda (n) (lambda ((m int)) (+ n m))))\n\
                 (define use (subr pure (int) int) (lambda (k) ((add k) 10)))";
    let r = run(adder, "use", &[32], FUEL);
    assert_eq!(r.direct, Ok("42".into()), "{}", r.code);
    let r = run(&bench("loop"), "count", &[1000], FUEL);
    assert_eq!(r.direct, Ok(r.rust.clone()), "{}", r.code);
}

/// Closures made in a loop and passed to a higher-order `map`, which conses
/// the results: as the Rust machine gives, and collecting at every
/// safepoint, so that closures, their captured values and the lists move
/// while native frames and closures refer to them.
#[test]
fn closures_through_a_map_survive_collection() {
    let defs = format!(
        "{}\n(define main (subr (maxeff (read @l) (alloc @l) spin) (int) int) (lambda (k) (go k 0 (upto 100 nil))))",
        bench("closures")
    );
    for gc_every in [None, Some(1), Some(5)] {
        let r = run_collecting(&defs, "main", &[20], FUEL, gc_every);
        assert_eq!(r.direct, Ok(r.rust.clone()), "collecting every {gc_every:?}:\n{}", r.code);
    }
}

/// Lists made by call-outs to `cons`, and read, in a loop of calls: as the
/// Rust machine gives; and the same collecting at every safepoint, so that
/// every pair moves while native frames hold it, and the code, in the
/// heap's code area, must be kept alive by the call that runs it.
#[test]
fn lists_made_in_call_outs_survive_collection() {
    for gc_every in [None, Some(1), Some(7)] {
        let r = run_collecting(&bench("lists"), "rounds", &[30, 0], FUEL, gc_every);
        assert_eq!(r.direct, Ok(r.rust.clone()), "collecting every {gc_every:?}:\n{}", r.code);
        if let Some(n) = gc_every {
            assert!(r.collections >= 30 * 1000 / n, "{} collections", r.collections);
        }
        // The code lived through the run's collections, and is reclaimed
        // by the first one after, when nothing refers to it.
        let (after_run, after_collect) = r.code_words;
        assert!(after_run > 0 && after_collect == 0, "code-area words in use: {:?}", r.code_words);
    }
}

/// A runtime primitive that fails says why, as a trap.
#[test]
fn a_primitive_that_fails_says_why() {
    let defs = "(define q (subr pure (int int) int) (lambda (a b) (quotient a b)))";
    let r = run(defs, "q", &[7, 0], FUEL);
    assert!(matches!(&r.direct, Err(m) if m.contains("zero")), "{:?}\n{}", r.direct, r.code);
}

/// Code compiled, run and dropped, over and over, with collections between:
/// the code area holds only what is still referred to, however long it
/// goes on (the code area's own test, `fixpt-native/tests/code_gc.rs`, for
/// the native convention).
#[test]
fn code_compiled_and_dropped_is_reclaimed() {
    let text = format!("{}\ntak", bench("tak"));
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), &text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).map(|(f, _)| c.top(f).expect("checks")).collect();
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let mut m = DirectMachine::new().expect("maps");
    s.scheme.scope(|sc| {
        let w = sc.make(|h| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(h.heap(), &c, &text);
            comp.registers = true;
            comp.program(&tops).expect("compiles")
        });
        let none = sc.make(|_| Value::NULL);
        let h = sc.call_global("%run-word", &[w, none]).expect("defines");
        let mut closure = Value::NULL;
        sc.make(|m| {
            closure = m.get(h);
            closure
        });
        let rt = sc.runtime_unrooted();
        let root = rt.heap.push_root(closure);
        let mut most = 0;
        for round in 0..5000 {
            // The closure, from its root: a collection may have moved it.
            let closure = rt.heap.root_at(root);
            let p = m.compile(&mut rt.heap, closure).expect("compiles")[0].1;
            let args = [Value::fixnum(12), Value::fixnum(8), Value::fixnum(4)];
            assert_eq!(m.call(rt, p, &args, FUEL).map(|v| v.as_fixnum()), Ok(5), "round {round}");
            if round % 16 == 15 {
                rt.heap.collect(&mut []);
                most = most.max(rt.heap.code_words().1);
            }
        }
        // Sixteen compiles' worth, and room to spare: not five thousand.
        let closure = rt.heap.root_at(root);
        let p = m.compile(&mut rt.heap, closure).expect("compiles")[0].1;
        let one = rt.heap.bloblet_head(p.code).bytes / 8;
        assert!(most < 64 * (one + 2), "the code area spans {most} words; one compile is {one}");
    });
}

thread_local! {
    static MACHINE: std::cell::RefCell<DirectMachine> = std::cell::RefCell::new(DirectMachine::new().expect("maps"));
}

fn run_native(rt: &mut fixpt_runtime::Runtime, closure: Value, fuel: u64) -> fixpt_fx26::session::NativeRun {
    use fixpt_fx26::session::NativeRun;
    MACHINE.with(|m| {
        let mut m = m.borrow_mut();
        match m.compile(&mut rt.heap, closure) {
            Err(why) => NativeRun::Declined(why),
            Ok(procs) => NativeRun::Ran(m.call(rt, procs[0].1, &[], fuel).map(|v| fixpt_runtime::write_value(&rt.heap, v)).map_err(|t| t.what)),
        }
    })
}

/// Every test program, form by form as the REPL runs them (each form after
/// the definitions before it), with each expression compiled in the native
/// convention and run as machine code: the same values and errors as the
/// same forms run as cellular code. What the compiler declines runs as
/// cellular code; how many were, and why, is reported.
#[test]
#[ignore = "a report, minutes long (two fresh REPL sessions a program): cargo test --release -p fixpt-fx26 --test direct -- --ignored --nocapture"]
fn every_test_program_runs_natively_as_cellular() {
    use fixpt_fx26::session::Strategy;
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let (mut report, mut native, mut declined) = (Vec::new(), 0, Vec::new());
    let forms_of = |text: &str, runner: Option<fixpt_fx26::session::NativeRunner>| {
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        s.strategy = Strategy::Cellular;
        s.native_runner = runner;
        let forms = s.checker.read_in(FileId(0), text).ok()?;
        Some(s.run_forms(&forms).ok()?.into_iter().map(|o| o.map(|o| (o.value, o.printed))).collect::<Vec<_>>())
    };
    for sub in ["bidirectional", "bloblet", "control", "run", "pldi89", "datum", "recursive", "generative", "sizes"] {
        let mut paths: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|p| p.unwrap().path()).collect();
        paths.sort();
        for path in paths {
            let text = std::fs::read_to_string(&path).unwrap();
            let (Some(want), Some(got)) = (forms_of(&text, None), forms_of(&text, Some(run_native))) else { continue };
            for (i, (w, g)) in want.iter().zip(&got).enumerate() {
                let (Ok((w, _)), Ok((g, printed))) = (w, g) else { continue };
                if printed.contains("not in the native convention yet") {
                    declined.push(format!("{}: {}", path.display(), printed.trim()));
                } else if g.as_ref().is_ok_and(|v| v.is_some()) || g.is_err() {
                    native += 1;
                }
                // The same error, said as each machine says it.
                let same_error = matches!((w, g), (Err(a), Err(b)) if a.contains(b.as_str()) || b.contains(a.as_str()));
                if w != g && !same_error {
                    report.push(format!("{} form {i}: native {g:?}, cellular {w:?}", path.display()));
                }
            }
        }
    }
    eprintln!("{native} expressions ran as machine code; {} declined:\n{}", declined.len(), declined.join("\n"));
    assert!(report.is_empty(), "{}", report.join("\n"));
    assert!(native >= 40, "only {native}");
}
