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

/// A procedure that captures, or calls what it was given, is declined, and
/// so is one that calls it.
#[test]
fn higher_order_code_is_declined() {
    let twice = "(define twice (subr pure ((subr pure (int) int) int) int) (lambda (f x) (f (f x))))";
    let r = direct_only(twice, "twice", &[], FUEL);
    assert!(matches!(&r.direct, Err(e) if e.starts_with("declined")), "{:?}", r.direct);
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
    assert!(matches!(&r.direct, Err(m) if m.contains("quotient")), "{:?}\n{}", r.direct, r.code);
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

