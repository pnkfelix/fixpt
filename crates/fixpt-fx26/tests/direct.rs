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
    /// Major and minor collections the run made.
    collections: (u64, u64),
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
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).flat_map(|(f, _)| c.top_all(f).expect("checks")).collect();
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
            Err(e) => return Ran { direct: Err(format!("declined: {e}")), rust, code: String::new(), collections: (0, 0), code_words: (0, 0) },
        };
        let p = procs[0].1;
        let code: String = m.instructions(&rt.heap, p).iter().enumerate().map(|(i, w)| disassemble(*w, i as i64) + "\n").collect();
        if std::env::var("DIRECT_SHOW").is_ok() {
            eprintln!("{code}");
        }
        // Compiled only, not run (`show_code`: its arguments are made up).
        if std::env::var("SHOW_FILE").is_ok() {
            return Ran { direct: Err("not run".into()), rust, code, collections: (0, 0), code_words: (0, 0) };
        }
        let vals: Vec<Value> = args.iter().map(|a| Value::fixnum(*a)).collect();
        let before = (rt.heap.gc_count, rt.heap.minor_count);
        let direct = m.call(rt, p, &vals, fuel).map(|v| fixpt_runtime::write_value(&rt.heap, v)).map_err(|DirectTrap { what, .. }| what);
        let collections = (rt.heap.gc_count - before.0, rt.heap.minor_count - before.1);
        let after_run = rt.heap.code_words().0;
        rt.heap.collect(&mut []);
        Ran { direct, rust, code, collections, code_words: (after_run, rt.heap.code_words().0) }
    })
}

fn on_rust_machine(text: &str) -> String {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).flat_map(|(f, _)| c.top_all(f).expect("checks")).collect();
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
    program(&format!("bench/{name}"))
}

/// A test program's definitions: everything but its last line, the call.
fn program(name: &str) -> String {
    let text = std::fs::read_to_string(format!("{}/tests/programs/{name}.fx", env!("CARGO_MANIFEST_DIR"))).unwrap();
    // The definitions: everything but the last line, the call.
    let lines: Vec<&str> = text.trim_end().lines().collect();
    lines[..lines.len() - 1].join("\n")
}

/// The identity on ints is two instructions: nothing to check, no frame.
#[test]
fn the_identity_is_a_move_and_a_return() {
    let r = run("(define* id (subr pure (int) int) (lambda (x) x))", "id", &[42], FUEL);
    assert_eq!(r.direct, Ok("42".into()));
    assert_eq!(r.rust, "42");
    assert_eq!(r.code, "mov x0, x1\nret\n");
}

/// Adding one is one instruction, with its checks: that the operand is a
/// fixnum, and of overflow; either goes out of the way, to a bignum.
#[test]
fn adding_one_checks_its_operand_and_overflow() {
    let r = run("(define* inc (subr pure (int) int) (lambda (x) (+ x 1)))", "inc", &[41], FUEL);
    assert_eq!(r.direct, Ok("42".into()));
    assert!(r.code.starts_with("tst x1, #0x7\nb.ne @5\nadds x0, x1, #8\nb.vs @5\nret\n"), "{}", r.code);
    let r = run("(define* inc (subr pure (int) int) (lambda (x) (+ x 1)))", "inc", &[(1 << 60) - 1], FUEL);
    assert_eq!((r.direct, r.rust.as_str()), (Ok("1152921504606846976".into()), "1152921504606846976"));
    let r = run("(define* acc (subr pure (int int) int) (lambda (x y) (- x (- y x))))", "acc", &[-(1 << 60), (1 << 59)], FUEL);
    assert_eq!(r.direct, Ok(r.rust.clone()));
}

/// A report: a procedure's native code, `helpers`' `run` unless
/// `SHOW_FILE` (a program's path, its definitions all but the last line)
/// and `SHOW_NAME` say. `cargo test --release -p fixpt-fx26 --test direct
/// -- --ignored show_code --nocapture`.
#[test]
#[ignore = "a report"]
fn show_code() {
    let defs = match std::env::var("SHOW_FILE") {
        Ok(f) => {
            let text = std::fs::read_to_string(f).expect("reads");
            let lines: Vec<&str> = text.trim_end().lines().collect();
            lines[..lines.len() - 1].join("\n")
        }
        Err(_) => bench("helpers"),
    };
    let name = std::env::var("SHOW_NAME").unwrap_or_else(|_| "run".into());
    println!("{}", direct_only(&defs, &name, &[0, 30, 0], FUEL).code);
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
    let defs = "(define* add3 (subr pure (int int int) int) (lambda (a b c) (+ a (+ b c))))\n\
                (define* f (subr pure (int) int) (lambda (n) (add3 n (+ n 1) (+ n 2))))";
    let r = run(defs, "f", &[10], FUEL);
    assert_eq!(r.direct, Ok("33".into()), "{}", r.code);
    assert_eq!(r.rust, "33");
}

/// Running out of fuel, and of stack, are traps, as on the other machines.
#[test]
fn fuel_and_stack_run_out() {
    let forever = "(define* forever (subr spin (int) int) (lambda (n) (forever (+ n 1))))";
    assert_eq!(direct_only(forever, "forever", &[0], 100_000).direct, Err("out of fuel".into()));
    let deep = "(define* deep (subr spin (int) int) (lambda (n) (+ 1 (deep n))))";
    assert_eq!(run(deep, "deep", &[0], FUEL).direct, Err("stack overflow".into()));
}

/// Higher-order code: a global's procedure passed as a value and called
/// through its native closure; closures made as the code runs, reading what
/// they captured; a `letrec`'s procedure, patched to capture itself.
#[test]
fn higher_order_code_and_closures() {
    let twice = "(define* twice (subr pure ((subr pure (int) int) int) int) (lambda (f x) (f (f x))))\n\
                 (define* inc (subr pure (int) int) (lambda (x) (+ x 1)))\n\
                 (define* use (subr pure (int) int) (lambda (n) (twice inc n)))";
    let r = run(twice, "use", &[40], FUEL);
    assert_eq!(r.direct, Ok("42".into()), "{}", r.code);
    let adder = "(define* add (subr pure (int) (subr pure (int) int)) (lambda (n) (lambda ((m int)) (+ n m))))\n\
                 (define* use (subr pure (int) int) (lambda (k) ((add k) 10)))";
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
        "{}\n(define* main (subr (maxeff (read @l) (alloc @l) spin) (int) int) (lambda (k) (go k 0 (upto 100 nil))))",
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
            assert!(r.collections.0 + r.collections.1 >= 30 * 1000 / n, "{:?} collections", r.collections);
        }
        // The code lived through the run's collections, and is reclaimed
        // by the first one after, when nothing refers to it.
        let (after_run, after_collect) = r.code_words;
        assert!(after_run > 0 && after_collect == 0, "code-area words in use: {:?}", r.code_words);
    }
    // With no policy, a run that fills the nursery several times collects
    // it alone each time: its call-outs make the collection that is due,
    // not a major one (they did, and `paraffins` took 57 s, not 10).
    let r = run_collecting(&bench("lists"), "rounds", &[3000, 0], FUEL, None);
    assert_eq!(r.direct, Ok(r.rust.clone()));
    assert!(r.collections.1 >= 3 && r.collections.0 == 0, "(major, minor) collections: {:?}", r.collections);
}

/// A runtime primitive that fails says why, as a trap.
#[test]
fn a_primitive_that_fails_says_why() {
    let defs = "(define* q (subr pure (int int) int) (lambda (a b) (quotient a b)))";
    let r = run(defs, "q", &[7, 0], FUEL);
    assert!(matches!(&r.direct, Err(m) if m.contains("zero")), "{:?}\n{}", r.direct, r.code);
}

/// The fixed-width integers' operations (`prim1`, `prim2`, `prim2imm`), in
/// line where they can be and called with no collection where not, on every
/// type's edge values, bignums among them, as the Rust machine gives them
/// (`programs/native/fixed-width-ops.fx`); and so under collections, which
/// the bignums the calls make must live through.
#[test]
fn fixed_width_operations_as_the_rust_machine_gives_them() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/fixed-width-ops"), "fixed-width-ops", &[0], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
    }
}

/// `i64` and `u64` raw in registers (`programs/native/raw-64.fx`): a loop's
/// variable raw around it; one live across a call, boxed into the frame and
/// unboxed again; ways meeting raw and boxed; bignums boxed on the way out;
/// under collections too. Division by zero fails; `T->int` past a fixnum is
/// a bignum.
#[test]
fn i64_and_u64_raw_in_registers() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/raw-64"), "raw-64", &[1000], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
    }
    let defs = "(define* q (subr pure (int int) int) (lambda (a b) (u64->int (u64-quotient (int->u64 a) (int->u64 b)))))";
    assert!(matches!(&run(defs, "q", &[7, 0], FUEL).direct, Err(m) if m.contains("zero")));
    let defs = "(define* w (subr pure (int) int) (lambda (a) (i64->int (i64* (int->i64 a) (int->i64 a)))))";
    assert_eq!(run(defs, "w", &[1 << 31], FUEL).direct, Ok("4611686018427387904".into()));
}

/// `f64` natively (`programs/native/floats.fx`): raw in registers around a
/// loop, boxed into the frame across a call, raw and boxed ways meeting,
/// IEEE's special values, and the runtime's operations beside the
/// machine's; as the Rust machine gives them, collecting often too, since
/// boxes are made where registers hold values.
#[test]
fn floats_as_the_rust_machine_gives_them() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/floats"), "floats", &[1000], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
    }
    // Flat arrays, of floats and of integers, natively.
    for (p, f) in [("run/flat-arrays", "flat"), ("native/flat-ints", "flat-ints")] {
        let r = run_collecting(&program(p), f, &[100], FUEL, Some(7));
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "{p}: {:?} against {}", r.direct, r.rust);
    }
    let defs = "(define* at (subr (alloc @heap) (int) f64) (lambda (i) (flatarray-ref (make-flatarray (f64-flat) 3 1.) i)))";
    assert!(matches!(&run(defs, "at", &[3], FUEL).direct, Err(m) if m.contains("out of range")));
    // `f32`, immediates, in line (`programs/run/f32.fx`).
    let r = run(&program("run/f32"), "f32s", &[1000], FUEL);
    assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "{:?} against {}", r.direct, r.rust);
}

/// Identity (PLAN.md Q5, `programs/native/identity.fx`): `pair-eq?` and
/// kin in line, and a union-find whose roots are found by it, as the Rust
/// machine gives them, and with its nodes moved by collections; and tables
/// keyed by identity (`programs/native/eqtables.fx`).
#[test]
fn identity_as_the_rust_machine_gives_it() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/identity"), "identity", &[300], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
        // Tables keyed by identity, their keys moved between operations.
        let r = run_collecting(&program("native/eqtables"), "eqtables", &[500], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
    }
}

/// The standard operations the ports wrote themselves (PLAN.md Q11,
/// `programs/native/standard-ops.fx`), as the Rust machine gives them;
/// `error` fails the run with its message; `append` of a cyclic list fails
/// rather than loops.
#[test]
fn standard_ops_as_the_rust_machine_gives_them() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/standard-ops"), "standard-ops", &[5], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
    }
    let defs = "(define* f (subr pure (int) int) (lambda (b) (if (zero? b) (error \"f: zero\") b)))";
    assert!(matches!(&run(defs, "f", &[0], FUEL).direct, Err(m) if m.contains("f: zero")));
    let defs = "(define* g (subr (maxeff (read @l) (write @l) (alloc @l)) (int) nat)\n  (lambda (n) (let ((xs (the (listof int @l) (list n 2))))\n    (begin (set-cdr! (cdr xs) xs) (list-length (append xs xs))))))";
    assert!(matches!(&run(defs, "g", &[1], FUEL).direct, Err(m) if m.contains("proper list")));
}

/// A leaf's registers and link, kept around a call with no collection: `b`
/// lives across a product past a fixnum, which the primitive makes.
#[test]
fn a_leaf_keeps_its_registers_around_a_primitive() {
    let defs = "(define* f (subr pure (int int) int)\n  (lambda (a b) (if (u64< (u64* (int->u64 a) (int->u64 b)) (int->u64 b)) a b)))";
    let r = run(defs, "f", &[-1, 5], FUEL);
    assert_eq!((r.direct, r.rust.as_str()), (Ok("5".into()), "5"), "{}", r.code);
    let defs = "(define* q (subr pure (int int) int) (lambda (a b) (u32->int (u32-quotient (int->u32 a) (int->u32 b)))))";
    assert!(matches!(&run(defs, "q", &[7, 0], FUEL).direct, Err(m) if m.contains("zero")));
}

/// An `int` is a bignum past a fixnum (PLAN.md, Q2), as native code makes
/// it: sums, products and quotients past one, `=` and `<` on bignums made
/// apart, back to fixnums, and the 64-bit types' conversions
/// (`programs/run/bignums.fx`); as the Rust machine does, collecting often
/// too, since the bignums are made where registers hold values.
#[test]
fn ints_are_bignums_natively() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("run/bignums"), "bignums", &[0], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
    }
    let defs = "(define* q (subr pure (int int) int) (lambda (a b) (quotient a b)))";
    assert_eq!(run(defs, "q", &[-(1 << 60), -1], FUEL).direct, Ok("1152921504606846976".into()));
}

/// An array's element, by `field@`: inline in range, and out of range
/// the call-out says so, as the Rust machine does.
#[test]
fn array_elements_in_and_out_of_range() {
    let defs = "(define a (arrayof int @a) (make-array 10 7))\n(define* at (subr (read @a) (int) int) (lambda (i) (array-ref a i)))";
    let r = run(defs, "at", &[9], FUEL);
    assert_eq!(r.direct, Ok("7".into()), "{}", r.code);
    let r = run(defs, "at", &[10], FUEL);
    assert!(matches!(&r.direct, Err(m) if m.contains("field")), "{:?} (the Rust machine: {})\n{}", r.direct, r.rust, r.code);
}

/// A pair written, by the runtime's `set-car!`, called out.
#[test]
fn a_pair_written() {
    let r = run(&program("run/letfreeze"), "frozen-list", &[10], FUEL);
    assert_eq!(r.direct, Ok("(10 2 3)".into()), "{}", r.code);
    assert_eq!(r.rust, "(10 2 3)");
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
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).flat_map(|(f, _)| c.top_all(f).expect("checks")).collect();
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

fn run_native(rt: &mut fixpt_runtime::Runtime, closure: Value, fuel: u64) -> fixpt_fx26::session::NativeRun {
    use fixpt_fx26::session::NativeRun;
    fixpt_native::direct::with_machine(|m| match m.compile(&mut rt.heap, closure) {
        Err(why) => NativeRun::Declined(why),
        Ok(procs) => NativeRun::Ran(m.call(rt, procs[0].1, &[], fuel).map_err(|t| t.what)),
    })
    .unwrap_or_else(|e| NativeRun::Ran(Err(e)))
}

/// Native code and cellular code calling each other, as the REPL runs
/// what the native compiler declines (here, by `stay-cellular`, which it
/// always declines) as cellular code: cellular code
/// calling a native closure, native code a cellular one, and a whole
/// continuation cellular code took thrown from native code
/// (`programs/native/mixed.fx`); and the same collecting often.
#[test]
fn native_and_cellular_code_call_each_other() {
    use fixpt_fx26::session::Strategy;
    for gc_every in [500] {
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        s.strategy = Strategy::Cellular;
        s.native_runner = Some(run_native);
        s.native_compiler = Some(fixpt_native::direct::compile_closure);
        s.register_code = true;
        s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
        s.scheme.runtime_unrooted().heap.gc_every = gc_every;
        let forms = s.checker.read_in(FileId(0), include_str!("programs/native/mixed.fx")).expect("reads");
        let out: Vec<String> =
            s.run_forms(&forms).expect("runs").into_iter().map(|o| o.map_or_else(|e| e.message, |o| format!("{}{:?}", o.printed, o.value))).collect();
        // Native: `bump`, which stays cellular, is neither inlined nor
        // specialized into its callers, so they stay native.
        assert!(out[4].ends_with("Ok(Some(\"5150\"))") && !out[4].contains("run as cellular code"), "{out:?}");
        assert!(out[5].ends_with("Ok(Some(\"42\"))"), "{out:?}");
    }
}

/// A session running forms as the REPL does, compiled; in the native
/// convention if `native`, its forms then compiled natively; with native
/// code callable from cellular code, and adapters between conventions.
fn session(native: bool) -> Fx26Session {
    use fixpt_fx26::session::Strategy;
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    s.strategy = Strategy::Cellular;
    s.set_native_convention(native);
    if native {
        s.native_runner = Some(run_native);
        s.native_compiler = Some(fixpt_native::direct::compile_closure);
        s.register_code = true;
    }
    s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
    s.scheme.runtime_unrooted().adapt = Some(fixpt_native::direct::adapt);
    s
}

/// A form run early, as the REPL does while it is typed, reads the globals
/// the forms before it defined, where this session's strategy put them: not
/// the lowered program's, which compiled sessions never fill. Then runs for
/// real to the same value.
#[test]
fn speculation_reads_compiled_globals() {
    use fixpt_fx26::session::Speculation;
    for native in [false, true] {
        let mut s = session(native);
        let defs = "(define-type t (sumof (x int) (y int)))\n(define x (sum x 3))";
        let forms = s.checker.read_in(FileId(0), defs).expect("reads");
        values_of(&mut s, &forms);
        let e = "((lambda ((f (subr (read (globals x)) (t) t))) (f (sum y 4))) (lambda ((y t)) x))";
        let form = s.checker.read_in(FileId(0), e).expect("reads").remove(0);
        let early = s.speculate(&form);
        assert!(matches!(&early, Speculation::Value(_)), "native {native}: {early:?}");
        let ran = values_of(&mut s, &[form]);
        assert_eq!(early, Speculation::Value(ran[0].clone()), "native {native}");
    }
}

/// Types that name each other run in a compiled session as in a file: the
/// pieces written in FX-26 are given them together.
#[test]
fn types_naming_each_other_run_compiled() {
    let mut s = session(true);
    let forms = s.checker.read_in(FileId(0), include_str!("programs/recursive/types-in-any-order.fx")).expect("reads");
    let out = values_of(&mut s, &forms);
    assert!(out.last().is_some_and(|v| v.starts_with("(#<sum some>)")), "{out:?}");
}

/// At the REPL, a datatype naming one not defined yet waits for it, and runs
/// with the entry that defines it; lowered, and compiled natively.
#[test]
fn an_entry_waits_for_the_types_it_names() {
    use fixpt_fx26::session::{Consider, Fx26Session as S};
    let entry = |s: &mut S, text: &str| s.checker.read_in(FileId(0), text).expect("reads");
    for native in [None, Some(true)] {
        let mut s = match native {
            None => Fx26Session::with_backend(Backend::Bytecode).expect("starts"),
            Some(n) => session(n),
        };
        let tree = entry(&mut s, "(define-datatype tree (leaf int) (node forest))");
        assert_eq!(s.consider(&tree), Consider::Pends(vec!["forest".into()]));
        s.hold(&tree);
        assert_eq!(s.awaiting(), ["forest"]);
        // Something unrelated runs as ever, and leaves it waiting.
        let other = entry(&mut s, "(define-type n int)");
        assert_eq!(s.consider(&other), Consider::Run);
        let forest = entry(&mut s, "(define-datatype forest (fnil) (fcons tree forest))");
        assert_eq!(s.consider(&forest), Consider::Completes(vec!["tree".into(), "leaf".into(), "node".into()]));
        for o in s.complete(&forest).expect("runs") {
            assert!(o.as_ref().is_ok_and(|o| o.value.is_ok()), "{:?}", o.err().map(|e| e.message));
        }
        assert!(s.pending.is_empty());
        let use_it = entry(&mut s, "(node (fcons (leaf 1) (fnil)))");
        assert_eq!(values_of(&mut s, &use_it), ["#<sum node>"], "native {native:?}");
    }
}

/// The values `forms` give, run in `s` (a failure as `error: …`).
fn values_of(s: &mut Fx26Session, forms: &[fixpt_read::Syntax]) -> Vec<String> {
    s.run_forms(forms)
        .expect("runs")
        .into_iter()
        .filter_map(|o| match o {
            Ok(o) => o.value.transpose().map(|v| v.unwrap_or_else(|e| format!("error: {e}"))),
            Err(e) => Some(format!("error: {}", e.message)),
        })
        .collect()
}

/// Each form's value, as `values_of` gives them, and the names of the
/// definitions that ran as cellular code, not native code, in order.
fn values_and_fallbacks(s: &mut Fx26Session, forms: &[fixpt_read::Syntax]) -> (Vec<String>, Vec<String>) {
    let mut fell = Vec::new();
    let mut values = Vec::new();
    for o in s.run_forms(forms).expect("runs") {
        match o {
            Ok(o) => {
                for line in o.printed.lines().filter(|l| l.contains("not in the native convention")) {
                    if let Some(name) = line.split('`').nth(1).filter(|_| line.contains("so `")) {
                        fell.push(name.to_string());
                    }
                }
                values.extend(o.value.transpose().map(|v| v.unwrap_or_else(|e| format!("error: {e}"))));
            }
            Err(e) => values.push(format!("error: {}", e.message)),
        }
    }
    (values, fell)
}

/// Conversions between the conventions make adapters, and native and
/// cellular code call each other through them, nested hundreds deep:
/// with each convention the program's, as the REPL runs each form, the
/// native one's forms compiled natively; the deepest collecting often
/// (`programs/native/adapters.fx`). One native session serves the tests
/// that follow too, `native_session_*`: each loads the front end.
fn adapters_in(s: &mut Fx26Session) -> Vec<String> {
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/adapters.fx")).expect("reads");
    // The last form, the deepest, collecting often.
    let (most, last) = forms.split_at(forms.len() - 1);
    let mut out = values_of(s, most);
    s.scheme.runtime_unrooted().heap.gc_every = 50;
    out.extend(values_of(s, last));
    s.scheme.runtime_unrooted().heap.gc_every = 0;
    out
}

const ADAPTED: [&str; 12] = ["2", "2", "2", "2", "6", "7", "12", "22", "15", "(7 7)", "(3 2 1)", "300"];

#[test]
fn conversions_make_adapters_in_cellular_code() {
    assert_eq!(adapters_in(&mut session(false)), ADAPTED);
}

/// In one native session: conversions (as above); an `extract` inlined
/// from an earlier form (`programs/native/inlined-extract.fx`), whose caller
/// keeps its register code; aborts across machines
/// (`programs/native/aborts.fx`): from native code to a prompt cellular
/// code installed, and from cellular code to one native code installed,
/// the abort going on from one machine to the other where it finds no
/// prompt, and under a deep native stack, which the search no longer walks
/// whole; more values than registers, the rest a list in the last one
/// (`programs/native/many-values.fx`); and a frame's stack map (`docs/research/generational-gc.md`): a
/// large array in a slot dead across a call that collects is not copied
/// by those collections; kept live across it, it is, each time
/// (`programs/native/dead-slot.fx`); a frame too wide for its map
/// (`programs/native/wide-frame.fx`); and recursion a million deep
/// (`programs/native/deep.fx`).
#[test]
fn native_session_adapters_aborts_and_stack_maps() {
    let mut s = session(true);
    assert_eq!(adapters_in(&mut s), ADAPTED, "adapters");
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/aborts.fx")).expect("reads");
    let (values, fell) = values_and_fallbacks(&mut s, &forms);
    assert_eq!(values, ["15", "105", "400200"], "aborts");
    assert_eq!(fell, ["in-cellular", "raise-cellular"], "only those that stay cellular do");
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/inlined-extract.fx")).expect("reads");
    for o in s.run_forms(&forms).expect("runs") {
        let o = o.expect("ran");
        assert!(!o.printed.contains("not in the native convention"), "{}", o.printed);
        if let Some(v) = o.value.transpose() {
            assert_eq!(v.as_deref(), Ok("3000"));
        }
    }
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/dead-slot.fx")).expect("reads");
    let (defs, runs) = forms.split_at(forms.len() - 2);
    for o in s.run_forms(defs).expect("runs") {
        assert!(o.is_ok_and(|o| !o.printed.contains("not in the native convention")), "defined natively");
    }
    // Collecting often while the native code runs (not while the front end
    // compiles it): how many collections, and how many words they copied.
    s.native_runner = Some(run_native_collecting);
    let mut seen = Vec::new();
    for form in runs {
        // Major collections, and the words they copied (minor ones copy
        // only the young, and the array is old).
        let heap = |s: &mut Fx26Session| {
            let h = &s.scheme.runtime_unrooted().heap;
            (h.gc_count, h.words_copied - h.minor_words_copied)
        };
        let before = heap(&mut s);
        let out = s.run_forms(std::slice::from_ref(form)).expect("runs").remove(0).expect("ran");
        assert!(!out.printed.contains("not in the native convention"), "{}", out.printed);
        let after = heap(&mut s);
        seen.push((after.0 - before.0, after.1 - before.1));
    }
    // About as many major collections each (three policy collections in
    // four are minor, and the array, old, is not copied by those); each of
    // `keep`'s copies the array, 100 000 words, and `drop`'s do not: per
    // collection, since each copies the whole live heap besides.
    let ((n0, c0), (n1, c1)) = (seen[0], seen[1]);
    assert!(n0 >= 5 && n0.abs_diff(n1) <= 1, "{seen:?}");
    assert!(c1 / n1 > c0 / n0 + 80_000, "{seen:?}");
    // A frame of 70 slots, past what a header's mask holds: traced whole,
    // under those collections (`programs/native/wide-frame.fx`).
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/wide-frame.fx")).expect("reads");
    assert_eq!(values_of(&mut s, &forms), ["2485", "37450000"], "wide frame");
    // More values than registers, the rest a list in the last register, under
    // those collections too.
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/many-values.fx")).expect("reads");
    let (values, fell) = values_and_fallbacks(&mut s, &forms);
    assert_eq!(values, ["25", "1012", "-154", "119", "1025", "1001"], "many values");
    assert_eq!(fell, ["cell10", "from-cell"], "only those that stay cellular do");
    // `rcons` made inline, in regions' chunks, under those collections too.
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/region-cons.fx")).expect("reads");
    assert_eq!(values_and_fallbacks(&mut s, &forms), (vec!["500100000".to_string()], vec![]), "region-cons");
    // Deep recursion, under those collections too.
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/deep.fx")).expect("reads");
    assert_eq!(values_and_fallbacks(&mut s, &forms), (vec!["500000500000".to_string()], vec![]), "deep");
    // Variadic procedures, the count in a register, under those collections
    // too: none left as cellular code.
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/variadic.fx")).expect("reads");
    let (values, fell) = values_and_fallbacks(&mut s, &forms);
    assert_eq!((values, fell), (vec!["60".into(), "1019".into(), "4140000".into()], vec![]), "variadic");
    // `list`, called and as a value, likewise.
    let forms = s.checker.read_in(FileId(0), include_str!("programs/run/list.fx")).expect("reads");
    assert_eq!(values_and_fallbacks(&mut s, &forms), (vec!["5539".to_string()], vec![]), "list");
    let forms = s.checker.read_in(FileId(0), include_str!("programs/run/list-regions.fx")).expect("reads");
    assert_eq!(values_and_fallbacks(&mut s, &forms).0.last().map(String::as_str), Some("54"), "list-regions");
    // `apply` copies a list that may be written (F11), and a cyclic one is an
    // error, as machine code too.
    let forms = s.checker.read_in(FileId(0), include_str!("programs/run/apply-fresh.fx")).expect("reads");
    assert_eq!(values_and_fallbacks(&mut s, &forms).0.last().map(String::as_str), Some("22"), "apply-fresh");
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/apply-cyclic.fx")).expect("reads");
    let values = values_of(&mut s, &forms);
    assert!(values.last().is_some_and(|v| v.contains("expected a list")), "{values:?}");
}

/// `run_native`, collecting every 97 safepoints while the native code runs
/// (not while the front end compiles it).
fn run_native_collecting(rt: &mut fixpt_runtime::Runtime, closure: Value, fuel: u64) -> fixpt_fx26::session::NativeRun {
    let was = std::mem::replace(&mut rt.heap.gc_every, 97);
    let r = run_native(rt, closure, fuel);
    rt.heap.gc_every = was;
    r
}

/// Control on native frames (`docs/research/native-conventions.md`, step
/// 5): prompts and aborts, whole and composable continuations taken and
/// given values, throws out of regions, and marks, each program's last
/// form run as machine code, not declined, collecting often as it runs, so
/// that frames and taken continuations move.
#[test]
fn control_on_native_frames() {
    use fixpt_fx26::session::Strategy;
    let programs = [
        ("bidirectional/capture-and-resume", "4"),
        ("bidirectional/cwcc", "1"),
        ("bidirectional/own-abort", "5"),
        ("run/region-escapes", "500500"),
        ("run/region-throws", "500500"),
        ("pldi89/c7", "(#<continuation> . #<continuation>)"),
        ("bench/captures", "420000"),
        ("run/marks-of", "(7)"),
        ("control/private-mark", "1"),
        ("control/frames-hold-private-state", "13"),
        ("run/tail-marks", "(1 2)"),
    ];
    // One session, loading the front end once: each program after the
    // ones before, as the REPL would run them, its names redefined.
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    s.strategy = Strategy::Cellular;
    s.native_runner = Some(run_native_collecting);
    s.native_compiler = Some(fixpt_native::direct::compile_closure);
    s.register_code = true;
    s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
    for (name, want) in programs {
        let text = std::fs::read_to_string(format!("{}/tests/programs/{name}.fx", env!("CARGO_MANIFEST_DIR"))).unwrap();
        let forms = s.checker.read_in(FileId(0), &text).expect("reads");
        let (last, before) = forms.split_last().expect("a form");
        s.run_forms(before).expect("runs");
        let out = s.run(last).expect("checks");
        assert!(!out.printed.contains("not in the native convention"), "{name}: {}", out.printed);
        assert_eq!(out.value.map(|v| v.unwrap_or_default()), Ok(want.to_string()), "{name}");
    }
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
        s.native_compiler = runner.map(|_| fixpt_native::direct::compile_closure as fixpt_fx26::session::NativeCompiler);
        // As the REPL has it: what the native compiler starts from.
        s.register_code = runner.is_some();
        s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
        s.scheme.runtime_unrooted().adapt = Some(fixpt_native::direct::adapt);
        let forms = s.checker.read_in(FileId(0), text).ok()?;
        Some(s.run_forms(&forms).ok()?.into_iter().map(|o| o.map(|o| (o.value, o.printed))).collect::<Vec<_>>())
    };
    // Every directory of programs but those that loop until a step limit
    // (`diverge`) and the benchmarks (long by design); what does not
    // check, or is not FX-26 forms, is skipped.
    let mut subs: Vec<String> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().file_name().to_string_lossy().into_owned()).filter(|d| d != "diverge" && d != "bench").collect();
    subs.sort();
    for sub in subs {
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
                // A procedure prints as the closure each makes, of either
                // kind, and perhaps an adapter: compared as a procedure.
                let procedure = |v: String| if v.starts_with("#<native-closure") || v.starts_with("#<cellular-closure") { "#<procedure>".into() } else { v };
                let kindless = |v: &Result<Option<String>, String>| v.clone().map(|v| v.map(procedure));
                if kindless(w) != kindless(g) && !same_error {
                    report.push(format!("{} form {i}: native {g:?}, cellular {w:?}", path.display()));
                }
            }
        }
    }
    eprintln!("{native} expressions ran as machine code; {} declined:\n{}", declined.len(), declined.join("\n"));
    assert!(report.is_empty(), "{}", report.join("\n"));
    assert!(native >= 40, "only {native}");
}

/// A call of a small global procedure is inlined in register code, behind a
/// guard that the global still holds the closure the body was compiled
/// from: redefined, the call calls the new one. So too a call specialized
/// at a lambda. As register code, and as machine code.
#[test]
fn inlined_calls_see_a_redefinition() {
    use fixpt_fx26::session::Strategy;
    for native in [false, true] {
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        s.strategy = Strategy::Cellular;
        s.register_code = true;
        if native {
            s.native_runner = Some(run_native);
            s.native_compiler = Some(fixpt_native::direct::compile_closure);
            s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
        } else {
            s.scheme.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_registers);
        }
        let forms = s.checker.read_in(FileId(0), include_str!("programs/redefine/compatible.fx")).expect("reads");
        let out: Vec<String> = s.run_forms(&forms).expect("runs").into_iter().map(|o| o.map_or_else(|e| e.message, |o| format!("{:?}", o.value))).collect();
        assert_eq!(out[2], "Ok(Some(\"4\"))", "native {native}: {out:?}");
        assert_eq!(s.inliners("f").expect("asks"), Ok(vec!["g".to_string()]), "native {native}");
        assert_eq!(out[4], "Ok(Some(\"202\"))", "native {native}: {out:?}");
        // A call specialized at a lambda, the same.
        let forms = s.checker.read_in(FileId(0), include_str!("programs/redefine/specialized.fx")).expect("reads");
        let out: Vec<String> = s.run_forms(&forms).expect("runs").into_iter().map(|o| o.map_or_else(|e| e.message, |o| format!("{:?}", o.value))).collect();
        assert_eq!((out[3].as_str(), out[5].as_str()), ("Ok(Some(\"36\"))", "Ok(Some(\"3036\"))"), "native {native}: {out:?}");
        assert_eq!(s.inliners("map1").expect("asks"), Ok(vec!["test".to_string()]), "native {native}");
    }
}
