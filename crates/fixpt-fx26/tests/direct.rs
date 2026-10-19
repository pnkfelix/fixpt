//! Code in the native convention (`docs/research/native-conventions.md`,
//! step 2; `fixpt_native::direct`): first-order procedures compiled from
//! their register code, called by `bl`, on native frames, give what the
//! Rust machine gives; what they cannot do they decline.
//!
//! Only where arm64 or x86_64 code runs: every test here runs some.
#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_fx26::Checker;
use fixpt_heap::Value;
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
    /// a collection then, when nothing refers to the code any more: past
    /// what was there before it was compiled (the adapters' code, which
    /// lives as the heap does, `Heap::adapter_code`, made as the
    /// definitions ran).
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
    Ran { rust, ..direct_in(defs, name, args, fuel, gc_every, None) }
}

/// The same without the Rust machine's run, on a stack cache of `stack.0`
/// words whose run may take `stack.1` in all.
fn direct_stack(defs: &str, name: &str, args: &[i64], fuel: u64, stack: (u64, u64)) -> Ran {
    direct_in(defs, name, args, fuel, None, Some(stack))
}

/// The same without the Rust machine's run: for what it would not finish.
fn direct_only(defs: &str, name: &str, args: &[i64], fuel: u64) -> Ran {
    direct_in(defs, name, args, fuel, None, None)
}

fn direct_in(defs: &str, name: &str, args: &[i64], fuel: u64, gc_every: Option<u64>, stack: Option<(u64, u64)>) -> Ran {
    let rust = String::new();
    let text = format!("{defs}\n{name}");
    // Run natively, so typed so: its calls compiled as their types say.
    let mut c = Checker::with_convention(fixpt_fx26::ast::Conv::Native);
    let forms = c.read_in(FileId(0), &text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).flat_map(|(f, _)| c.top_all(f).expect("checks")).collect();
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    // What the definitions make, run as cellular code, is native (`nclosure`).
    s.scheme.runtime_unrooted().adapt = Some(fixpt_native::direct::adapt);
    let mut m = DirectMachine::new().expect("maps");
    if let Some((cache, max)) = stack {
        m.set_stack_words(cache, max);
    }
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
        let kept = rt.heap.code_words().0;
        let procs = match m.compile(&mut rt.heap, closure) {
            Ok(p) => p,
            Err(e) => return Ran { direct: Err(format!("declined: {e}")), rust, code: String::new(), collections: (0, 0), code_words: (0, 0) },
        };
        let p = procs[0].1;
        let code = code_of(&m, &rt.heap, p);
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
        let after_run = rt.heap.code_words().0 - kept;
        rt.heap.collect(&mut []);
        Ran { direct, rust, code, collections, code_words: (after_run, rt.heap.code_words().0 - kept) }
    })
}

/// A procedure's own instructions, one to a line, as the disassembler
/// reads them: arm64's, or x86_64's, a branch's target `@byte`.
fn code_of(m: &DirectMachine, heap: &fixpt_heap::Heap, p: fixpt_native::direct::Compiled) -> String {
    if cfg!(target_arch = "x86_64") {
        let bytes = &heap.bloblet_bytes(p.code)[..p.len];
        let mut at = 0;
        let mut out = String::new();
        while at < bytes.len() {
            let (text, n) = fixpt_native::x86_64::disasm::disassemble(bytes, at);
            out.push_str(&text);
            out.push('\n');
            at += n;
        }
        return out;
    }
    m.instructions(heap, p).iter().enumerate().map(|(i, w)| fixpt_native::arm64::disasm::disassemble(*w, i as i64) + "\n").collect()
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
    assert_eq!(r.code, if cfg!(target_arch = "x86_64") { "mov rax, rdi\nret\n" } else { "mov x0, x1\nret\n" });
}

/// Adding one is one instruction, with its checks: that the operand is a
/// fixnum, and of overflow; either goes out of the way, to a bignum.
#[test]
fn adding_one_checks_its_operand_and_overflow() {
    let r = run("(define* inc (subr pure (int) int) (lambda (x) (+ x 1)))", "inc", &[41], FUEL);
    assert_eq!(r.direct, Ok("42".into()));
    let want = if cfg!(target_arch = "x86_64") { "test edi, 7\njne @" } else { "tst x1, #0x7\nb.ne @5\nadds x0, x1, #8\nb.vs @5\nret\n" };
    assert!(r.code.starts_with(want), "{}", r.code);
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
    assert_eq!(direct_only(forever, "forever", &[0], 100_000).direct, Err("evaluation step limit exceeded".into()));
    // Past the most a run's frames may take, with the stack cache's chain:
    // here 2^20 words, through a cache of 4096.
    let deep = "(define* deep (subr spin (int) int) (lambda (n) (+ 1 (deep n))))";
    assert_eq!(direct_stack(deep, "deep", &[0], FUEL, (4096, 1 << 20)).direct, Err("stack overflow".into()));
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

/// `i8` and `u8` (`TODO.md` §84), in line as `i32` and `u32` are, wrapped
/// to a byte (`programs/native/small-width-ops.fx`), as the Rust machine
/// gives them.
#[test]
fn byte_width_operations_as_the_rust_machine_gives_them() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/small-width-ops"), "small-width-ops", &[0], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
    }
}

/// A bytevector's bytes and length read, and its bytes written, in line
/// (`TODO.md` §84,
/// `programs/native/bytevector-sum.fx`), as the Rust machine gives them,
/// collecting often too; and a read past the end refused as the
/// primitive refuses it.
#[test]
fn bytevector_reads_in_line() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/bytevector-sum"), "bytevector-sum", &[1000], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
    }
    let defs = "(define* past (subr (maxeff (alloc @b) (read @b)) (int) int) (lambda (i) (bytevector-u8-ref (the (bytevectorof @b) (make-bytevector 3 (int->u8 1))) i)))";
    for i in [3, -1] {
        let r = run(defs, "past", &[i], FUEL);
        assert!(matches!(&r.direct, Err(m) if m.contains("out of range")), "{i}: {:?}", r.direct);
    }
    // And a write, in line too, refused alike.
    let defs = "(define* put (subr (maxeff (alloc @b) (write @b)) (int) unit) (lambda (i) (bytevector-u8-set! (the (bytevectorof @b) (make-bytevector 3 (int->u8 1))) i (int->u8 2))))";
    for i in [3, -1] {
        let r = run(defs, "put", &[i], FUEL);
        assert!(matches!(&r.direct, Err(m) if m.contains("out of range")), "{i}: {:?}", r.direct);
    }
}

/// Mutable bloblets made and written in line (`TODO.md` §57,
/// `programs/native/bloblet-tree.fx`): a tree built, its leaves replaced by
/// younger nodes, summed; as the Rust machine gives it, collecting often too.
#[test]
fn mutable_bloblets_made_and_written_in_line() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/bloblet-tree"), "tree", &[10], FUEL, gc_every);
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
    // An `i64` or `u64` where an `int` is wanted (`TODO.md` §63,
    // `programs/native/i64-as-int.fx`): boxed there, a bignum past a fixnum.
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/i64-as-int"), "run", &[0], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
        assert_eq!(r.rust, "(9223372036854775808 18446744073709551616 -9223372036854775805 6 42)");
    }
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

/// Blobrefs natively (`TODO.md` §77, `programs/native/blobrefs.fx`): every
/// scalar read and written in line, at any alignment, a bignum `i64` by the
/// primitive, steps, owners and offsets; as the Rust machine gives them,
/// with collections moving the owner too. A read past the end fails as
/// the primitive says. (FX-26 cannot freeze a suffix: `fixpt-heap`'s tests
/// and the runtime's primitives check a write into one.)
#[test]
fn blobrefs_as_the_rust_machine_gives_them() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/blobrefs"), "blobrefs", &[5], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
    }
    let defs = "(define-type o (bloblet (fields) @heap)) \
                (define* past (subr (maxeff (alloc @heap) (read @heap)) (int) int) \
                  (lambda (k) (i64->int (blobref-get (the (blobref o i64) (blobref-at (the o (make-bloblet 12)) k))))))";
    // An `i64` at byte 8 of 12 runs past the end: refused where it is made
    // (`Checker::note_fits`).
    assert!(matches!(&run(defs, "past", &[8], FUEL).direct, Err(m) if m.contains("runs past the end")));
    // At a literal offset, in line: one past the suffix fails likewise.
    let defs = "(define-type o (bloblet (fields) @heap)) \
                (define* at (subr (alloc @heap) (int) int) \
                  (lambda (k) (blobref-offset (the (blobref o i32) (blobref-at (the o (make-bloblet 12)) 12)))))";
    assert!(matches!(&run(defs, "at", &[0], FUEL).direct, Err(m) if m.contains("no byte")));
}

/// Flat sums (`TODO.md` §77, `programs/native/flat-sums.fx`): variants
/// made and read back through blobrefs, the tag an index into the owner's
/// fields or a number, as the Rust machine gives them, with collections.
#[test]
fn flat_sums_as_the_rust_machine_gives_them() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/flat-sums"), "flat-sums", &[5], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
        assert_eq!(r.rust, "(3295581 128 1 0 7 0)");
    }
    // In line, a label no field holds and a tag past the fields fail as
    // the primitives say.
    let defs = include_str!("programs/native/flat-sums-fail.fx");
    assert!(matches!(&run(defs, "var", &[0], FUEL).direct, Err(m) if m.contains("no field of the owner holds the label")));
    assert!(matches!(&run(defs, "tag", &[1], FUEL).direct, Err(m) if m.contains("names no field")));
    assert!(run(defs, "tag", &[0], FUEL).direct.as_ref().is_ok_and(|d| d == "1"));
}

/// Flat sums of numeric keys (`TODO.md` §77, `programs/native/flat-keyed.fx`):
/// tags of one, two and four bytes, steps, `blobref-index` and raw `f64`
/// reads, all in line, as the Rust machine gives them, with collections;
/// an index past the end fails as the primitive says.
#[test]
fn flat_keyed_as_the_rust_machine_gives_them() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/flat-keyed"), "flat-keyed", &[5], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
        assert_eq!(r.rust, "(1400 1275 777444 44 1 112 1)");
    }
    let defs = "(define-type o (bloblet (fields) @heap)) \
                (define* past (subr (maxeff (alloc @heap) (read @heap)) (int) int) \
                  (lambda (k) (blobref-offset (blobref-index (the (blobref o (arrayof i32 3)) (blobref-at (the o (make-bloblet 12)) 0)) k))))";
    assert!(matches!(&run(defs, "past", &[3], FUEL).direct, Err(m) if m.contains("out of range")));
    assert!(run(defs, "past", &[2], FUEL).direct.as_ref().is_ok_and(|d| d == "8"));
}

/// Shift counts past a fixnum (kayak's report, `programs/native/
/// shift-counts.fx`): a fixed-width shift's count modulo its width, a
/// bignum's low bits, not its pointer's; as the Rust machine gives them.
#[test]
fn shift_counts_past_a_fixnum() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/shift-counts"), "shift-counts", &[1], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
        assert_eq!(r.rust, "(1 2 2147483648 1 2 9223372036854775808 -4 -1 6 512 0 -1 0)");
    }
}

/// Sums and products made in line (`%make-frozen`,
/// `programs/native/frozen-made.fx`): of one to seven fields, taken apart
/// again, as the Rust machine gives them, with collections moving them.
#[test]
fn frozen_data_made_in_line() {
    for gc_every in [None, Some(7)] {
        let r = run_collecting(&program("native/frozen-made"), "frozen-made", &[300], FUEL, gc_every);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting every {gc_every:?}: {:?} against {}", r.direct, r.rust);
        assert_eq!(r.rust, "3032200");
    }
}

/// `arithmetic-shift` (`programs/native/shifts.fx`): in line for fixnums,
/// the primitive past them, as the Rust machine gives it.
#[test]
fn shifts_as_the_rust_machine_gives_them() {
    let r = run(&program("native/shifts"), "shifts", &[5], FUEL);
    assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "{:?} against {}", r.direct, r.rust);
    assert_eq!(
        r.rust,
        "(8 -20 3 -4 1152921504606846976 2305843009213693952 3541774862152233910272 -1 0 2305843009213693950 -1152921504606846976 5)"
    );
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

/// `remainder` in line (`TODO.md` §103), a `prim2`, as `quotient` and
/// `modulo` are: of each sign of each operand, by a constant and not, the
/// least fixnum by −1, and a bignum (the primitive's), as the Rust machine
/// gives them; by zero, said.
#[test]
fn remainder_in_line_as_the_rust_machine_gives_it() {
    let defs = &program("native/remainder");
    for (a, b) in [(17, 5), (-17, 5), (17, -5), (-17, -5), (15, 5), (-15, 5), (0, 3), (-(1 << 60), -1), ((1 << 60) - 1, 7)] {
        let r = run(defs, "r", &[a, b], FUEL);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "(remainder {a} {b}): {:?} against {}\n{}", r.direct, r.rust, r.code);
    }
    for a in [20, -20, 21, -21] {
        let r = run(defs, "r7", &[a], FUEL);
        assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "(remainder {a} -7): {:?} against {}", r.direct, r.rust);
    }
    let r = run(defs, "big", &[-123456789, 1000003], FUEL);
    assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "a bignum's: {:?} against {}", r.direct, r.rust);
    assert!(matches!(&run(defs, "r", &[7, 0], FUEL).direct, Err(m) if m.contains("zero")));
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

/// Constant lists unrolled (`programs/run/unrolled-lists.fx`): the same
/// answers natively and on the Rust machine; and, the list redefined, the
/// guard fails and the search sees the new one.
#[test]
fn unrolled_constant_lists_answer_as_searched() {
    let defs = include_str!("programs/run/unrolled-lists.fx").trim_end().trim_end_matches("(score)");
    let r = run(defs, "score", &[], FUEL);
    assert_eq!((r.direct, r.rust.as_str()), (Ok("211".into()), "211"), "{}", r.code);
    let r = run(&format!("{defs}(define k syms (list 'q))\n"), "score", &[], FUEL);
    assert_eq!((r.direct, r.rust.as_str()), (Ok("-1".into()), "-1"), "{}", r.code);
}

/// `case` on each kind of atom (`programs/run/case.fx`): the same answer
/// natively and on the Rust machine.
#[test]
fn case_answers_natively() {
    let defs = include_str!("programs/run/case.fx").trim_end().trim_end_matches("(score)");
    let r = run(defs, "score", &[], FUEL);
    assert_eq!((r.direct, r.rust.as_str()), (Ok("12312342223".into()), "12312342223"), "{}", r.code);
}

/// `(with #%fx n)` under shadowing (`programs/run/standard-refs.fx`):
/// the same natively and on the Rust machine.
#[test]
fn standard_refs_answer_natively() {
    let defs = include_str!("programs/run/standard-refs.fx").trim_end().trim_end_matches("(score)");
    let r = run(defs, "score", &[], FUEL);
    assert_eq!((r.direct, r.rust.as_str()), (Ok("123456".into()), "123456"), "{}", r.code);
}

/// `case`s of many data, searched by halving (`programs/run/case-tree.fx`):
/// the same natively and on the Rust machine.
#[test]
fn case_trees_answer_natively() {
    let defs = include_str!("programs/run/case-tree.fx").trim_end().trim_end_matches("(score)");
    let r = run(defs, "score", &[], FUEL);
    assert_eq!((r.direct, r.rust.as_str()), (Ok("(78 630 820 1890 210 234)".into()), "(78 630 820 1890 210 234)"), "{}", r.code);
}

/// A module's member folded through a `with`, then the module redefined
/// (`TODO.md` §42): its global written again, the guard fails, and the
/// plain version reads the new module's member.
#[test]
fn a_folded_module_member_redefined_is_seen() {
    let step = "(define m (module (define k int 3)))\n\
                (define* step (subr (read (globals m)) (int) int) (lambda (x) (with m (+ x k))))\n";
    let r = run(step, "step", &[4], FUEL);
    assert_eq!(r.direct, Ok("7".into()), "{}", r.code);
    let r = run(&format!("{step}(define m (module (define k int 5)))\n"), "step", &[4], FUEL);
    assert_eq!((r.direct, r.rust.as_str()), (Ok("9".into()), "9"), "{}", r.code);
}

/// A constant folded in a fast version, then redefined (`TODO.md` §42):
/// each definition at the same type assigns its global, so when the machine
/// code runs the cell has been written since the fast version was compiled,
/// its `global-guard` fails, and the plain version sees the value there is
/// now.
#[test]
fn a_folded_constant_redefined_is_seen() {
    let step = "(define k int 3)\n(define flag bool #t)\n\
                (define* step (subr pure (int) int) (lambda (x) (if flag (+ x k) (- x k))))\n";
    let r = run(step, "step", &[4], FUEL);
    assert_eq!(r.direct, Ok("7".into()), "{}", r.code);
    let r = run(&format!("{step}(define k int 5)\n"), "step", &[4], FUEL);
    assert_eq!((r.direct, r.rust.as_str()), (Ok("9".into()), "9"), "{}", r.code);
    let r = run(&format!("{step}(define k int 5)\n(define flag bool #f)\n"), "step", &[4], FUEL);
    assert_eq!((r.direct, r.rust.as_str()), (Ok("-1".into()), "-1"), "{}", r.code);
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
    // Run natively, so typed so: its calls compiled as their types say.
    let mut c = Checker::with_convention(fixpt_fx26::ast::Conv::Native);
    let forms = c.read_in(FileId(0), &text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).flat_map(|(f, _)| c.top_all(f).expect("checks")).collect();
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    // What the definitions make, run as cellular code, is native (`nclosure`).
    s.scheme.runtime_unrooted().adapt = Some(fixpt_native::direct::adapt);
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
        s.set_native_convention(true);
        s.strategy = Strategy::Cellular;
        s.native_runner = Some(run_native);
        s.native_compiler = Some(fixpt_native::direct::compile_closure);
        s.register_code = true;
        s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
        s.scheme.runtime_unrooted().adapt = Some(fixpt_native::direct::adapt);
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

/// The REPL's machine (the native convention, what it declines run on
/// the arm64 cellular machine): cellular code calls a native closure, by a
/// typed call, through the Rust machine (it had been entered as a cellular
/// one, and the machine crashed). And a standard operation as a value in a
/// global's body, which a later form calls, makes that form decline
/// nothing: such a body is not inlined, as it would need the operation's
/// word, which only the stack code of the form making the closure makes.
#[test]
fn typed_calls_of_native_code() {
    let mut s = session(true);
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_registers);
    let text = "(define g (subr pure (int) int) (lambda (x) (+ x 1)))\n\
                (stay-cellular (g 1))\n\
                (define f (subr pure (int int) int) (lambda (a b) (let ((h +)) (h a b))))\n\
                (f 1 2)";
    let forms = s.checker.read_in(FileId(0), text).expect("reads");
    let out: Vec<String> =
        s.run_forms(&forms).expect("runs").into_iter().map(|o| o.map_or_else(|e| e.message, |o| format!("{}{:?}", o.printed, o.value))).collect();
    assert!(out[1].ends_with("Ok(Some(\"2\"))"), "{out:?}");
    assert_eq!(out[3], "Ok(Some(\"3\"))", "{out:?}");
}

/// A module of more members than `ldur` reaches (31) is native code too:
/// a far field is read through its address. (Declined, it ran as cellular
/// code, which cannot capture up to a prompt native code set: the
/// scheduler's module, at 32 members, failed every wait so.)
#[test]
fn far_fields_are_native_code() {
    let mut s = session(true);
    let members: String = (0..40).map(|i| format!("(define a{i} int {i}) ")).collect();
    let text = format!("(define m (module {members}(define f (subr pure () int) (lambda () (+ a0 a39)))))\n\
                        (+ (with m a39) ((with m f)))");
    let forms = s.checker.read_in(FileId(0), &text).expect("reads");
    let out: Vec<String> =
        s.run_forms(&forms).expect("runs").into_iter().map(|o| o.map_or_else(|e| e.message, |o| format!("{}{:?}", o.printed, o.value))).collect();
    assert_eq!(out[1], "Ok(Some(\"78\"))", "{out:?}");
    assert!(!out.iter().any(|o| o.contains("not in the native convention")), "{out:?}");
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

/// In one native session: conversions (as above); a global redefined
/// after native code bound it (`programs/native/redefined.fx`); an `extract` inlined
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
/// In a program whose convention is native, what cellular code makes is
/// native, as its type says (`nclosure`, `TODO.md` §97): a closure that a
/// procedure the native compiler declines gives back, a `letrec`'s made
/// where it declines (its siblings patched in through the adapters), a
/// standard operation as a value there, a closure in a list, a place's
/// (`rlambda`), its adapter in that place; each a native closure, called
/// by native code (`programs/native/made-native.fx`).
#[test]
fn what_cellular_code_makes_is_native() {
    let mut s = session(true);
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/made-native.fx")).expect("reads");
    let (values, fell) = values_and_fallbacks(&mut s, &forms);
    assert_eq!(values, ["15", "#t", "5", "42", "500500"], "{fell:?}");
    for name in ["add5", "even", "plus", "(car fns)"] {
        let native = s.with_global_value(name, |rt, v| v.is_bloblet() && rt.heap.bloblet_kind(v) == fixpt_heap::layout::kind("native-closure"));
        assert_eq!(native.expect("compiles"), Ok(true), "{name}");
    }
}

/// A place's closure in a program whose convention is native
/// (`%region-nclosure`): a native closure, an adapter over the cellular
/// one, both in the place, so that they end together.
#[test]
fn a_place_holds_its_closures_adapter() {
    let mut s = session(true);
    let rt = s.scheme.runtime_unrooted();
    let prim = |name: &str| match fixpt_runtime::PRIMITIVES.iter().find(|d| d.name == name).map(|d| &d.kind) {
        Some(fixpt_runtime::PrimKind::Simple(f)) => *f,
        _ => panic!("no simple primitive {name}"),
    };
    let word = { let u = rt.heap.undefined_closure(); rt.heap.bloblet_slot(u, fixpt_heap::layout::cellular::CLOSURE_WORD) };
    let made = |rt: &mut fixpt_runtime::Runtime, name: &str| {
        let h = rt.heap.region_enter();
        let v = prim(name)(rt, &mut [Value::fixnum(h as i64), Value::fixnum(7), word]).unwrap_or_else(|_| panic!("{name}"));
        (v, rt.heap.region_in_use(h))
    };
    let (plain, plain_words) = made(rt, "%region-closure");
    let (native, native_words) = made(rt, "%region-nclosure");
    let kind = |rt: &fixpt_runtime::Runtime, v: Value| rt.heap.bloblet_kind(v);
    assert_eq!(kind(rt, plain), fixpt_heap::layout::kind("cellular-closure"));
    assert_eq!(kind(rt, native), fixpt_heap::layout::kind("native-closure"));
    let inner = rt.heap.adapted(native).expect("an adapter");
    assert_eq!(kind(rt, inner), fixpt_heap::layout::kind("cellular-closure"));
    // The adapter, a closure over one value, as the closure is, in the
    // place with it.
    assert_eq!(native_words, 2 * plain_words, "{plain_words} {native_words}");
}

#[test]
fn native_session_adapters_aborts_and_stack_maps() {
    let mut s = session(true);
    assert_eq!(adapters_in(&mut s), ADAPTED, "adapters");
    // Native code bound to a global as compiled, the global redefined
    // after (`programs/native/redefined.fx`): the new definition, seen.
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/redefined.fx")).expect("reads");
    assert_eq!(values_of(&mut s, &forms), ["3", "201", "3", "201"], "redefined");
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
    // `f64`s passed raw to a procedure made native a form before, and,
    // once it is redefined, boxed through its cell (`TODO.md` §91).
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/raw-args-across-forms.fx")).expect("reads");
    let (values, fell) = values_and_fallbacks(&mut s, &forms);
    assert_eq!((values, fell), (vec!["250250".into(), "1000".into(), "500".into()], vec![]), "raw args across forms");
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
/// Deep recursion through a small stack cache
/// (`docs/research/deep-recursion.md`): 4096 words, so that each program's
/// frames are flushed into the heap many times over and restored as they
/// return, collecting often as they run (`programs/native/deep-control.fx`):
/// values the flushed frames hold; an abort to a prompt among them; a
/// mark read through them; a composable continuation of them, taken and
/// run twice; and continuations that cross machines.
#[test]
fn deep_recursion_through_the_stack_cache() {
    fixpt_native::direct::with_machine(|m| m.set_stack_words(4096, 1 << 26)).expect("a machine");
    let mut s = session(true);
    s.native_runner = Some(run_native_collecting);
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/deep-control.fx")).expect("reads");
    let before = fixpt_native::direct::stack_stats();
    let (values, fell) = values_and_fallbacks(&mut s, &forms);
    assert_eq!(values, ["5000049999", "1007", "50005", "60001", "60000"], "deep control");
    assert_eq!(fell, Vec::<String>::new(), "all native");
    // `level`'s frames, on a cache of 4098 words, overflow at the entry of
    // a thunk a mark in tail position called: the mark's frame moves with
    // the thunk's, which replaces it (it was 60087, with 87 marks too many).
    fixpt_native::direct::with_machine(|m| m.set_stack_words(4098, 1 << 26)).expect("a machine");
    let forms = s.checker.read_in(FileId(0), "(level 30000)").expect("reads");
    assert_eq!(values_and_fallbacks(&mut s, &forms), (vec!["60000".to_string()], vec![]), "tail marks");
    // Each program's frames went through the heap, and came back.
    let after = fixpt_native::direct::stack_stats();
    assert!(after.overflows - before.overflows > 100 && after.underflows - before.underflows > 1000, "{before:?} {after:?}");
    // Composable continuations that cross machines, and marks read across
    // them (`TODO.md` §93, `programs/native/captures.fx`), on this small
    // cache too, so that frames each machine took are in its chain.
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/captures.fx")).expect("reads");
    let (values, fell) = values_and_fallbacks(&mut s, &forms);
    let want = ["(10 10 10 10 343 343 343 343 16 16 60001 60001)", "(918 1215 1009 1009 1009)", "(77 88 158 157)"];
    assert_eq!(values, want, "captures");
    assert_eq!(fell, ["grab-c", "climb-c", "tail-c", "under-c", "grab-marks", "mark-c", "look-c", "in-c"], "only those that stay cellular do");
    // Whole continuations that cross machines, thrown and called again
    // (`TODO.md` §93, `programs/native/whole-captures.fx`).
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/whole-captures.fx")).expect("reads");
    let (values, fell) = values_and_fallbacks(&mut s, &forms);
    assert_eq!(values, ["(6 6 6 6 6 6 8 8)", "(413 413 413 413)"], "whole captures");
    assert_eq!(fell, ["throw-c", "via-c", "cap-c", "deep-c", "again-c", "keep-c"], "only those that stay cellular do");
    fixpt_native::direct::with_machine(|m| m.set_stack_words(1 << 20, 1 << 28)).expect("a machine");
}

/// Recursion alternating between native and cellular code, too deep for
/// the thread's Rust stack, on which each call between them nests (`DONE.md`
/// §93, `programs/native/crossing-overflow.fx`): a stack overflow, not a
/// crash, and the session goes on. On a thread of a known stack.
#[test]
fn crossings_too_deep_for_the_rust_stack_overflow() {
    let run = std::thread::Builder::new().stack_size(16 << 20).spawn(|| {
        let mut s = session(true);
        let forms = s.checker.read_in(FileId(0), include_str!("programs/native/crossing-overflow.fx")).expect("reads");
        values_and_fallbacks(&mut s, &forms)
    });
    let (values, fell) = run.expect("spawns").join().expect("no crash");
    assert_eq!(values, ["1000", "error: stack overflow", "1001"], "crossing overflow");
    assert_eq!(fell, ["deep-c"], "only the one that stays cellular does");
}

/// `f64`s in raw frame slots (`TODO.md` §91, `programs/native/raw-slots.fx`):
/// live across a deep recursion, through a small stack cache's overflows
/// and underflows, collecting every 7 words, so frames holding raw words
/// are flushed into the heap, copied, collected and restored; and a slot
/// that holds an `f64`, then an `int`, split, the `int` a value's. As the
/// Rust machine gives them, and through the heap many times over.
#[test]
fn raw_slots_through_the_stack_cache_and_collections() {
    let text = program("native/raw-slots");
    let defs: String = text.lines().filter(|l| !l.starts_with("(raw-slots ")).map(|l| format!("{l}\n")).collect();
    let r = run_collecting(&defs, "raw-slots", &[3000], FUEL, Some(7));
    assert_eq!(r.rust, "4277");
    assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting: {:?} against {}", r.direct, r.rust);
    let before = fixpt_native::direct::stack_stats();
    let r = direct_in(&defs, "raw-slots", &[3000], FUEL, Some(7), Some((2048, 1 << 26)));
    assert_eq!(r.direct.as_deref(), Ok("4277"), "through a small stack cache");
    let after = fixpt_native::direct::stack_stats();
    // Through the heap: flushed at overflows and collections, restored
    // after each.
    assert!(after.overflows - before.overflows > 10 && after.frames_restored - before.frames_restored > 1000, "{before:?} {after:?}");
}

/// Boxes made where native code cannot collect (`TODO.md` §102,
/// `programs/native/quiet-boxes.fx`): a loop whose only allocation is a
/// quiet call-out's, each call boxing its `f64` argument for a procedure
/// value, past the nursery's end. Its next poll collects: minor
/// collections while it runs, where there were none, and the words in use
/// growing with the loop.
#[test]
fn quiet_boxes_are_collected_at_the_next_poll() {
    let mut s = session(true);
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/quiet-boxes.fx")).expect("reads");
    let (defs, run) = forms.split_at(forms.len() - 1);
    for o in s.run_forms(defs).expect("runs") {
        assert!(o.is_ok_and(|o| !o.printed.contains("not in the native convention")), "defined natively");
    }
    let collections = |s: &mut Fx26Session| s.scheme.runtime_unrooted().heap.collections();
    let before = collections(&mut s);
    let out = s.run_forms(run).expect("runs").remove(0).expect("ran");
    assert_eq!(out.value.transpose().map(|v| v.expect("a value")).as_deref(), Some("4000002000000"));
    let made = collections(&mut s) - before;
    assert!(made >= 2, "{made} collections while 2000000 boxes were made");
}

/// `f64`s returned raw (`TODO.md` §91): to callers that take them so and to
/// callers that keep the value, from a polymorphic procedure that returns
/// one boxed, a flat array's element, and through the stack cache's
/// overflows and underflows, collecting as it goes. As the Rust machine
/// gives them.
#[test]
fn raw_returns_to_every_kind_of_caller() {
    let text = program("native/raw-returns");
    let defs: String = text.lines().filter(|l| !l.starts_with("(raw-returns ")).map(|l| format!("{l}\n")).collect();
    let r = run_collecting(&defs, "raw-returns", &[3000], FUEL, Some(7));
    assert_eq!(r.rust, "4506016");
    assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting: {:?} against {}", r.direct, r.rust);
    let before = fixpt_native::direct::stack_stats();
    let r = direct_in(&defs, "raw-returns", &[3000], FUEL, Some(7), Some((2048, 1 << 26)));
    assert_eq!(r.direct.as_deref(), Ok("4506016"), "through a small stack cache");
    let after = fixpt_native::direct::stack_stats();
    // Through the heap: flushed (at collections, here, before the cache
    // fills) and restored.
    let flushes = after.overflows + after.collection_flushes - before.overflows - before.collection_flushes;
    assert!(flushes > 10 && after.frames_restored - before.frames_restored > 1000, "{before:?} {after:?}");
}

/// `f64`s passed raw (`TODO.md` §91): to callees that take them raw and to
/// ones that take values, from callers that have them raw and ones that
/// have values, in tail calls through a global, to a continuation, and
/// through the stack cache's overflows at an entry that takes them raw,
/// collecting as it goes. As the Rust machine gives them.
#[test]
fn raw_args_between_every_kind_of_caller_and_callee() {
    let text = program("native/raw-args");
    let defs: String = text.lines().filter(|l| !l.starts_with("(raw-args ")).map(|l| format!("{l}\n")).collect();
    let r = run_collecting(&defs, "raw-args", &[3000], FUEL, Some(7));
    assert_eq!(r.rust, "8315");
    assert!(r.direct.as_ref().is_ok_and(|d| *d == r.rust), "collecting: {:?} against {}", r.direct, r.rust);
    let before = fixpt_native::direct::stack_stats();
    let r = direct_in(&defs, "raw-args", &[3000], FUEL, None, Some((2048, 1 << 26)));
    assert_eq!(r.direct.as_deref(), Ok("8315"), "through a small stack cache");
    let after = fixpt_native::direct::stack_stats();
    assert!(after.overflows - before.overflows > 10, "{before:?} {after:?}");
}

fn run_native_collecting(rt: &mut fixpt_runtime::Runtime, closure: Value, fuel: u64) -> fixpt_fx26::session::NativeRun {
    let was = std::mem::replace(&mut rt.heap.gc_every, 97);
    let r = run_native(rt, closure, fuel);
    rt.heap.gc_every = was;
    r
}

/// `run_native`, collecting at every safepoint while the native code runs.
fn run_native_collecting_always(rt: &mut fixpt_runtime::Runtime, closure: Value, fuel: u64) -> fixpt_fx26::session::NativeRun {
    let was = std::mem::replace(&mut rt.heap.gc_every, 1);
    let r = run_native(rt, closure, fuel);
    rt.heap.gc_every = was;
    r
}

/// A capture in cellular code up to a prompt in the native frames out from
/// it, collecting at every safepoint: the cellular machine kept the tag
/// across the capture's safepoint, so a collection there that moved it
/// left the frames out searched for where it had been, and found no
/// prompt (`programs/native/capture-across-collecting.fx`).
#[test]
fn a_tag_moved_at_a_capture_across_machines_finds_its_prompt() {
    let mut s = session(true);
    s.native_runner = Some(run_native_collecting_always);
    let forms = s.checker.read_in(FileId(0), include_str!("programs/native/capture-across-collecting.fx")).expect("reads");
    let (values, fell) = values_and_fallbacks(&mut s, &forms);
    // Each `1 + 3d`, `d` the cellular frames between (`captures.fx`).
    assert_eq!(values.last().map(String::as_str), Some("220"), "{values:?}");
    assert_eq!(fell, ["grab-c", "climb-c"], "only those that stay cellular do");
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
    s.set_native_convention(true);
    s.strategy = Strategy::Cellular;
    s.native_runner = Some(run_native_collecting);
    s.native_compiler = Some(fixpt_native::direct::compile_closure);
    s.register_code = true;
    s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
    s.scheme.runtime_unrooted().adapt = Some(fixpt_native::direct::adapt);
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
        s.set_native_convention(runner.is_some());
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
            // With `DIRECT_PROGRESS`, each program as it starts: the report
            // is long, and a program that loops would look like it.
            if std::env::var_os("DIRECT_PROGRESS").is_some() {
                eprintln!("{}", path.display());
            }
            let (Some(want), Some(got)) = (forms_of(&text, None), forms_of(&text, Some(run_native))) else { continue };
            for (i, (w, g)) in want.iter().zip(&got).enumerate() {
                let (Ok((w, _)), Ok((g, printed))) = (w, g) else { continue };
                if printed.contains("not in the native convention yet") {
                    declined.push(format!("{}: {}", path.display(), printed.trim()));
                } else if g.as_ref().is_ok_and(|v| v.is_some()) || g.is_err() {
                    native += 1;
                }
                // A procedure prints as the closure each makes, of either
                // kind, and perhaps an adapter: compared as a procedure.
                let procedure = |v: String| if v.starts_with("#<native-closure") || v.starts_with("#<cellular-closure") { "#<procedure>".into() } else { v };
                let kindless = |v: &Result<Option<String>, String>| v.clone().map(|v| v.map(procedure));
                if kindless(w) != kindless(g) {
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
            s.set_native_convention(true);
            s.native_runner = Some(run_native);
            s.native_compiler = Some(fixpt_native::direct::compile_closure);
            s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
            s.scheme.runtime_unrooted().adapt = Some(fixpt_native::direct::adapt);
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
