//! Register code (PLAN.md 13h′): the Rust compiler, asked to, gives each
//! lambda it can a twin of MacScheme-machine instructions, each checked by
//! the heap as it is made.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_fx26::Checker;
use fixpt_read::FileId;

/// The program compiled with register code, shown.
fn shown(text: &str) -> String {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).flat_map(|(f, _)| c.top_all(f).expect("checks")).collect();
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let mut out = String::new();
    s.scheme.scope(|sc| {
        sc.make(|m| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, text);
            comp.registers = true;
            let w = comp.program(&tops).expect("compiles");
            out = fixpt_runtime::disasm::disassemble(m.heap(), w);
            w
        });
    });
    out
}

#[test]
fn the_benchmarks_procedures_have_register_code() {
    for p in ["fib", "tak", "loop"] {
        let text = std::fs::read_to_string(format!("{}/tests/programs/bench/{p}.fx", env!("CARGO_MANIFEST_DIR"))).unwrap();
        let out = shown(&text);
        assert!(out.contains("its register code"), "{p}:\n{out}");
    }
}

/// `fib`'s: one frame slot for `n` and one for the first call's value;
/// arguments and the rest in registers; its calls of itself by its own
/// entry, while its global holds it, else through the global, as any use
/// of the global is (`docs/fx26.md`, "Redefinition").
#[test]
fn fib_in_registers() {
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/bench/fib.fx")).unwrap();
    let out = shown(&text);
    for want in ["save 2", "op2imm int-less 2", "global fib", "global-guard fib", "invokeself 1", "invoke 1", "setstk 1", "op2 int-add 1", "pop 2"] {
        assert!(out.contains(want), "{want}:\n{out}");
    }
}

/// Bound locally, with `letrec`, a procedure's calls of itself are by its
/// own entry: the binding cannot change.
#[test]
fn a_letrec_procedure_calls_itself_directly() {
    let out = shown(include_str!("programs/redefine/local-fib.fx"));
    assert!(out.contains("invokeself 1"), "{out}");
}

/// Every test program compiles with register code, which the heap checks
/// as it makes each register word.
#[test]
fn every_test_program_has_well_formed_register_code() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    for sub in ["bidirectional", "bloblet", "control", "run", "pldi89", "bench", "datum"] {
        for p in std::fs::read_dir(format!("{dir}/{sub}")).unwrap() {
            let path = p.unwrap().path();
            let text = std::fs::read_to_string(&path).unwrap();
            let mut c = Checker::new();
            let Ok(forms) = c.read_in(FileId(0), &text) else { continue };
            let Ok(done) = c.declare_ahead(&forms) else { continue };
            let tops: Result<Vec<Vec<_>>, _> = forms.iter().zip(done).filter(|(_, d)| !d).map(|(f, _)| c.top_all(f)).collect();
            let tops = tops.map(|t| t.concat());
            let Ok(tops) = tops else { continue };
            let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
            s.scheme.scope(|sc| {
                sc.make(|m| {
                    let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, &text);
                    comp.registers = true;
                    comp.program(&tops).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
                });
            });
        }
    }
}

/// Every test program that checks and runs, compiled with register code
/// and run on the native machine as register code, gives what the
/// lowering gives.
#[test]
fn register_code_runs_as_lowered() {
    runs_as_lowered(None);
}

/// The same, collecting at every allocation, so that every object moves
/// under every call-out: what register code keeps in registers across one
/// would be stale.
#[test]
fn register_code_runs_as_lowered_while_collecting() {
    runs_as_lowered(Some(1));
}

fn runs_as_lowered(gc_every: Option<u64>) {
    use fixpt_heap::Value;
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let (mut report, mut ran) = (Vec::new(), 0);
    for sub in ["bidirectional", "bloblet", "control", "run", "pldi89", "bench", "datum"] {
        let mut paths: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|p| p.unwrap().path()).collect();
        paths.sort();
        for path in paths {
            if sub == "bench" && !path.to_string_lossy().contains("tak") {
                continue; // the others are long; the benchmark runs them
            }
            let text = std::fs::read_to_string(&path).unwrap();
            let mut c = Checker::new();
            let Ok(forms) = c.read_in(FileId(0), &text) else { continue };
            let Ok(done) = c.declare_ahead(&forms) else { continue };
            let tops: Result<Vec<Vec<_>>, _> = forms.iter().zip(done).filter(|(_, d)| !d).map(|(f, _)| c.top_all(f)).collect();
            let tops = tops.map(|t| t.concat());
            let Ok(tops) = tops else { continue };
            let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
            let Ok(Ok(lowered)) = s.run_program(&text).map(|v| v.map_err(|e| e.to_string())) else { continue };
            let got = s.scheme.scope(|sc| {
                let w = sc.make(|m| {
                    let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, &text);
                    comp.registers = true;
                    comp.program(&tops).expect("compiles")
                });
                sc.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_registers);
                if let Some(n) = gc_every {
                    sc.set_gc_every(n);
                }
                let none = sc.make(|_| Value::NULL);
                match sc.call_global("%run-word", &[w, none]) {
                    Ok(v) => sc.write(v),
                    Err(e) => format!("!! {e}"),
                }
            });
            ran += 1;
            let norm = |v: &str| if v.is_empty() || v == "#u" { "#u".to_string() } else { v.to_string() };
            if norm(&got) != norm(&lowered) {
                report.push(format!("{}: register code {got:?}, lowered {lowered:?}", path.display()));
            }
        }
    }
    assert!(report.is_empty(), "{}", report.join("\n"));
    assert!(ran >= 15, "only {ran}");
}

/// `program` in `tests/programs/run`, compiled with register code and run
/// as that, collecting at every `gc_every`th safepoint if asked: what it
/// gives, the words allocated in regions, and how many are live after.
fn run_in_registers(program: &str, gc_every: Option<u64>) -> (String, u64, usize) {
    let (got, words, live, _) = run_in_registers_counting(program, gc_every);
    (got, words, live)
}

/// The same, and how many collections there were.
fn run_in_registers_counting(program: &str, gc_every: Option<u64>) -> (String, u64, usize, u64) {
    use fixpt_heap::Value;
    let text = std::fs::read_to_string(format!("{}/tests/programs/run/{program}", env!("CARGO_MANIFEST_DIR"))).unwrap();
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), &text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).flat_map(|(f, _)| c.top_all(f).expect("checks")).collect();
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    s.scheme.scope(|sc| {
        let w = sc.make(|m| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, &text);
            comp.registers = true;
            comp.program(&tops).expect("compiles")
        });
        sc.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_registers);
        if let Some(n) = gc_every {
            sc.set_gc_every(n);
        }
        let none = sc.make(|_| Value::NULL);
        let got = sc.call_global("%run-word", &[w, none]).map(|v| sc.write(v)).unwrap_or_else(|e| format!("!! {e}"));
        let h = &sc.runtime_unrooted().heap;
        (got, h.region_words(), h.live_regions(), h.gc_count)
    })
}

/// A `letrena`'s `rcons`s, in the helpers its body makes, are made in the
/// heap's regions, which are all ended when the program is done; and the
/// same, collecting at every safepoint, when the regions are roots.
#[test]
fn a_letrena_allocates_in_its_region() {
    for gc_every in [None, Some(1)] {
        let (got, words, live) = run_in_registers("arena.fx", gc_every);
        assert_eq!(got, (1000 * 55).to_string());
        assert_eq!(words, 1000 * 20, "ten pairs each call, in a region");
        assert_eq!(live, 0);
    }
}

/// Closures made by `rlambda`, a `letrec`'s and a list of them, are made
/// in the region too.
#[test]
fn closures_are_made_in_a_region() {
    for gc_every in [None, Some(1)] {
        let (got, words, live) = run_in_registers("region-closures.fx", gc_every);
        assert_eq!(got, "(55 42)");
        assert!(words > 10 * 2 + 10 * 4, "ten pairs and ten closures, and the helpers: {words}");
        assert_eq!(live, 0);
    }
}

/// An abort out of the bodies of regions, to a prompt around them, ends
/// them: none is live when the program is done, though no form's end has
/// ended them.
#[test]
fn an_abort_ends_the_regions_it_leaves() {
    for gc_every in [None, Some(1)] {
        let (got, words, live) = run_in_registers("region-escapes.fx", gc_every);
        assert_eq!(got, (500 * 1001).to_string());
        assert_eq!(words, 1000 * 4, "two pairs each round");
        assert_eq!(live, 0);
    }
}

/// A throw to a whole continuation, out of the bodies of regions entered
/// since it was taken, ends them, as an abort does
/// (`docs/research/soundness-findings.md`, F7).
#[test]
fn a_throw_ends_the_regions_it_leaves() {
    for gc_every in [None, Some(1)] {
        let (got, words, live) = run_in_registers("region-throws.fx", gc_every);
        assert_eq!(got, (500 * 1001).to_string());
        assert_eq!(words, 1000 * 4, "two pairs each round");
        assert_eq!(live, 0);
    }
}

/// A `letreap` is collected while its body runs: 300,000 pairs go
/// through it, though it holds a thousand live at a time; and it ends.
#[test]
fn a_letreap_is_collected_as_it_runs() {
    for gc_every in [None, Some(1000)] {
        let (got, words, live, collections) = run_in_registers_counting("reap.fx", gc_every);
        assert_eq!(got, "500500");
        assert!(words >= 300 * 1000 * 2, "{words}");
        assert_eq!(live, 0);
        assert!(collections >= 10, "what the reap takes starts collections: {collections}");
    }
}

/// A map over a lambda: `map1` only calls `f`, or passes it on to itself,
/// so the call runs a copy of `map1` made for the lambda (named for both),
/// whose calls of `f` are the lambda's body, `k` read from the lambda's
/// closure, and whose calls of itself are by its own entry; each call
/// behind a guard that `map1` is still what the copy was made from.
#[test]
fn a_map_over_a_lambda_is_specialized() {
    let out = shown(include_str!("programs/run/map-specialized.fx"));
    let copy = out.split("\nword map1@lambda@").nth(1).expect("a copy of map1");
    let copy = copy.split("\nword ").next().unwrap_or(copy);
    for want in ["field 3", "op2 int-add", "global map1", "op2imm eq", "invokeself 2"] {
        assert!(copy.contains(want), "{want}:\n{copy}");
    }
    assert!(!copy.contains("invoke 1"), "the lambda is not called:\n{copy}");
}

/// Constants through inlining: `(sum2 i 2)` is `(+ (dbl i) (dbl 2))`, and
/// `(dbl 2)`, `(+ 2 2)`, is 4, folded; behind `dbl`'s guard, since `dbl`
/// may yet be redefined, so the sum is not folded further.
#[test]
fn constants_are_folded_through_inlined_calls() {
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/bench/helpers.fx")).unwrap();
    let out = shown(&text);
    assert!(out.contains("const 4"), "{out}");
}

/// A `letrec`-bound procedure entered and calling itself only in tail
/// position is a join point: `count`'s `loop` is no closure and no call,
/// but code in `count` itself, its parameters in registers (`count` a
/// leaf), each call a jump.
#[test]
fn a_loop_entered_in_tail_position_is_a_join_point() {
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/bench/loop.fx")).unwrap();
    let out = shown(&text);
    let count = out.split("its register code").nth(1).expect("register code");
    let count = count.split("\nword ").next().unwrap_or(count);
    assert!(!count.contains("lambda") && !count.contains("invoke") && !count.contains("save"), "{count}");
    assert!(count.contains("movereg") && count.contains("branch"), "{count}");
}

/// A body that inlines, where no global can change while it runs, has two
/// versions: after `args`, one `global-guard` for each global it assumes,
/// then the fast version, a leaf (no `save`) with no guard inside; the
/// plain one, as ever, after.
#[test]
fn a_body_that_inlines_has_two_versions() {
    let out = shown(include_str!("programs/run/versions.fx"));
    let step = out.split("its register code").find(|c| c.contains("global-guard sum2") && c.contains("0: args 2")).expect("step's register code");
    let lines: Vec<&str> = step.lines().skip(1).take_while(|l| !l.is_empty()).collect();
    assert!(lines[0].contains("args 2"), "{step}");
    let guards = lines.iter().skip(1).take_while(|l| l.contains("global-guard")).count();
    assert!(guards >= 2, "{step}");
    let fast: Vec<&&str> = lines.iter().skip(1 + guards).take_while(|l| !l.contains("save")).collect();
    assert!(fast.iter().any(|l| l.contains("return")) && !fast.iter().any(|l| l.contains("global-guard") || l.contains("invoke")), "{step}");
}

/// A lambda inside another has one word, made by the stack code of the body
/// it is in, which the register code of that body uses too: not one more
/// for each, and so twice as many at every depth. Both compilers.
#[test]
fn a_nested_lambda_is_compiled_once() {
    let text = "(lambda ((a int)) (lambda ((b int)) (lambda ((c int)) (lambda ((d int)) (+ a (+ b (+ c d)))))))";
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let (fx26, rust) = fixpt_fx26::compare::both_compilers(&mut s, text).expect("checks");
    for (who, code) in [("FX-26", fx26), ("Rust", rust)] {
        let code = code.unwrap_or_else(|e| panic!("{who}: {e}"));
        let words = code.lines().filter(|l| l.starts_with("word ")).count();
        // The program's word and the four lambdas'.
        assert_eq!(words, 5, "{who}:\n{code}");
    }
}

/// A constructor called on constants, inlined in a fast version, is a
/// constant made once while compiling: no `%make-frozen` when it runs.
/// Both compilers.
#[test]
fn a_constructor_of_constants_is_made_once() {
    let text = "(define-datatype col (red) (rgb int int int))
                (define* f (subr pure () col) (lambda () (rgb 1 2 3)))
                (f)";
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let (fx26, rust) = fixpt_fx26::compare::both_compilers(&mut s, text).expect("checks");
    for (who, code) in [("FX-26", fx26), ("Rust", rust)] {
        let code = code.unwrap_or_else(|e| panic!("{who}: {e}"));
        let f = &code[code.find("its register code").expect("register code")..];
        let fast = &f[..f.find("global rgb").expect("the plain version")];
        assert!(fast.contains("const #<sum rgb>") && !fast.contains("%make-frozen"), "{who}:\n{f}");
    }
}

/// A constant first goes second, an immediate, where the operation does not
/// care which; and a chain of `+` and `-` of constants adds their sum at
/// once (integers are exact). Both compilers.
#[test]
fn constants_are_combined_and_made_immediates() {
    let text = "(define* f (subr pure (int) int) (lambda (x) (- (+ 1 (+ 2 x)) 10))) (f 3)";
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let (fx26, rust) = fixpt_fx26::compare::both_compilers(&mut s, text).expect("checks");
    for (who, code) in [("FX-26", fx26), ("Rust", rust)] {
        let code = code.unwrap_or_else(|e| panic!("{who}: {e}"));
        let ops: Vec<&str> = code.lines().filter(|l| l.contains("op2")).collect();
        assert_eq!(ops.len(), 1, "{who}:\n{code}");
        assert!(ops[0].ends_with("op2imm int-sub 7"), "{who}:\n{code}");
    }
}

/// A test made of `and`, `or` and `not` is jumps: each comparison branches
/// straight to where its outcome goes, and no boolean is made (Twobit's
/// `pass2if.sch` gets there by rewriting `if`s in tests). Both compilers.
#[test]
fn a_compound_test_is_jumps() {
    let text = "(define* f (subr pure (int int) int)
                  (lambda (x y) (if (and (< x 10) (not (= y 0))) 1 (if (or (= x 3) (< y x)) 2 3))))
                (f 3 4)";
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let (fx26, rust) = fixpt_fx26::compare::both_compilers(&mut s, text).expect("checks");
    for (who, code) in [("FX-26", fx26), ("Rust", rust)] {
        let code = code.unwrap_or_else(|e| panic!("{who}: {e}"));
        let reg = &code[code.find("its register code").expect("register code")..];
        let n = |op: &str| reg.lines().filter(|l| l.contains(op)).count();
        assert_eq!((n("branchf"), n("brancht"), n("const #")), (2, 2, 0), "{who}:\n{reg}");
    }
}
