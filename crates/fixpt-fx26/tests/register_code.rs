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
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).map(|(f, _)| c.top(f).expect("checks")).collect();
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let mut out = String::new();
    s.scheme.scope(|sc| {
        sc.make(|m| {
            let mut comp = fixpt_fx26::threaded::Compiler::new(m.heap(), &c, text);
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
/// arguments and the rest in registers.
#[test]
fn fib_in_registers() {
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/bench/fib.fx")).unwrap();
    let out = shown(&text);
    for want in ["save 2", "op2imm int-less 2", "invoke 1", "setstk 1", "op2 int-add 1", "pop 2"] {
        assert!(out.contains(want), "{want}:\n{out}");
    }
}

/// Every test program compiles with register code, which the heap checks
/// as it makes each register word.
#[test]
fn every_test_program_has_well_formed_register_code() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    for sub in ["bidirectional", "bloblet", "control", "run", "pldi89", "bench"] {
        for p in std::fs::read_dir(format!("{dir}/{sub}")).unwrap() {
            let path = p.unwrap().path();
            let text = std::fs::read_to_string(&path).unwrap();
            let mut c = Checker::new();
            let Ok(forms) = c.read_in(FileId(0), &text) else { continue };
            let Ok(done) = c.declare_ahead(&forms) else { continue };
            let tops: Result<Vec<_>, _> = forms.iter().zip(done).filter(|(_, d)| !d).map(|(f, _)| c.top(f)).collect();
            let Ok(tops) = tops else { continue };
            let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
            s.scheme.scope(|sc| {
                sc.make(|m| {
                    let mut comp = fixpt_fx26::threaded::Compiler::new(m.heap(), &c, &text);
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
    for sub in ["bidirectional", "bloblet", "control", "run", "pldi89", "bench"] {
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
            let tops: Result<Vec<_>, _> = forms.iter().zip(done).filter(|(_, d)| !d).map(|(f, _)| c.top(f)).collect();
            let Ok(tops) = tops else { continue };
            let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
            let Ok(Ok(lowered)) = s.run_program(&text).map(|v| v.map_err(|e| e.to_string())) else { continue };
            let got = s.scheme.scope(|sc| {
                let w = sc.make(|m| {
                    let mut comp = fixpt_fx26::threaded::Compiler::new(m.heap(), &c, &text);
                    comp.registers = true;
                    comp.program(&tops).expect("compiles")
                });
                sc.runtime_unrooted().run_word = Some(fixpt_native::threaded::run_word_registers);
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

/// A `letrena`'s `rcons`s, in the helpers its body makes, are made in the
/// heap's regions, which are all ended when the program is done; and the
/// same, collecting at every safepoint, when the regions are roots.
#[test]
fn a_letrena_allocates_in_its_region() {
    use fixpt_heap::Value;
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/run/arena.fx")).unwrap();
    for gc_every in [None, Some(1)] {
        let mut c = Checker::new();
        let forms = c.read_in(FileId(0), &text).expect("reads");
        let done = c.declare_ahead(&forms).expect("declares");
        let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).map(|(f, _)| c.top(f).expect("checks")).collect();
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        let (got, words, live) = s.scheme.scope(|sc| {
            let w = sc.make(|m| {
                let mut comp = fixpt_fx26::threaded::Compiler::new(m.heap(), &c, &text);
                comp.registers = true;
                comp.program(&tops).expect("compiles")
            });
            sc.runtime_unrooted().run_word = Some(fixpt_native::threaded::run_word_registers);
            if let Some(n) = gc_every {
                sc.set_gc_every(n);
            }
            let none = sc.make(|_| Value::NULL);
            let got = sc.call_global("%run-word", &[w, none]).map(|v| sc.write(v)).unwrap_or_else(|e| format!("!! {e}"));
            let h = &sc.runtime_unrooted().heap;
            (got, h.region_words(), h.live_regions())
        });
        assert_eq!(got, (1000 * 55).to_string());
        assert_eq!(words, 1000 * 20, "ten pairs each call, in a region");
        assert_eq!(live, 0);
    }
}
