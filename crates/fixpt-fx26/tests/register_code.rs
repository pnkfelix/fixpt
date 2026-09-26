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
