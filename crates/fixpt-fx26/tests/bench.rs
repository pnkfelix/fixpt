//! The benchmarks of `tests/programs/bench` (PLAN.md, M13 step 13b): each
//! program lowered to Scheme, and compiled by the Rust compiler to cellular
//! words run on each machine, best of three. Each optimization of M13 is
//! measured with this before it stays; the figures go in
//! `docs/performance.md`.
//!
//!     cargo test --release -p fixpt-fx26 --test bench -- --ignored --nocapture

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_fx26::{Checker, Top};
use fixpt_heap::Value;
use fixpt_read::FileId;
use std::time::Instant;

fn checked(text: &str) -> (Checker, Vec<Top>) {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    let tops = forms.iter().zip(done).filter(|(_, d)| !d).map(|(f, _)| c.top(f).expect("checks")).collect();
    (c, tops)
}

fn best(mut f: impl FnMut() -> String) -> (String, f64) {
    let (mut out, mut t) = (String::new(), f64::INFINITY);
    for _ in 0..3 {
        let start = Instant::now();
        out = f();
        t = t.min(start.elapsed().as_secs_f64());
    }
    (out, t)
}

#[test]
#[ignore = "a report: cargo test --release -p fixpt-fx26 --test bench -- --ignored --nocapture"]
fn benchmarks() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/bench");
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    type Run = fn(&mut fixpt_runtime::Runtime, Value, &[Value]) -> Result<Value, String>;
    let machines: [(&str, Run); 4] = [
        ("Rust machine", fixpt_engine::cellular::run_word),
        ("hand-encoded", fixpt_native::cellular::run_word_as_is),
        ("stencils -O2", fixpt_native::stencil::run_word),
        // Last: compiling to machine code changes the words' entries.
        ("words compiled", fixpt_native::cellular::run_word_compiled),
    ];
    println!("| program | lowered | {} | register code |", machines.map(|m| m.0).join(" | "));
    for path in names {
        let text = std::fs::read_to_string(&path).unwrap();
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        s.scheme.engine.set_step_limit(None);
        let (lowered, t_lowered) = best(|| {
            let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
            s.scheme.engine.set_step_limit(None);
            format!("{:?}", s.run_program(&text).map(|v| v.map_err(|e| e.to_string())).map_err(|e| e.message))
        });
        let (c, tops) = checked(&text);
        let mut row = vec![format!("{:.1} ms", 1e3 * t_lowered)];
        s.scheme.scope(|sc| {
            let w = sc.make(|m| fixpt_fx26::cellular::Compiler::new(m.heap(), &c, &text).program(&tops).expect("compiles"));
            for (_, run) in machines {
                sc.runtime_unrooted().run_word = Some(run);
                let (out, t) = best(|| {
                    let none = sc.make(|_| Value::NULL);
                    match sc.call_global("%run-word", &[w, none]) {
                        Ok(v) => sc.write(v),
                        Err(e) => format!("!! {e}"),
                    }
                });
                assert!(lowered.contains(&out), "{name}: {out} against {lowered}");
                row.push(format!("{:.1} ms", 1e3 * t));
            }
            // Register code (PLAN.md 13h′): the program compiled again, with
            // each lambda's register code, and run as that.
            let w = sc.make(|m| {
                let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, &text);
                comp.registers = true;
                comp.program(&tops).expect("compiles")
            });
            sc.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_registers);
            let (out, t) = best(|| {
                let none = sc.make(|_| Value::NULL);
                match sc.call_global("%run-word", &[w, none]) {
                    Ok(v) => sc.write(v),
                    Err(e) => format!("!! {e}"),
                }
            });
            assert!(lowered.contains(&out), "{name} as register code: {out} against {lowered}");
            row.push(format!("{:.1} ms", 1e3 * t));
        });
        println!("| {name} | {} |", row.join(" | "));
    }
}
