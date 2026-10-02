//! First-class modules, stage M1 (`docs/research/first-class-modules.md`):
//! each program in `programs/modules` says on its first line what it gives,
//! `;; => value`, or what its refusal says, `;; ! words`, lowered. Kept in
//! files: the checker written in FX-26 has no modules yet (M2), and the
//! tests compare both checkers on every literal program in these sources.

mod common;

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

#[test]
fn module_programs_do_as_they_say() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/modules");
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    let (mut wrong, mut seen) = (Vec::new(), 0);
    for path in names {
        let text = std::fs::read_to_string(&path).unwrap();
        let first = text.lines().next().unwrap_or("");
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        let got = match s.run_program(&text) {
            Ok(Ok(v)) => Ok(v),
            Ok(Err(e)) => Err(e.to_string()),
            Err(e) => Err(e.message),
        };
        seen += 1;
        let ok = match (first.strip_prefix(";; => "), first.strip_prefix(";; ! "), &got) {
            (Some(want), _, Ok(v)) => v == want,
            (_, Some(want), Err(e)) => e.contains(want),
            _ => false,
        };
        if !ok {
            wrong.push(format!("{}: says `{first}`, gives {got:?}", path.display()));
        }
    }
    assert!(seen >= 10, "only {seen} programs");
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The compiler written in Rust (`src/cellular.rs`) makes each program
/// that runs into cellular words, which give what the lowering gives
/// (stage M3; the compiler written in FX-26 is compared with it by
/// `rust_compiler.rs` once it has modules too).
#[test]
fn the_rust_compiler_runs_modules_as_lowered() {
    use fixpt_fx26::{Checker, Top};
    use fixpt_heap::Value;
    use fixpt_read::FileId;
    let checked = |text: &str| -> Result<(Checker, Vec<Top>), String> {
        let mut c = Checker::new();
        let forms = c.read_in(FileId(0), text).map_err(|e| e.message)?;
        let done = c.declare_ahead(&forms).map_err(|e| e.message)?;
        let mut tops = Vec::new();
        for (f, done) in forms.iter().zip(done) {
            if !done {
                tops.extend(c.top_all(f).map_err(|e| e.message)?);
            }
        }
        Ok((c, tops))
    };
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/modules");
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    let (mut wrong, mut ran) = (Vec::new(), 0);
    for path in names {
        let text = std::fs::read_to_string(&path).unwrap();
        let Ok((c, tops)) = checked(&text) else { continue };
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        let Ok(Ok(lowered)) = s.run_program(&text) else { continue };
        // Its cellular words on the machine written in Rust; and its
        // register code too, on the hand-encoded machine.
        let machines: [(&str, Option<fixpt_runtime::RunWord>); 2] =
            [("cellular words", None), ("register code", Some(fixpt_native::cellular::run_word_registers))];
        for (what, run) in machines {
            let got = s.scheme.scope(|sc| {
                let mut err = None;
                let w = sc.make(|m| {
                    let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, &text);
                    comp.registers = run.is_some();
                    match comp.program(&tops) {
                        Ok(w) => w,
                        Err(e) => {
                            err = Some(e);
                            Value::NULL
                        }
                    }
                });
                if let Some(e) = err {
                    return format!("!! {e}");
                }
                if let Some(run) = run {
                    sc.runtime_unrooted().run_word = Some(run);
                    // Every procedure has register code: none that makes or
                    // opens a module was declined.
                    let mut n = 0;
                    sc.make(|m| {
                        let v = m.get(w);
                        n = common::register_words(m.heap(), v, &mut Default::default());
                        v
                    });
                    // `make`, the conversions, `inc`, `value` and `use`: a
                    // module declined would leave those inside it without.
                    if path.ends_with("made-in-procedure.fx") && n < 6 {
                        return format!("!! {n} register words, where every procedure should have some");
                    }
                }
                let none = sc.make(|_| Value::NULL);
                match sc.call_global("%run-word", &[w, none]) {
                    Ok(v) => sc.write(v),
                    Err(e) => format!("!! {e}"),
                }
            });
            ran += 1;
            if got != lowered {
                wrong.push(format!("{}, {what}: compiled {got:?}, lowered {lowered:?}", path.display()));
            }
        }
    }
    assert!(ran >= 5, "only {ran} ran");
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
