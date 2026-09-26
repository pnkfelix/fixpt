//! Hash tables written in FX-26 (`src/table.fx`), over arrays and bloblets.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;

fn run(program: &str) -> String {
    let program = format!("{}\n{program}", fixpt_fx26::TABLE);
    let mut answers = Vec::new();
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = Fx26Session::with_backend(backend).expect("starts");
        let v = s.run_program(&program).unwrap_or_else(|e| panic!("does not check: {e}"));
        answers.push(v.unwrap_or_else(|e| format!("!! {e}")));
    }
    assert_eq!(answers[0], answers[1], "the engines disagree");
    answers.pop().expect("two")
}

#[test]
fn a_symbol_table_counts() {
    assert_eq!(run(include_str!("programs/bloblet/table-use.fx")), "(3 0 3)");
}

#[test]
fn a_table_grows_and_keeps_everything() {
    // 1000 string keys through several doublings; every value found again.
    assert_eq!(run(include_str!("programs/bloblet/table-grow.fx")), "(1000 499500 0)");
}
