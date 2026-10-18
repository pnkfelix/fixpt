//! The native convention's compiler to x86_64 written in FX-26
//! (`src/native-direct-x64.fx` and the files beside it) against the Rust
//! one (`fixpt_native::direct`'s `procedure_x64`), its oracle, piece by
//! piece: each piece's bytes, and the call-outs it numbers, the same as the
//! Rust piece's of the same name (`fixpt_native::direct::oracle_x64`). The
//! whole compiler, procedure by procedure, is `tests/native_x64.rs`'s.
//! Any machine compiles for x86_64; none runs the code here.

use fixpt_engine::Backend;
use fixpt_heap::Value;

/// The compiler's modules, as the conductor makes them, and each piece
/// tested named at top level as `fx:name`, compiled into a Scheme session.
fn pieces(names: &[&str]) -> fixpt_scheme::Session {
    let mut program = String::from(
        "(define x86-64 (load-input \"fx26:x86_64.fx\"))\n\
         (define dl (load-module \"fx26:native-direct-x64-layout.fx\"))\n\
         (define asm ((load-input \"fx26:native-direct-x64-asm.fx\") x86-64 dl))\n",
    );
    for n in names {
        program.push_str(&format!("(define {n} (with asm {n}))\n"));
    }
    let compiled = fixpt_fx26::session::compile_program(&program).unwrap_or_else(|e| panic!("checks: {e}"));
    let mut s = fixpt_scheme::Session::with_backend(Backend::Bytecode);
    compiled.load_into(&mut s).expect("loads");
    s
}

/// The bytes FX-26's `name` makes of integer `args`.
fn bytes_of(s: &mut fixpt_scheme::Session, name: &str, args: &[i64]) -> Vec<u8> {
    s.scope(|sc| {
        let args: Vec<_> = args.iter().map(|x| sc.make(|_| Value::fixnum(*x))).collect();
        let r = sc.call_global(&format!("fx:{name}"), &args).unwrap_or_else(|e| panic!("{name} runs: {e}"));
        sc.view(|v| v.get(r).list().expect("a list").iter().map(|b| b.fixnum().expect("an int") as u8).collect())
    })
}

#[test]
fn the_continuation_procedure_as_the_rust_compiler_makes_it() {
    let mut s = pieces(&["da-continuation-code"]);
    for n in [0i64, 7, 300] {
        let (want, _) = fixpt_native::direct::oracle_x64("continuation-code", &[n]).expect("a piece");
        let got = bytes_of(&mut s, "da-continuation-code", &[n]);
        assert_eq!(got, want, "continuation code {n}: FX-26 {got:02x?}, Rust {want:02x?}");
    }
}
