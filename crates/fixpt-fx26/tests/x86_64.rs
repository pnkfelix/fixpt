//! The x86_64 encoder written in FX-26 (`src/x86_64.fx`) against the Rust
//! one (`fixpt_native::x86_64`), its oracle, as `tests/arm64.rs` checks the
//! arm64 one: over every register, and immediates and displacements up to
//! the edges of each form and past them.

use fixpt_engine::Backend;
use fixpt_heap::Value;
use fixpt_native::x86_64 as x;

/// The encoders: `fx26:x86_64.fx` loaded by a program that names each of
/// its definitions at top level, as `fx:name`, compiled into a Scheme
/// session.
fn encoders() -> fixpt_scheme::Session {
    let names = fixpt_fx26::X86_64.lines().filter_map(|l| l.strip_prefix("(define ")?.split([' ', ')']).next());
    let mut program = String::from("(define x86-64 (load-input \"fx26:x86_64.fx\"))\n");
    for n in names {
        program.push_str(&format!("(define {n} (with x86-64 {n}))\n"));
    }
    let compiled = fixpt_fx26::session::compile_program(&program).expect("checks");
    let mut s = fixpt_scheme::Session::with_backend(Backend::Bytecode);
    compiled.load_into(&mut s).expect("loads");
    s
}

const REGS: [u8; 8] = [0, 1, 3, 4, 5, 8, 12, 13];
const DISPS: [i32; 8] = [0, 1, -8, 127, 128, -128, -129, 4096];
const IMMS: [i32; 6] = [0, 1, -1, 127, 128, -129];

#[test]
fn every_instruction_as_the_rust_encoder_makes_it() {
    use x::{Alu, Cond, Shift, m, mi};
    let mut s = encoders();
    let mut cases: Vec<(String, Vec<i64>, Vec<u8>)> = Vec::new();
    let mut add = |name: &str, args: Vec<i64>, want: x::Ins| cases.push((name.to_string(), args, want.to_vec()));
    let alus = [Alu::Add, Alu::Or, Alu::And, Alu::Sub, Alu::Xor, Alu::Cmp];
    for d in 0..16u8 {
        for s in REGS {
            add("x86-mov", vec![d as i64, s as i64], x::mov(d, s));
            add("x86-test", vec![d as i64, s as i64], x::test(d, s));
            for op in alus {
                add("x86-alu", vec![op as i64, d as i64, s as i64], x::alu(op, d, s));
            }
        }
        for b in 0..16u8 {
            for disp in DISPS {
                add("x86-load", vec![d as i64, b as i64, disp as i64], x::load(d, m(b, disp)));
                add("x86-store", vec![b as i64, disp as i64, d as i64], x::store(m(b, disp), d));
                add("x86-lea", vec![d as i64, b as i64, disp as i64], x::lea(d, m(b, disp)));
            }
            for (ix, scale, disp) in [(0u8, 1u8, 0i32), (6, 8, -16), (12, 4, 200), (13, 2, 0)] {
                let a = vec![d as i64, b as i64, ix as i64, scale as i64, disp as i64];
                add("x86-load-ix", a.clone(), x::load(d, mi(b, ix, scale, disp)));
                add("x86-lea-ix", a, x::lea(d, mi(b, ix, scale, disp)));
                add("x86-jmp-m", vec![b as i64, ix as i64, scale as i64, disp as i64], x::jmp_m(mi(b, ix, scale, disp)));
                add("x86-store8-imm", vec![b as i64, ix as i64, scale as i64, disp as i64, 1], x::store8_imm(mi(b, ix, scale, disp), 1));
            }
            add("x86-jmp-m", vec![b as i64, -1, 1, 520], x::jmp_m(m(b, 520)));
            add("x86-call-m", vec![b as i64, 88], x::call_m(m(b, 88)));
            add("x86-cmov-m", vec![Cond::L as i64, d as i64, b as i64, 56], x::cmov_m(Cond::L, d, m(b, 56)));
            add("x86-cmov-m", vec![Cond::E as i64, d as i64, b as i64, 0], x::cmov_m(Cond::E, d, m(b, 0)));
            add("x86-cmov", vec![Cond::B as i64, d as i64, b as i64], x::cmov(Cond::B, d, b));
        }
        for op in alus {
            for imm in IMMS.into_iter().chain([0x1000, -0x12345]) {
                add("x86-alu-imm", vec![op as i64, d as i64, imm as i64], x::alu_imm(op, d, imm));
            }
            for disp in [0, 64, -20, 400] {
                add("x86-alu-rm", vec![op as i64, d as i64, R15 as i64, disp as i64], x::alu_rm(op, d, m(R15, disp)));
                for imm in [1, 8, 1000] {
                    add("x86-alu-mi", vec![op as i64, d as i64, disp as i64, imm as i64], x::alu_mi(op, m(d, disp), imm));
                }
            }
        }
        for imm in [0u32, 7, 3, 0xffff_ffff] {
            add("x86-test-imm", vec![d as i64, imm as i64], x::test_imm(d, imm));
        }
        for imm in [0u64, 5, 0xffff_ffff, 0x1_0000_0000, (-6i64) as u64, (-0x8000_0000i64) as u64, 0x0123_4567_89ab_cdef] {
            add("x86-mov-imm", vec![d as i64, imm as i64], x::mov_imm(d, imm));
        }
        for op in [Shift::Shl, Shift::Shr, Shift::Sar] {
            for imm in [1u8, 3, 9, 63] {
                add("x86-shift-imm", vec![op as i64, d as i64, imm as i64], x::shift_imm(op, d, imm));
            }
        }
        add("x86-jmp-r", vec![d as i64], x::jmp_r(d));
        // Register code's.
        add("x86-push", vec![d as i64], x::push(d));
        add("x86-pop", vec![d as i64], x::pop(d));
        add("x86-neg", vec![d as i64], x::neg(d));
        add("x86-idiv", vec![d as i64], x::idiv(d));
        for s in 0..16u8 {
            add("x86-imul", vec![d as i64, s as i64], x::imul(d, s));
            add("x86-movzx8", vec![d as i64, s as i64], x::movzx8(d, s));
        }
        for op in [Shift::Shl, Shift::Shr, Shift::Sar] {
            add("x86-shift-cl", vec![op as i64, d as i64], x::shift_cl(op, d));
        }
        for b in 0..16u8 {
            for disp in [0, 8, -12, 744, 4096] {
                add("x86-push-m", vec![b as i64, disp as i64], x::push_m(m(b, disp)));
                add("x86-pop-m", vec![b as i64, disp as i64], x::pop_m(m(b, disp)));
                add("x86-neg-m", vec![b as i64, disp as i64], x::neg_m(m(b, disp)));
                add("x86-load32-ix", vec![d as i64, b as i64, -1, 1, disp as i64], x::load32(d, m(b, disp)));
            }
            for (ix, scale, disp) in [(0u8, 1u8, 0i32), (1, 4, 4), (12, 8, -16)] {
                add("x86-load32-ix", vec![d as i64, b as i64, ix as i64, scale as i64, disp as i64], x::load32(d, mi(b, ix, scale, disp)));
                add("x86-call-m-ix", vec![b as i64, ix as i64, scale as i64, disp as i64], x::call_m(mi(b, ix, scale, disp)));
            }
        }
    }
    add("x86-cqo", vec![], x::cqo());
    add("x86-ret", vec![], x::ret());
    // The native convention's (`native-direct-x64.fx`).
    for d in 0..16u8 {
        for disp in [0i32, -8, 300, -0x1234] {
            add("x86-load-rip", vec![d as i64, disp as i64], x::load_rip(d, disp));
            add("x86-lea-rip", vec![d as i64, disp as i64], x::lea_rip(d, disp));
        }
        add("x86-div", vec![d as i64], x::div(d));
        add("x86-not", vec![d as i64], x::not(d));
        add("x86-call-r", vec![d as i64], x::call_r(d));
        for b in 0..16u8 {
            for (ix, scale, disp) in [(-1i64, 1u8, 0i32), (-1, 1, -4), (-1, 1, 200), (0, 1, 0), (6, 8, -16), (12, 4, 4), (13, 2, 0)] {
                let mem = if ix < 0 { m(b, disp) } else { mi(b, ix as u8, scale, disp) };
                let a = |first: i64| vec![first, b as i64, ix, scale as i64, disp as i64];
                let s = |last: i64| vec![b as i64, ix, scale as i64, disp as i64, last];
                add("x86-store-ix", s(d as i64), x::store(mem, d));
                add("x86-store32-ix", s(d as i64), x::store32(mem, d));
                add("x86-store8-ix", s(d as i64), x::store8(mem, d));
                add("x86-store16-ix", s(d as i64), x::store16(mem, d));
                add("x86-load32s-ix", a(d as i64), x::load32s(d, mem));
                add("x86-load8-ix", a(d as i64), x::load8(d, mem));
                add("x86-load16-ix", a(d as i64), x::load16(d, mem));
                if d == 0 {
                    for imm in [0, 1, -1, 0x1234_5678] {
                        add("x86-store-imm", s(imm as i64), x::store_imm(mem, imm));
                    }
                }
            }
        }
    }
    for xr in 0..16u8 {
        for r in 0..16u8 {
            add("x86-movq-to-xmm", vec![xr as i64, r as i64], x::movq_to_xmm(xr, r));
            add("x86-movq-from-xmm", vec![r as i64, xr as i64], x::movq_from_xmm(r, xr));
            add("x86-movd-to-xmm", vec![xr as i64, r as i64], x::movd_to_xmm(xr, r));
            add("x86-movd-from-xmm", vec![r as i64, xr as i64], x::movd_from_xmm(r, xr));
            add("x86-cvtsi2sd", vec![xr as i64, r as i64], x::cvtsi2sd(xr, r));
            add("x86-cvttsd2si", vec![r as i64, xr as i64], x::cvttsd2si(r, xr));
            for double in [false, true] {
                add("x86-ucomis", vec![double as i64, xr as i64, r as i64], x::ucomis(double, xr, r));
                for op in [x::Fop::Sqrt, x::Fop::Add, x::Fop::Mul, x::Fop::Sub, x::Fop::Div] {
                    add("x86-fop", vec![double as i64, op as i64, xr as i64, r as i64], x::fop(double, op, xr, r));
                }
                for mode in 0..4u8 {
                    add("x86-round", vec![double as i64, xr as i64, r as i64, mode as i64], x::round(double, xr, r, mode));
                }
            }
        }
    }

    for rel in [0i32, -5, 100, -0x8000_0000, 0x7fff_ffff] {
        add("x86-jmp", vec![rel as i64], x::jmp(rel));
        add("x86-call", vec![rel as i64], x::call(rel));
        for c in 0..16u8 {
            add("x86-jcc", vec![c as i64, rel as i64], x::jcc(Cond::from_bits(c), rel));
        }
    }
    // No-ops are bytes, not one instruction.
    for n in 0..40usize {
        cases.push(("x86-nops".into(), vec![n as i64], x::nops(n)));
    }
    let mut wrong = Vec::new();
    for (name, args, want) in &cases {
        let got: Vec<u8> = s.scope(|sc| {
            let args: Vec<_> = args.iter().map(|x| sc.make(|_| Value::fixnum(*x))).collect();
            let r = sc.call_global(&format!("fx:{name}"), &args).expect("runs");
            sc.view(|v| v.get(r).list().expect("a list").iter().map(|b| b.fixnum().expect("an int") as u8).collect())
        });
        if &got != want {
            wrong.push(format!("{name} {args:?}: FX-26 {got:02x?}, Rust {want:02x?}"));
        }
    }
    assert!(wrong.is_empty(), "{} of {} disagree:\n{}", wrong.len(), cases.len(), wrong.iter().take(40).cloned().collect::<Vec<_>>().join("\n"));
    eprintln!("{} encodings agree", cases.len());
}

const R15: u8 = x::R15;
