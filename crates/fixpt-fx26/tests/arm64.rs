//! The arm64 encoder written in FX-26 (`src/arm64.fx`) against the Rust one
//! (`fixpt_native::arm64`), its oracle, over every instruction on registers
//! and immediates up to their edges and past them (`PLAN.md` §11, 11b).
//! Where the Rust encoder refuses an operand, the FX-26 one gives -1.

use fixpt_engine::Backend;
use fixpt_heap::Value;
use fixpt_native::arm64 as a;

/// What the Rust encoder gives, or `None` where it refuses.
fn oracle(f: impl FnOnce() -> u32 + std::panic::UnwindSafe) -> Option<i64> {
    std::panic::catch_unwind(f).ok().map(|w| w as i64)
}

/// The encoders: `fx26:arm64.fx` loaded by a program that names each of its
/// definitions at top level, as `fx:name`, compiled into a Scheme session.
fn encoders() -> fixpt_scheme::Session {
    let names = fixpt_fx26::ARM64.lines().filter_map(|l| l.strip_prefix("(define ")?.split([' ', ')']).next());
    let mut program = String::from("(define arm64 (load-input \"fx26:arm64.fx\"))\n");
    for n in names {
        program.push_str(&format!("(define {n} (with arm64 {n}))\n"));
    }
    let compiled = fixpt_fx26::session::compile_program(&program).expect("checks");
    let mut s = fixpt_scheme::Session::with_backend(Backend::Bytecode);
    compiled.load_into(&mut s).expect("loads");
    s
}

const REGS: [u32; 7] = [0, 1, 9, 13, 19, 28, 31];
const SIMM9: [i64; 7] = [-257, -256, -8, 0, 8, 255, 256];
const SIMM19: [i64; 6] = [-(1 << 18) - 1, -(1 << 18), -3, 0, 5, (1 << 18) - 1];
const SIMM26: [i64; 5] = [-(1 << 25) - 1, -(1 << 25), 0, 12, (1 << 25) - 1];
const OFF12: [u32; 6] = [0, 8, 12, 4088, 32760, 32768];
const PAIR: [i64; 6] = [-520, -512, -96, 8, 504, 512];
const IMM12: [u32; 4] = [0, 1, 4095, 4096];
const CONDS: [a::Cond; 12] = [
    a::Cond::Eq, a::Cond::Ne, a::Cond::Hs, a::Cond::Lo, a::Cond::Vs, a::Cond::Vc,
    a::Cond::Hi, a::Cond::Ls, a::Cond::Ge, a::Cond::Lt, a::Cond::Gt, a::Cond::Le,
];

#[test]
fn every_instruction_as_the_rust_encoder_makes_it() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut s = encoders();
    let mut cases: Vec<(String, Vec<i64>, Option<i64>)> = Vec::new();
    let mut add = |name: &str, args: Vec<i64>, want: Option<i64>| cases.push((name.to_string(), args, want));
    for t in REGS {
        for n in REGS {
            for imm in SIMM9 {
                add("arm-ldr-post", vec![t as i64, n as i64, imm], oracle(|| a::ldr_post(t, n, imm)));
                add("arm-ldr-pre", vec![t as i64, n as i64, imm], oracle(|| a::ldr_pre(t, n, imm)));
                add("arm-str-post", vec![t as i64, n as i64, imm], oracle(|| a::str_post(t, n, imm)));
                add("arm-str-pre", vec![t as i64, n as i64, imm], oracle(|| a::str_pre(t, n, imm)));
                add("arm-ldur", vec![t as i64, n as i64, imm], oracle(|| a::ldur(t, n, imm)));
                add("arm-stur", vec![t as i64, n as i64, imm], oracle(|| a::stur(t, n, imm)));
                add("arm-ldur-w", vec![t as i64, n as i64, imm], oracle(|| a::ldur_w(t, n, imm)));
            }
            for off in OFF12 {
                add("arm-ldr", vec![t as i64, n as i64, off as i64], oracle(|| a::ldr(t, n, off)));
                add("arm-str", vec![t as i64, n as i64, off as i64], oracle(|| a::str(t, n, off)));
            }
            for imm in IMM12 {
                add("arm-add-imm", vec![t as i64, n as i64, imm as i64], oracle(|| a::add_imm(t, n, imm)));
                add("arm-sub-imm", vec![t as i64, n as i64, imm as i64], oracle(|| a::sub_imm(t, n, imm)));
                add("arm-subs-imm", vec![t as i64, n as i64, imm as i64], oracle(|| a::subs_imm(t, n, imm)));
            }
            add("arm-cmp-imm", vec![n as i64, 7], oracle(|| a::cmp_imm(n, 7)));
            add("arm-cmp", vec![t as i64, n as i64], oracle(|| a::cmp(t, n)));
            add("arm-mov", vec![t as i64, n as i64], oracle(|| a::mov(t, n)));
            for bits in [0u32, 1, 3, 32, 63, 64] {
                add("arm-and-low", vec![t as i64, n as i64, bits as i64], oracle(|| a::and_low(t, n, bits)));
            }
            add("arm-tst-low", vec![n as i64, 3], oracle(|| a::tst_low(n, 3)));
            for (lsb, width) in [(3u32, 8u32), (0, 1), (60, 4), (61, 4)] {
                add("arm-ubfx", vec![t as i64, n as i64, lsb as i64, width as i64], oracle(|| a::ubfx(t, n, lsb, width)));
            }
            for sh in [0u32, 3, 63, 64] {
                add("arm-asr-imm", vec![t as i64, n as i64, sh as i64], oracle(|| a::asr_imm(t, n, sh)));
                add("arm-lsl-imm", vec![t as i64, n as i64, sh as i64], oracle(|| a::lsl_imm(t, n, sh)));
            }
            add("arm-ldr-reg", vec![t as i64, n as i64, 13], oracle(|| a::ldr_reg(t, n, 13)));
            for m in [0u32, 16, 31] {
                add("arm-add", vec![t as i64, n as i64, m as i64], oracle(|| a::add(t, n, m)));
                add("arm-sub", vec![t as i64, n as i64, m as i64], oracle(|| a::sub(t, n, m)));
                add("arm-adds", vec![t as i64, n as i64, m as i64], oracle(|| a::adds(t, n, m)));
                add("arm-subs", vec![t as i64, n as i64, m as i64], oracle(|| a::subs(t, n, m)));
                add("arm-orr", vec![t as i64, n as i64, m as i64], oracle(|| a::orr(t, n, m)));
                add("arm-sdiv", vec![t as i64, n as i64, m as i64], oracle(|| a::sdiv(t, n, m)));
                add("arm-eor", vec![t as i64, n as i64, m as i64], oracle(|| a::eor(t, n, m)));
                add("arm-mul", vec![t as i64, n as i64, m as i64], oracle(|| a::mul(t, n, m)));
                add("arm-smulh", vec![t as i64, n as i64, m as i64], oracle(|| a::smulh(t, n, m)));
                add("arm-and", vec![t as i64, n as i64, m as i64], oracle(|| a::and(t, n, m)));
                add("arm-lslv", vec![t as i64, n as i64, m as i64], oracle(|| a::lslv(t, n, m)));
                add("arm-asrv", vec![t as i64, n as i64, m as i64], oracle(|| a::asrv(t, n, m)));
                add("arm-msub", vec![t as i64, n as i64, m as i64, 19], oracle(|| a::msub(t, n, m, 19)));
                for sh in [0u32, 1, 3, 63, 64] {
                    add("arm-add-lsl", vec![t as i64, n as i64, m as i64, sh as i64], oracle(|| a::add_lsl(t, n, m, sh)));
                }
            }
            for imm in PAIR {
                add("arm-stp-pre", vec![t as i64, 30, n as i64, imm], oracle(|| a::stp_pre(t, 30, n, imm)));
                add("arm-ldp-post", vec![t as i64, 30, n as i64, imm], oracle(|| a::ldp_post(t, 30, n, imm)));
                add("arm-stp", vec![t as i64, 30, n as i64, imm], oracle(|| a::stp(t, 30, n, imm)));
                add("arm-ldp", vec![t as i64, 30, n as i64, imm], oracle(|| a::ldp(t, 30, n, imm)));
            }
            for c in CONDS {
                add("arm-csel", vec![t as i64, n as i64, 16, c as i64], oracle(|| a::csel(t, n, 16, c)));
            }
        }
        for (imm, hw) in [(0u32, 0u32), (0xffff, 3), (0x1234, 1), (0x10000, 0), (1, 4)] {
            add("arm-movz", vec![t as i64, imm as i64, hw as i64], oracle(|| a::movz(t, imm, hw)));
            add("arm-movk", vec![t as i64, imm as i64, hw as i64], oracle(|| a::movk(t, imm, hw)));
        }
        for w in SIMM19 {
            add("arm-ldr-lit", vec![t as i64, w], oracle(|| a::ldr_lit(t, w)));
            add("arm-cbz", vec![t as i64, w], oracle(|| a::cbz(t, w)));
            add("arm-cbnz", vec![t as i64, w], oracle(|| a::cbnz(t, w)));
        }
        add("arm-br", vec![t as i64], oracle(|| a::br(t)));
        add("arm-blr", vec![t as i64], oracle(|| a::blr(t)));
    }
    for c in CONDS {
        for w in SIMM19 {
            add("arm-b-cond", vec![c as i64, w], oracle(|| a::b_cond(c, w)));
        }
    }
    for w in SIMM26 {
        add("arm-b", vec![w], oracle(|| a::b(w)));
        add("arm-bl", vec![w], oracle(|| a::bl(w)));
    }
    let _ = std::panic::take_hook();
    let mut wrong = Vec::new();
    for (name, args, want) in &cases {
        let got = s.scope(|sc| {
            let args: Vec<_> = args.iter().map(|x| sc.make(|_| Value::fixnum(*x))).collect();
            let r = sc.call_global(&format!("fx:{name}"), &args).expect("runs");
            sc.view(|v| v.get(r).fixnum().expect("an int"))
        });
        if got != want.unwrap_or(-1) {
            wrong.push(format!("{name} {args:?}: FX-26 {got:#x}, Rust {want:x?}"));
        }
    }
    assert!(wrong.is_empty(), "{} of {} disagree:\n{}", wrong.len(), cases.len(), wrong.join("\n"));
    let ret = s.scope(|sc| {
        let r = sc.global(&"fx:arm-ret").expect("bound");
        sc.view(|v| v.get(r).fixnum())
    });
    assert_eq!(ret, Some(a::ret() as i64));
    let nop = s.scope(|sc| {
        let r = sc.global(&"fx:arm-nop").expect("bound");
        sc.view(|v| v.get(r).fixnum())
    });
    assert_eq!(nop, Some(a::NOP as i64));
    eprintln!("{} encodings agree", cases.len());
}

/// And a constant of any size, as `mov_imm64` loads it.
#[test]
fn constants_as_the_rust_encoder_loads_them() {
    let mut s = encoders();
    for v in [0u64, 1, 0xffff, 0x1_0000, 0x1234_5678, 0x0f00_0000_0000_0001, (1 << 59) - 1] {
        let want: Vec<i64> = a::mov_imm64(13, v).into_iter().map(|w| w as i64).collect();
        let got: Vec<i64> = s.scope(|sc| {
            let (d, x) = (sc.make(|_| Value::fixnum(13)), sc.make(|_| Value::fixnum(v as i64)));
            let r = sc.call_global(&"fx:arm-mov-imm64", &[d, x]).expect("runs");
            sc.view(|w| w.get(r).list().expect("a list").iter().map(|x| x.fixnum().expect("an int")).collect())
        });
        assert_eq!(got, want, "{v:#x}");
    }
}

/// What the native convention's compiler uses besides
/// (`native-direct-arm64*.fx`): narrow and indexed memory, wide
/// immediates, division, shifts by a register, and floating point; and a
/// card marked, as `card_mark` marks it.
#[test]
fn the_native_conventions_instructions_as_the_rust_encoder_makes_them() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut s = encoders();
    let mut cases: Vec<(String, Vec<i64>, Option<i64>)> = Vec::new();
    let mut add = |name: &str, args: Vec<i64>, want: Option<i64>| cases.push((name.to_string(), args, want));
    type F3 = fn(u32, u32, u32) -> u32;
    type F2 = fn(u32, u32) -> u32;
    for t in REGS {
        for n in REGS {
            for imm in SIMM9 {
                let nine: [(&str, fn(u32, u32, i64) -> u32); 6] =
                    [("arm-ldur-w", a::ldur_w), ("arm-ldurh", a::ldurh), ("arm-ldurb", a::ldurb), ("arm-sturh", a::sturh), ("arm-sturb", a::sturb), ("arm-stur-w", a::stur_w)];
                for (name, f) in nine {
                    add(name, vec![t as i64, n as i64, imm], oracle(move || f(t, n, imm)));
                }
            }
            for m in [0u32, 16, 31] {
                let three: [(&str, F3); 18] = [
                    ("arm-ldr-x8", a::ldr_x8),
                    ("arm-ldr-w4", a::ldr_w4),
                    ("arm-ldrsw-4", a::ldrsw_4),
                    ("arm-str-x8", a::str_x8),
                    ("arm-str-w4", a::str_w4),
                    ("arm-eor", a::eor),
                    ("arm-and", a::and),
                    ("arm-sdiv", a::sdiv),
                    ("arm-udiv", a::udiv),
                    ("arm-mul", a::mul),
                    ("arm-smulh", a::smulh),
                    ("arm-lslv", a::lslv),
                    ("arm-lsrv", a::lsrv),
                    ("arm-asrv", a::asrv),
                    ("arm-fadd", a::fadd),
                    ("arm-fsub", a::fsub),
                    ("arm-fmul", a::fmul),
                    ("arm-fdiv", a::fdiv),
                ];
                for (name, f) in three {
                    add(name, vec![t as i64, n as i64, m as i64], oracle(move || f(t, n, m)));
                }
                for sh in [0u32, 3, 63, 64] {
                    add("arm-add-lsl", vec![t as i64, n as i64, m as i64, sh as i64], oracle(move || a::add_lsl(t, n, m, sh)));
                }
                add("arm-msub", vec![t as i64, n as i64, m as i64, 7], oracle(move || a::msub(t, n, m, 7)));
            }
            for imm in IMM12 {
                add("arm-add-imm-pages", vec![t as i64, n as i64, imm as i64], oracle(|| a::add_imm_pages(t, n, imm)));
                add("arm-sub-imm-pages", vec![t as i64, n as i64, imm as i64], oracle(|| a::sub_imm_pages(t, n, imm)));
                add("arm-adds-imm", vec![t as i64, n as i64, imm as i64], oracle(|| a::adds_imm(t, n, imm)));
            }
            for (lsb, width) in [(3u32, 8u32), (0, 1), (3, 61), (0, 63), (0, 64), (60, 4), (61, 4), (3, 32)] {
                add("arm-and-bits", vec![t as i64, n as i64, lsb as i64, width as i64], oracle(|| a::and_bits(t, n, lsb, width)));
            }
            for sh in [0u32, 3, 29, 63, 64] {
                add("arm-lsl-imm", vec![t as i64, n as i64, sh as i64], oracle(|| a::lsl_imm(t, n, sh)));
            }
            let two: [(&str, F2); 16] = [
                ("arm-fmov-to-d", a::fmov_to_d),
                ("arm-fmov-from-d", a::fmov_from_d),
                ("arm-fabs", a::fabs),
                ("arm-fneg", a::fneg),
                ("arm-fsqrt", a::fsqrt),
                ("arm-frintn", a::frintn),
                ("arm-frintp", a::frintp),
                ("arm-frintm", a::frintm),
                ("arm-frintz", a::frintz),
                ("arm-fcmp", a::fcmp),
                ("arm-scvtf", a::scvtf),
                ("arm-fcvtzs", a::fcvtzs),
                ("arm-fmov-to-s", a::fmov_to_s),
                ("arm-fmov-from-s", a::fmov_from_s),
                ("arm-cmp", a::cmp),
                ("arm-mov", a::mov),
            ];
            for (name, f) in two {
                add(name, vec![t as i64, n as i64], oracle(move || f(t, n)));
            }
        }
        add("arm-cmp-sp", vec![t as i64], oracle(|| a::cmp_sp(t)));
        for w in [-(1i64 << 18) - 1, -(1 << 18), -3, 0, 5, (1 << 18) - 1, 1 << 18] {
            add("arm-adr", vec![t as i64, w], oracle(|| a::adr(t, w)));
        }
    }
    let _ = std::panic::take_hook();
    let mut wrong = Vec::new();
    for (name, args, want) in &cases {
        let got = s.scope(|sc| {
            let args: Vec<_> = args.iter().map(|x| sc.make(|_| Value::fixnum(*x))).collect();
            let r = sc.call_global(&format!("fx:{name}"), &args).expect("runs");
            sc.view(|v| v.get(r).fixnum().expect("an int"))
        });
        if got != want.unwrap_or(-1) {
            wrong.push(format!("{name} {args:?}: FX-26 {got:#x}, Rust {want:x?}"));
        }
    }
    // A single's instruction from a double's.
    for w in [a::fadd(16, 16, 17), a::fdiv(16, 16, 17), a::fsqrt(16, 16), a::frintn(16, 16), a::fcmp(16, 17), a::fneg(16, 16), a::scvtf(16, 13)] {
        let got = s.scope(|sc| {
            let x = sc.make(|_| Value::fixnum(w as i64));
            let r = sc.call_global("fx:arm-single", &[x]).expect("runs");
            sc.view(|v| v.get(r).fixnum().expect("an int"))
        });
        if got != a::single(w) as i64 {
            wrong.push(format!("arm-single {w:#x}: FX-26 {got:#x}, Rust {:#x}", a::single(w)));
        }
    }
    for (obj, off, cards) in [(1u32, -12i64, 600u32), (13, 0, 8), (16, 4092, 32760), (2, -4095, 0)] {
        let want: Vec<i64> = a::card_mark(obj, off, 24, cards, 16, 17).into_iter().map(|w| w as i64).collect();
        let got: Vec<i64> = s.scope(|sc| {
            let args: Vec<_> = [obj as i64, off, 24, cards as i64, 16, 17].iter().map(|x| sc.make(|_| Value::fixnum(*x))).collect();
            let r = sc.call_global("fx:arm-card-mark", &args).expect("runs");
            sc.view(|w| w.get(r).list().expect("a list").iter().map(|x| x.fixnum().expect("an int")).collect())
        });
        if got != want {
            wrong.push(format!("arm-card-mark {obj} {off} {cards}: FX-26 {got:x?}, Rust {want:x?}"));
        }
    }
    let nop = s.scope(|sc| {
        let r = sc.global(&"fx:arm-nop").expect("bound");
        sc.view(|v| v.get(r).fixnum())
    });
    assert_eq!(nop, Some(a::NOP as i64));
    assert!(wrong.is_empty(), "{} of {} disagree:\n{}", wrong.len(), cases.len(), wrong.join("\n"));
    eprintln!("{} encodings agree", cases.len());
}
