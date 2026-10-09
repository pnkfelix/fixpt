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
            }
            add("arm-ldr-reg", vec![t as i64, n as i64, 13], oracle(|| a::ldr_reg(t, n, 13)));
            for m in [0u32, 16, 31] {
                add("arm-add", vec![t as i64, n as i64, m as i64], oracle(|| a::add(t, n, m)));
                add("arm-sub", vec![t as i64, n as i64, m as i64], oracle(|| a::sub(t, n, m)));
                add("arm-adds", vec![t as i64, n as i64, m as i64], oracle(|| a::adds(t, n, m)));
                add("arm-subs", vec![t as i64, n as i64, m as i64], oracle(|| a::subs(t, n, m)));
                add("arm-orr", vec![t as i64, n as i64, m as i64], oracle(|| a::orr(t, n, m)));
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
