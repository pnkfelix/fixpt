//! The disassembler against the encoders: each form it knows, made by its
//! encoder and read back as the instruction it is.

use fixpt_native::arm64::disasm::disassemble;
use fixpt_native::arm64::*;

#[test]
fn every_encoder_reads_back() {
    let cases: Vec<(u32, &str)> = vec![
        (ldr_post(9, 20, -8), "ldr x9, [x20], #-8"),
        (ldr_pre(1, 2, 16), "ldr x1, [x2, #16]!"),
        (str_post(3, 22, 8), "str x3, [x22], #8"),
        (str_pre(13, 23, -16), "str x13, [x23, #-16]!"),
        (ldr(16, 24, 128), "ldr x16, [x24, #128]"),
        (str(13, 24, 72), "str x13, [x24, #72]"),
        (ldur(10, 11, -20), "ldur x10, [x11, #-20]"),
        (ldur_w(10, 11, 4), "ldur w10, [x11, #4]"),
        (stur(1, 2, -8), "stur x1, [x2, #-8]"),
        (ldr_lit(0, -2), "ldr x0, @1"),
        (ldr_reg(10, 25, 9), "ldr x10, [x25, x9]"),
        (stp_pre(29, 30, SP, -96), "stp x29, x30, [sp, #-96]!"),
        (ldp_post(29, 30, SP, 96), "ldp x29, x30, [sp], #96"),
        (stp(21, 22, SP, 32), "stp x21, x22, [sp, #32]"),
        (ldp(27, 28, SP, 80), "ldp x27, x28, [sp, #80]"),
        (add_imm(9, 9, 1), "add x9, x9, #1"),
        (sub_imm(20, 11, 20), "sub x20, x11, #20"),
        (add(11, 19, 9), "add x11, x19, x9"),
        (add_lsl(1, 2, 3, 3), "add x1, x2, x3, lsl #3"),
        (sub(13, 13, 20), "sub x13, x13, x20"),
        (adds(0, 1, 2), "adds x0, x1, x2"),
        (subs(0, 1, 2), "subs x0, x1, x2"),
        (subs_imm(28, 28, 1), "subs x28, x28, #1"),
        (adds_imm(0, 1, 8), "adds x0, x1, #8"),
        (cmp_sp(27), "cmp sp, x27"),
        (orr(1, 2, 3), "orr x1, x2, x3"),
        (and_low(1, 2, 3), "and x1, x2, #0x7"),
        (tst_low(9, 3), "tst x9, #0x7"),
        (ubfx(1, 2, 3, 4), "ubfx x1, x2, #3, #4"),
        (asr_imm(1, 2, 3), "asr x1, x2, #3"),
        (cmp_imm(13, 0), "cmp x13, #0"),
        (cmp(1, 2), "cmp x1, x2"),
        (csel(1, 2, 3, Cond::Lt), "csel x1, x2, x3, lt"),
        (mov(21, 9), "mov x21, x9"),
        (movz(0, 42, 0), "movz x0, #0x2a"),
        (movk(0, 0xbeef, 2), "movk x0, #0xbeef, lsl #32"),
        (b(-5), "b @-2"),
        (bl(4), "bl @7"),
        (b_cond(Cond::Ne, 3), "b.ne @6"),
        (cbz(10, 7), "cbz x10, @10"),
        (cbnz(16, -1), "cbnz x16, @2"),
        (br(16), "br x16"),
        (blr(10), "blr x10"),
        (NOP, "nop"),
        (sdiv(1, 2, 3), "sdiv x1, x2, x3"),
        (msub(1, 2, 3, 4), "msub x1, x2, x3, x4"),
        (eor(1, 2, 3), "eor x1, x2, x3"),
        (ret(), "ret"),
    ];
    for (w, want) in cases {
        assert_eq!(disassemble(w, 3), want, "{w:#010x}");
    }
}

#[test]
fn what_no_encoder_makes_is_a_word() {
    assert_eq!(disassemble(0, 0), ".word 0x00000000");
}

/// Every instruction a native machine makes reads as one: its own code,
/// and the code of words it compiles.
#[test]
fn everything_the_native_machine_makes_reads_back() {
    use fixpt_engine::cellular::examples;
    use fixpt_heap::Heap;
    use fixpt_native::cellular::{NativeMachine, machine_code_text};
    let m = NativeMachine::new();
    let unread: Vec<String> = m
        .machine_instructions()
        .iter()
        .enumerate()
        .map(|(i, w)| disassemble(*w, i as i64))
        .filter(|t| t.starts_with(".word"))
        .collect();
    assert!(unread.is_empty(), "the machine's own code: {unread:?}");
    let mut heap = Heap::new();
    let mut m = NativeMachine::new();
    for w in [examples::fib(&mut heap), examples::sum_to(&mut heap), examples::list_sum(&mut heap)] {
        m.compile_reachable(&mut heap, w).expect("compiles");
        let text = machine_code_text(&heap, w).expect("compiled");
        assert!(!text.contains(".word"), "{text}");
        assert!(text.lines().count() > 2, "{text}");
    }
}
