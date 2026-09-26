//! The encoder is ours; the system assembler is only the oracle here. Every
//! encoding in `arm64.rs` is checked against it: each
//! instruction is written out as assembly text, assembled by `as`, and the
//! word it produced compared with the encoder's.

use fixpt_native::arm64::*;

/// Assemble `lines` with the system assembler and return the words.
fn assemble(lines: &[String]) -> Vec<u32> {
    // One directory per call: the tests run in parallel.
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("fixpt-arm64-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let src = dir.join("t.s");
    let obj = dir.join("t.o");
    let text = format!(".text\n.p2align 2\n{}\n", lines.join("\n"));
    std::fs::write(&src, text).expect("writes");
    let out = std::process::Command::new("as")
        .args(["-arch", "arm64", "-o"])
        .arg(&obj)
        .arg(&src)
        .output()
        .expect("runs as");
    assert!(out.status.success(), "as failed: {}", String::from_utf8_lossy(&out.stderr));
    let dump = std::process::Command::new("otool").args(["-t", "-X"]).arg(&obj).output().expect("runs otool");
    let text = String::from_utf8_lossy(&dump.stdout);
    text.lines()
        .flat_map(|l| l.split_whitespace().skip(1).map(|w| u32::from_str_radix(w, 16).expect("hex word")).collect::<Vec<_>>())
        .collect()
}

#[test]
fn every_encoding_matches_the_assembler() {
    use Cond::*;
    let cases: Vec<(u32, String)> = vec![
        (ldr_post(9, 20, -8), "ldr x9, [x20], #-8".into()),
        (ldr_post(3, 0, 8), "ldr x3, [x0], #8".into()),
        (ldr_pre(20, 22, -8), "ldr x20, [x22, #-8]!".into()),
        (str_post(20, 22, 8), "str x20, [x22], #8".into()),
        (str_pre(1, 2, -16), "str x1, [x2, #-16]!".into()),
        (ldr(19, 24, 0), "ldr x19, [x24]".into()),
        (ldr(23, 24, 32), "ldr x23, [x24, #32]".into()),
        (str(20, 24, 8), "str x20, [x24, #8]".into()),
        (ldur(11, 10, -16), "ldur x11, [x10, #-16]".into()),
        (stur(13, 21, -8), "stur x13, [x21, #-8]".into()),
        (ldr_lit(0, -2), "ldr x0, .-8".into()),
        (ldr_lit(7, 3), "ldr x7, .+12".into()),
        (ldr_reg(12, 23, 11), "ldr x12, [x23, x11]".into()),
        (stp_pre(29, 30, SP, -96), "stp x29, x30, [sp, #-96]!".into()),
        (ldp_post(29, 30, SP, 96), "ldp x29, x30, [sp], #96".into()),
        (stp(19, 20, SP, 16), "stp x19, x20, [sp, #16]".into()),
        (ldp(21, 22, SP, 32), "ldp x21, x22, [sp, #32]".into()),
        (add_imm(20, 10, 24), "add x20, x10, #24".into()),
        (sub_imm(10, 9, 4), "sub x10, x9, #4".into()),
        (sub_imm(20, 10, 24), "sub x20, x10, #24".into()),
        (add(10, 19, 10), "add x10, x19, x10".into()),
        (sub(13, 13, 9), "sub x13, x13, x9".into()),
        (adds(15, 14, 13), "adds x15, x14, x13".into()),
        (subs(15, 14, 13), "subs x15, x14, x13".into()),
        (subs_imm(28, 28, 1), "subs x28, x28, #1".into()),
        (orr(15, 13, 14), "orr x15, x13, x14".into()),
        (and_low(14, 13, 3), "and x14, x13, #7".into()),
        (and_low(1, 2, 8), "and x1, x2, #0xff".into()),
        (tst_low(9, 3), "tst x9, #7".into()),
        (ubfx(14, 14, 3, 8), "ubfx x14, x14, #3, #8".into()),
        (add_imm(29, SP, 0), "mov x29, sp".into()),
        (cbnz(0, -5), "cbnz x0, .-20".into()),
        (b_cond(Vs, 2), "b.vs .+8".into()),
        (b_cond(Hs, 2), "b.hs .+8".into()),
        (b_cond(Lo, 2), "b.lo .+8".into()),
        (b_cond(Hi, 2), "b.hi .+8".into()),
        (b_cond(Ls, 2), "b.ls .+8".into()),
        (b_cond(Gt, 2), "b.gt .+8".into()),
        (asr_imm(14, 9, 3), "asr x14, x9, #3".into()),
        (cmp_imm(9, 3), "cmp x9, #3".into()),
        (cmp(13, 9), "cmp x13, x9".into()),
        (csel(9, 14, 15, Lt), "csel x9, x14, x15, lt".into()),
        (mov(0, 9), "mov x0, x9".into()),
        (movz(14, 11, 0), "movz x14, #11".into()),
        (movz(1, 0xbeef, 1), "movz x1, #0xbeef, lsl #16".into()),
        (movk(1, 0x1234, 3), "movk x1, #0x1234, lsl #48".into()),
        (b(-3), "b .-12".into()),
        (b(5), "b .+20".into()),
        (bl(2), "bl .+8".into()),
        (b_cond(Eq, 4), "b.eq .+16".into()),
        (b_cond(Ne, -2), "b.ne .-8".into()),
        (cbz(9, 3), "cbz x9, .+12".into()),
        (br(12), "br x12".into()),
        (blr(16), "blr x16".into()),
        (ret(), "ret".into()),
    ];
    let lines: Vec<String> = cases.iter().map(|(_, s)| s.clone()).collect();
    let words = assemble(&lines);
    assert_eq!(words.len(), cases.len(), "as produced {} words for {} lines", words.len(), cases.len());
    for ((ours, text), theirs) in cases.iter().zip(&words) {
        assert_eq!(*ours, *theirs, "{text}: ours {ours:#010x}, as {theirs:#010x}");
    }
}

#[test]
fn a_64_bit_constant_is_built_in_pieces() {
    let v = 0x1234_0000_beef_0042u64;
    let ours = mov_imm64(5, v);
    let theirs = assemble(&[
        "movz x5, #0x42".into(),
        "movk x5, #0xbeef, lsl #16".into(),
        "movk x5, #0x1234, lsl #48".into(),
    ]);
    assert_eq!(ours, theirs);
}
