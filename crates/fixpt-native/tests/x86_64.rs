//! The x86_64 encoder against the system assembler, as `tests/arm64.rs`
//! checks the arm64 one: each instruction written out as assembly text (in
//! the assembler's Intel syntax), assembled by `as`, and its bytes compared
//! with the encoder's; and the disassembler reading the encoder's bytes back
//! as that text. On macOS, its own `as` (LLVM's), for x86_64; on another
//! machine that is not x86_64, binutils for it (`x86_64-linux-gnu-as`).

use fixpt_native::x86_64::disasm::disassemble;
use fixpt_native::x86_64::*;

/// Assemble `lines` with the system assembler, each by itself: the bytes
/// of each.
fn assemble(lines: &[String]) -> Vec<Vec<u8>> {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("fixpt-x86_64-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    // Each line after a label of its own, so that its bytes can be found:
    // a symbol table gives where each starts.
    let mut text = String::from(".intel_syntax noprefix\n.text\n");
    for (i, l) in lines.iter().enumerate() {
        // LLVM's assembler, macOS's, takes no `.` in an Intel operand: the
        // line's own label is where it starts.
        let l = if cfg!(target_os = "macos") { l.replace(" .+", &format!(" i{i}+")).replace(" .-", &format!(" i{i}-")) } else { l.clone() };
        text += &format!("i{i}:\n{l}\n");
    }
    text += &format!("i{}:\n", lines.len());
    let (src, obj, bin) = (dir.join("t.s"), dir.join("t.o"), dir.join("t.bin"));
    std::fs::write(&src, text).expect("writes");
    // On macOS its own assembler, for x86_64, and the text read back by
    // `otool`, as `tests/arm64.rs` does; elsewhere GNU binutils.
    let macos = cfg!(target_os = "macos");
    let prefix = if macos || cfg!(target_arch = "x86_64") { "" } else { "x86_64-linux-gnu-" };
    let out = std::process::Command::new(format!("{prefix}as"))
        .args(if macos { &["-arch", "x86_64"][..] } else { &[] })
        .arg("-o")
        .arg(&obj)
        .arg(&src)
        .output()
        .unwrap_or_else(|e| panic!("runs {prefix}as (binutils for x86_64): {e}"));
    assert!(out.status.success(), "{prefix}as failed: {}", String::from_utf8_lossy(&out.stderr));
    let bytes = if macos {
        let dump = std::process::Command::new("otool").args(["-t", "-X"]).arg(&obj).output().expect("runs otool");
        String::from_utf8_lossy(&dump.stdout)
            .lines()
            .flat_map(|l| l.split_whitespace().skip(1).map(|b| u8::from_str_radix(b, 16).expect("hex byte")).collect::<Vec<_>>())
            .collect()
    } else {
        let out = std::process::Command::new(format!("{prefix}objcopy"))
            .args(["-O", "binary", "--only-section=.text"])
            .arg(&obj)
            .arg(&bin)
            .output()
            .unwrap_or_else(|e| panic!("runs {prefix}objcopy: {e}"));
        assert!(out.status.success(), "{prefix}objcopy failed: {}", String::from_utf8_lossy(&out.stderr));
        std::fs::read(&bin).expect("reads")
    };
    let nm = std::process::Command::new(format!("{prefix}nm")).arg(&obj).output().expect("runs nm");
    let mut at = vec![0usize; lines.len() + 1];
    for l in String::from_utf8_lossy(&nm.stdout).lines() {
        let f: Vec<&str> = l.split_whitespace().collect();
        if let [addr, _, name] = f[..]
            && let Some(i) = name.strip_prefix('i').and_then(|i| i.parse::<usize>().ok())
        {
            at[i] = usize::from_str_radix(addr, 16).expect("hex");
        }
    }
    (0..lines.len()).map(|i| bytes[at[i]..at[i + 1]].to_vec()).collect()
}

/// An instruction, its assembly text, and how the disassembler shows it
/// (the same text, unless given).
fn case(i: Ins, text: &str) -> (Ins, String, String) {
    (i, text.into(), text.into())
}

fn case2(i: Ins, text: &str, shown: &str) -> (Ins, String, String) {
    (i, text.into(), shown.into())
}

#[test]
fn every_encoding_matches_the_assembler() {
    use Cond::*;
    let mut cases = vec![
        case(mov(RAX, RCX), "mov rax, rcx"),
        case(mov(R15, RDI), "mov r15, rdi"),
        case(mov(R9, R12), "mov r9, r12"),
        case(load(RAX, m(R14, 0)), "mov rax, [r14]"),
        case(load(RCX, m(R15, 64)), "mov rcx, [r15+64]"),
        case(load(RDX, m(R13, 0)), "mov rdx, [r13]"),
        case(load(RDX, m(RBP, -8)), "mov rdx, [rbp-8]"),
        case(load(R8, m(R12, 8)), "mov r8, [r12+8]"),
        case(load(R11, m(RSP, 0)), "mov r11, [rsp]"),
        case(load(RSI, m(RBX, 4096)), "mov rsi, [rbx+4096]"),
        case(load(RDI, m(RAX, -20)), "mov rdi, [rax-20]"),
        case(load(RDI, mi(R10, RAX, 1, 0)), "mov rdi, [r10+rax]"),
        case(load(RCX, mi(RBX, R9, 8, -16)), "mov rcx, [rbx+r9*8-16]"),
        case(load(RCX, mi(R13, R12, 4, 0)), "mov rcx, [r13+r12*4]"),
        case(store(m(R12, -8), RCX), "mov [r12-8], rcx"),
        case(store(m(R15, 200), R13), "mov [r15+200], r13"),
        case(store(mi(RBX, RCX, 8, 24), R9), "mov [rbx+rcx*8+24], r9"),
        case(store_imm(m(R15, 72), 0), "mov qword ptr [r15+72], 0"),
        case(store_imm(m(RBX, 8), -5), "mov qword ptr [rbx+8], -5"),
        case(load32(RAX, m(RCX, 4)), "mov eax, [rcx+4]"),
        case(store32(m(RCX, 4), RDX), "mov [rcx+4], edx"),
        case(load32s(RAX, m(RCX, 4)), "movsxd rax, dword ptr [rcx+4]"),
        case(load8(RAX, m(RCX, -7)), "movzx eax, byte ptr [rcx-7]"),
        case(load8(R8, m(R9, 0)), "movzx r8d, byte ptr [r9]"),
        case(mov_imm(RAX, 5), "mov eax, 0x5"),
        case(mov_imm(R8, 0xffff_ffff), "mov r8d, 0xffffffff"),
        case(mov_imm(RCX, (-6i64) as u64), "mov rcx, -6"),
        case(mov_imm(RDX, 0x1_2345_6789), "movabs rdx, 0x123456789"),
        case(mov_imm64(R11, 7), "movabs r11, 0x7"),
        case(lea(RAX, m(RBX, 16)), "lea rax, [rbx+16]"),
        case(lea(R14, mi(R13, RCX, 1, -44)), "lea r14, [r13+rcx-44]"),
        case(cmov(L, RCX, RDX), "cmovl rcx, rdx"),
        case(cmov(E, R8, R11), "cmove r8, r11"),
        case(cmov_m(L, R8, m(R15, 56)), "cmovl r8, [r15+56]"),
        case(add(RCX, RDX), "add rcx, rdx"),
        case(sub(R14, RCX), "sub r14, rcx"),
        case(and(RAX, R9), "and rax, r9"),
        case(or(R8, RCX), "or r8, rcx"),
        case(xor(RDX, RDX), "xor rdx, rdx"),
        case(cmp(RCX, R8), "cmp rcx, r8"),
        case(add_imm(R12, 8), "add r12, 8"),
        case(add_imm(RAX, 0x1000), "add rax, 4096"),
        case(add_imm(RBX, -32), "add rbx, -32"),
        case(sub_imm(R14, 8), "sub r14, 8"),
        case(sub_imm(RCX, 300), "sub rcx, 300"),
        case(and_imm(RCX, 7), "and rcx, 7"),
        case(cmp_imm(RCX, 2), "cmp rcx, 2"),
        case(cmp_imm(R11, 1000), "cmp r11, 1000"),
        case(alu_rm(Alu::Cmp, R12, m(R15, 128)), "cmp r12, [r15+128]"),
        case(alu_rm(Alu::Add, RCX, m(RBX, 0)), "add rcx, [rbx]"),
        case(alu_mr(Alu::Add, m(RBX, 8), RCX), "add [rbx+8], rcx"),
        case(alu_mi(Alu::Sub, m(R15, 64), 1), "sub qword ptr [r15+64], 1"),
        case(alu_mi(Alu::Add, m(RAX, -4), 1000), "add qword ptr [rax-4], 1000"),
        case(test(RCX, RDX), "test rcx, rdx"),
        case(test_imm(RAX, 7), "test eax, 7"),
        case(test_imm(RCX, 7), "test ecx, 7"),
        case(test_imm(R9, 3), "test r9d, 3"),
        case(imul(RCX, RDX), "imul rcx, rdx"),
        case(neg(RCX), "neg rcx"),
        case(not(R8), "not r8"),
        case(cqo(), "cqo"),
        case(idiv(RCX), "idiv rcx"),
        case(shl_imm(RCX, 3), "shl rcx, 3"),
        case(shr_imm(RDX, 1), "shr rdx, 1"),
        case(sar_imm(R8, 3), "sar r8, 3"),
        case(shift_cl(Shift::Sar, RAX), "sar rax, cl"),
        case(movzx8(RAX, RCX), "movzx eax, cl"),
        case(movzx8(RDX, RSI), "movzx edx, sil"),
        case(movzx8(R8, R9), "movzx r8d, r9b"),
        case(setcc(L, RCX), "setl cl"),
        case(setcc(E, RDI), "sete dil"),
        case(jmp_r(RAX), "jmp rax"),
        case(jmp_r(R11), "jmp r11"),
        case(jmp_m(mi(R10, RAX, 1, 0)), "jmp qword ptr [r10+rax]"),
        case(jmp_m(m(R15, 520)), "jmp qword ptr [r15+520]"),
        case(call_r(R11), "call r11"),
        case(call_m(m(R15, 88)), "call qword ptr [r15+88]"),
        case(push(RBX), "push rbx"),
        case(push(R12), "push r12"),
        case(pop(R15), "pop r15"),
        case(push_m(m(R15, 600)), "push qword ptr [r15+600]"),
        case(push_m(m(R12, 0)), "push qword ptr [r12]"),
        case(pop_m(m(R12, 0)), "pop qword ptr [r12]"),
        case(pop_m(m(R15, 600)), "pop qword ptr [r15+600]"),
        case(neg_m(m(RBX, 8)), "neg qword ptr [rbx+8]"),
        case(load_rip(RAX, 100), "mov rax, [rip+100]"),
        case(load16(RAX, m(RDI, 4)), "movzx eax, word ptr [rdi+4]"),
        case(load16(R9, m(R11, 0)), "movzx r9d, word ptr [r11]"),
        case(store8(m(R11, 0), RSI), "mov byte ptr [r11], sil"),
        case(store8(m(RAX, 3), RCX), "mov byte ptr [rax+3], cl"),
        case(store8(m(R11, 1), R14), "mov byte ptr [r11+1], r14b"),
        case(store16(m(R11, 2), RCX), "mov word ptr [r11+2], cx"),
        case(store16(m(RDI, 0), R13), "mov word ptr [rdi], r13w"),
        case(div(RCX), "div rcx"),
        case(div(R14), "div r14"),
        case(movq_to_xmm(0, RAX), "movq xmm0, rax"),
        case(movq_to_xmm(1, R14), "movq xmm1, r14"),
        case(movq_from_xmm(RAX, 0), "movq rax, xmm0"),
        case(movq_from_xmm(R13, 1), "movq r13, xmm1"),
        case(movd_to_xmm(1, RCX), "movd xmm1, ecx"),
        case(movd_from_xmm(RCX, 0), "movd ecx, xmm0"),
        case(fop(true, Fop::Add, 0, 1), "addsd xmm0, xmm1"),
        case(fop(true, Fop::Div, 0, 1), "divsd xmm0, xmm1"),
        case(fop(true, Fop::Sqrt, 0, 0), "sqrtsd xmm0, xmm0"),
        case(fop(false, Fop::Mul, 0, 1), "mulss xmm0, xmm1"),
        case(fop(false, Fop::Sub, 0, 1), "subss xmm0, xmm1"),
        case(ucomis(true, 0, 1), "ucomisd xmm0, xmm1"),
        case(ucomis(false, 1, 0), "ucomiss xmm1, xmm0"),
        case(cvtsi2sd(0, RCX), "cvtsi2sd xmm0, rcx"),
        case(cvtsi2sd(1, R14), "cvtsi2sd xmm1, r14"),
        case(cvttsd2si(RCX, 0), "cvttsd2si rcx, xmm0"),
        case(cvttsd2si(R13, 1), "cvttsd2si r13, xmm1"),
        case(round(true, 0, 0, 1), "roundsd xmm0, xmm0, 1"),
        case(round(false, 0, 1, 3), "roundss xmm0, xmm1, 3"),
        case(load_rip(R14, -4000), "mov r14, [rip-4000]"),
        case(lea_rip(R10, -20), "lea r10, [rip-20]"),
        case(pop(RBP), "pop rbp"),
        case(ret(), "ret"),
        case(ud2(), "ud2"),
        case(int3(), "int3"),
        case(store8_imm(mi(RDX, RCX, 1, 0), 1), "mov byte ptr [rdx+rcx], 1"),
        // Branches: the assembler's `.` is the instruction's start, the
        // encoder's displacement from its end; shown as the byte reached.
        case2(jmp(100), "{disp32} jmp .+105", "jmp @105"),
        case2(jmp(-5), "{disp32} jmp .+0", "jmp @0"),
        case2(jmp8(-2), "jmp .+0", "jmp @0"),
        case2(jcc(Ne, 94), "{disp32} jne .+100", "jne @100"),
        case2(jcc(O, -6), "{disp32} jo .+0", "jo @0"),
        case2(jcc(Be, 0), "{disp32} jbe .+6", "jbe @6"),
        case2(jcc8(L, 10), "jl .+12", "jl @12"),
        case2(call(16), "call .+21", "call @21"),
    ];
    for op in [Alu::Add, Alu::Or, Alu::And, Alu::Sub, Alu::Xor, Alu::Cmp] {
        cases.push(case(alu(op, R9, RBX), &format!("{} r9, rbx", op.name())));
        cases.push(case(alu_imm(op, RAX, 0x12345), &format!("{} rax, 74565", op.name())));
    }
    for c in [O, No, B, Ae, E, Ne, Be, A, S, Ns, L, Ge, Le, G] {
        cases.push(case(cmov(c, RAX, RBX), &format!("cmov{} rax, rbx", c.name())));
    }
    let want = assemble(&cases.iter().map(|(_, t, _)| t.clone()).collect::<Vec<_>>());
    let mut bad = Vec::new();
    for ((ins, text, shown), want) in cases.iter().zip(&want) {
        if &ins[..] != &want[..] {
            bad.push(format!("{text}: encoder {ins:?}, assembler {want:02x?}"));
        }
        let (got, n) = disassemble(ins, 0);
        if got != *shown || n != ins.len() {
            bad.push(format!("{text}: read back as `{got}` ({n} bytes of {})", ins.len()));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// The no-ops of each length, which the assembler writes as it pads.
#[test]
fn nops_are_what_the_assembler_pads_with() {
    for n in 1..=9 {
        let i = nop(n);
        assert_eq!(i.len(), n);
        let (text, len) = disassemble(&i, 0);
        assert_eq!((text.split_whitespace().next(), len), (Some(if n == 2 { "xchg" } else { "nop" }), n), "{i:?}");
    }
    assert_eq!(nops(20).len(), 20);
}

/// The write barrier's sequence, as `arm64::card_mark` does it.
#[test]
fn a_card_mark_reads_back() {
    let code = card_mark(RSI, -20, R15, 400, RCX, RDX);
    let text = fixpt_native::x86_64::disasm::listing(&code);
    for want in ["lea rcx, [rsi-20]", "shr rcx, 9", "mov rdx, [r15+400]", "mov byte ptr [rdx+rcx], 1"] {
        assert!(text.contains(want), "no `{want}` in\n{text}");
    }
}
