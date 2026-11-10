//! How much stack the front end's checks take, held to a budget: the front
//! end's own sources, and nesting of a known depth, each checked on a thread
//! of a fixed stack; and, in a debug build on x86_64 Linux, how large each of
//! the checker's frames is, held to `frame-debt.txt`. A debug build makes a
//! frame room for every local of every arm of a `match`, so a dispatcher of
//! many arms takes kilobytes a level of nesting where a release build takes
//! a few hundred bytes, and growth there is what overflows a test's stack
//! first (`debug_stack`, `scripts/debuggers/fixpt_gdb.py`).

use fixpt_fx26::session::compile_program_as;

/// `f` run on a thread of `bytes` of stack.
fn in_stack<T: Send + 'static>(bytes: usize, f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new().stack_size(bytes).spawn(f).expect("a thread").join().expect("no panic, and no overflow")
}

const MIB: usize = 1 << 20;

#[test]
fn the_front_end_checks_in_three_mib() {
    // The measure (2026-11-09): a debug build needs some 2.2 MiB, a release
    // build much less.
    let budget = if cfg!(debug_assertions) { 3 * MIB } else { MIB };
    let r = in_stack(budget, || compile_program_as(&fixpt_fx26::front_end(), "fx:").map(|_| ()).map_err(|e| String::from(e.message)));
    assert_eq!(r, Ok(()));
}

#[test]
fn calls_nested_a_hundred_deep_check_in_two_mib() {
    // `(+ 1 (+ 1 … 0))`: each level a call, its argument the next.
    let depth = 100;
    let program = format!("{}0{}\n", "(+ 1 ".repeat(depth), ")".repeat(depth));
    let budget = if cfg!(debug_assertions) { 2 * MIB } else { MIB / 2 };
    let r = in_stack(budget, move || {
        fixpt_fx26::compare::check_with_rust_checker(&mut fixpt_fx26::Checker::new(), &program).map_err(|e| String::from(e.message))
    });
    assert_eq!(r.map(|v| v.len()), Ok(1));
}

#[test]
fn the_checkers_frames_stay_within_their_debt() {
    if !cfg!(all(debug_assertions, target_arch = "x86_64", target_os = "linux")) {
        eprintln!("frames are measured only in a debug build on x86_64 Linux");
        return;
    }
    let exe = std::env::current_exe().expect("this test's executable");
    let bytes = std::fs::read(&exe).expect("readable");
    let frames = frames::checker_frames(&bytes);
    assert!(frames.len() > 100, "the checker's methods found in {}: {}", exe.display(), frames.len());
    let debt_path = concat!(env!("CARGO_MANIFEST_DIR"), "/frame-debt.txt");
    let debt: std::collections::BTreeMap<String, usize> = std::fs::read_to_string(debt_path)
        .expect("frame-debt.txt")
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .map(|l| {
            let (name, n) = l.rsplit_once(' ').expect("`name bytes`");
            (name.trim().to_string(), n.trim().parse().expect("bytes"))
        })
        .collect();
    let mut wrong = Vec::new();
    for (name, size) in &frames {
        match debt.get(name) {
            Some(d) if size > d => wrong.push(format!("{name}: {size} bytes, worse than its debt ({d}): split it, as `parse_exp` and `synth_node` are")),
            Some(d) if size < d => wrong.push(format!("{name}: now {size} bytes, better than its debt ({d}): lower its entry")),
            Some(_) => {}
            None if *size > frames::LIMIT => wrong.push(format!("{name}: {size} bytes, over {} with no debt: split it", frames::LIMIT)),
            None => {}
        }
    }
    for name in debt.keys().filter(|n| !frames.contains_key(*n)) {
        wrong.push(format!("{name}: in frame-debt.txt, but no such method: remove its entry"));
    }
    assert!(wrong.is_empty(), "the checker's frames, debug build:\n{}", wrong.join("\n"));
}

/// The checker's methods' frames, read from this executable: its ELF symbol
/// table, and the first instructions of each method, which reserve its frame
/// (x86_64's `sub $n, %rsp`, or, past a page, a probe loop's `sub $n, %r11`).
mod frames {
    use std::collections::BTreeMap;

    /// The most a method's debug frame may be with no entry in the debt.
    pub const LIMIT: usize = 4096;

    fn u16_at(b: &[u8], i: usize) -> usize {
        u16::from_le_bytes(b[i..i + 2].try_into().expect("2")) as usize
    }
    fn u32_at(b: &[u8], i: usize) -> usize {
        u32::from_le_bytes(b[i..i + 4].try_into().expect("4")) as usize
    }
    fn u64_at(b: &[u8], i: usize) -> usize {
        u64::from_le_bytes(b[i..i + 8].try_into().expect("8")) as usize
    }

    /// Each `fixpt_fx26::check::Checker` method by name, and its frame in
    /// bytes.
    pub fn checker_frames(elf: &[u8]) -> BTreeMap<String, usize> {
        assert_eq!(&elf[..4], b"\x7fELF", "an ELF file");
        let (shoff, shentsize, shnum) = (u64_at(elf, 0x28), u16_at(elf, 0x3a), u16_at(elf, 0x3c));
        let section = |i: usize| {
            let h = shoff + i * shentsize;
            // (type, address, offset, size, link)
            (u32_at(elf, h + 4), u64_at(elf, h + 0x10), u64_at(elf, h + 0x18), u64_at(elf, h + 0x20), u32_at(elf, h + 0x28))
        };
        let sections: Vec<_> = (0..shnum).map(section).collect();
        let Some(&(_, _, symoff, symsize, strndx)) = sections.iter().find(|s| s.0 == 2) else { return BTreeMap::new() };
        let (_, _, stroff, _, _) = sections[strndx];
        let mut out = BTreeMap::new();
        for k in 0..symsize / 24 {
            let s = symoff + k * 24;
            let (name_at, info, value, size) = (u32_at(elf, s), elf[s + 4], u64_at(elf, s + 8), u64_at(elf, s + 16));
            if info & 0xf != 2 || size == 0 {
                continue;
            }
            let name = cstr(&elf[stroff + name_at..]);
            let Some(method) = checker_method(name) else { continue };
            // The file offset of the code: in the section holding it.
            let Some(&(_, addr, off, _, _)) = sections.iter().find(|(t, addr, _, sz, _)| *t == 1 && *addr <= value && value < addr + sz) else { continue };
            let code = &elf[off + (value - addr)..(off + (value - addr) + size.min(160)).min(elf.len())];
            let n = frame(code);
            let e = out.entry(method).or_insert(0);
            *e = (*e).max(n);
        }
        out
    }

    fn cstr(b: &[u8]) -> &str {
        let n = b.iter().position(|&c| c == 0).unwrap_or(b.len());
        std::str::from_utf8(&b[..n]).unwrap_or("")
    }

    /// `name`, a symbol mangled as Rust's v0 scheme does, the method's name
    /// if it is one of `fixpt_fx26::check::Checker`'s: a value (`Nv`) in an
    /// inherent impl (`M`) of `Checker` in `fixpt_fx26`, not a closure
    /// in one (`NC`) or a generic's instance (`I`); its name the last
    /// identifier, `<length><bytes>`, at the symbol's end.
    fn checker_method(name: &str) -> Option<String> {
        let rest = name.strip_prefix("_RNvM")?;
        // The path's parts may be back-references (`B…_`) to ones before,
        // so `check` need not be spelled out.
        if !(rest.contains("10fixpt_fx26") && rest.contains("7Checker")) {
            return None;
        }
        let b = rest.as_bytes();
        for j in (1..b.len()).rev() {
            if !b[j].is_ascii_digit() || b[j - 1].is_ascii_digit() {
                continue;
            }
            let digits = b[j..].iter().take_while(|c| c.is_ascii_digit()).count();
            let n: usize = rest[j..j + digits].parse().ok()?;
            if j + digits + n == b.len() {
                return Some(rest[j + digits..].to_string());
            }
        }
        None
    }

    /// The bytes a function's prologue, `code`, reserves: from its first
    /// `sub` of the stack pointer, a probed frame's `sub $n, %r11`, else
    /// each `sub $n, %rsp` in a row, a page's probe (`movq $0, (%rsp)`)
    /// between them.
    fn frame(code: &[u8]) -> usize {
        let at = |i: usize, p: &[u8]| code.get(i..i + p.len()) == Some(p);
        let Some(mut i) = (0..code.len().min(48)).find(|&i| at(i, &[0x49, 0x81, 0xeb]) || at(i, &[0x48, 0x81, 0xec]) || at(i, &[0x48, 0x83, 0xec])) else {
            return 0;
        };
        if at(i, &[0x49, 0x81, 0xeb]) {
            return u32_at(code, i + 3);
        }
        let mut n = 0;
        loop {
            if at(i, &[0x48, 0x81, 0xec]) && i + 7 <= code.len() {
                n += u32_at(code, i + 3);
                i += 7;
            } else if at(i, &[0x48, 0x83, 0xec]) && i + 4 <= code.len() {
                n += code[i + 3] as usize;
                i += 4;
            } else if at(i, &[0x48, 0xc7, 0x04, 0x24, 0, 0, 0, 0]) {
                i += 8;
            } else {
                return n;
            }
        }
    }
}
