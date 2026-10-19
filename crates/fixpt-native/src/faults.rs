//! Where the machine code faulted, said: with `FIXPT_FAULTS` set, a fault in
//! the code space prints the pc, which installed code it is in and where,
//! and the machine's registers, before the process dies as it would have.
//! For debugging compilers to machine code.

use std::sync::Mutex;

/// Each piece of installed code: its first address, its length in bytes,
/// and what it is.
static PIECES: Mutex<Vec<(usize, usize, String)>> = Mutex::new(Vec::new());

/// `len` bytes of code at `start` are `what`: for a fault there to say,
/// and for profilers to name (`crate::symbols`).
pub fn note(start: usize, len: usize, what: String) {
    crate::symbols::note(start, len, &what);
    if std::env::var_os("FIXPT_FAULTS").is_some() {
        install();
        if let Ok(mut p) = PIECES.lock() {
            p.push((start, len, what));
        }
    }
}

fn install() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        // SAFETY: a handler for the fault signals, which reports and then
        // lets the fault happen again with the default action.
        unsafe {
            let mut sa: libc::sigaction = std::mem::zeroed();
            sa.sa_sigaction = handler as *const () as usize;
            sa.sa_flags = libc::SA_SIGINFO | libc::SA_RESETHAND;
            libc::sigaction(libc::SIGSEGV, &sa, std::ptr::null_mut());
            libc::sigaction(libc::SIGBUS, &sa, std::ptr::null_mut());
        }
    });
}

/// The faulting pc, and the registers by name, from the kernel's ucontext
/// for this thread; `None` where this does not know its layout.
///
/// # Safety
/// `ctx` must be the ucontext a signal handler was given.
unsafe fn registers(ctx: *mut libc::c_void) -> Option<(usize, Vec<(String, u64)>)> {
    let uc = ctx as *mut libc::ucontext_t;
    let xs = |x: &[u64]| x.iter().enumerate().map(|(i, v)| (format!("x{i}"), *v)).collect::<Vec<_>>();
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    // SAFETY: the caller's ucontext (macOS, arm64).
    unsafe {
        let ss = &(*(*uc).uc_mcontext).__ss;
        let mut r = xs(&ss.__x);
        r.extend([("fp".into(), ss.__fp), ("lr".into(), ss.__lr), ("sp".into(), ss.__sp)]);
        Some((ss.__pc as usize, r))
    }
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    // SAFETY: the caller's ucontext (Linux, arm64).
    unsafe {
        let mc = &(*uc).uc_mcontext;
        let mut r = xs(&mc.regs[..29]);
        r.extend([("fp".into(), mc.regs[29]), ("lr".into(), mc.regs[30]), ("sp".into(), mc.sp)]);
        Some((mc.pc as usize, r))
    }
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    // SAFETY: the caller's ucontext (Linux, x86_64).
    unsafe {
        let _ = xs;
        let g = &(*uc).uc_mcontext.gregs;
        let at = |i: libc::c_int| g[i as usize] as u64;
        let names = [
            ("rax", libc::REG_RAX),
            ("rcx", libc::REG_RCX),
            ("rdx", libc::REG_RDX),
            ("rbx", libc::REG_RBX),
            ("rsp", libc::REG_RSP),
            ("rbp", libc::REG_RBP),
            ("rsi", libc::REG_RSI),
            ("rdi", libc::REG_RDI),
            ("r8", libc::REG_R8),
            ("r9", libc::REG_R9),
            ("r10", libc::REG_R10),
            ("r11", libc::REG_R11),
            ("r12", libc::REG_R12),
            ("r13", libc::REG_R13),
            ("r14", libc::REG_R14),
            ("r15", libc::REG_R15),
        ];
        Some((at(libc::REG_RIP) as usize, names.iter().map(|(n, i)| (n.to_string(), at(*i))).collect()))
    }
    #[cfg(not(any(target_arch = "aarch64", all(target_os = "linux", target_arch = "x86_64"))))]
    {
        let _ = (uc, xs);
        None
    }
}

extern "C" fn handler(_sig: libc::c_int, info: *mut libc::siginfo_t, ctx: *mut libc::c_void) {
    // SAFETY: the kernel's siginfo and ucontext for this thread.
    unsafe {
        let addr = (*info).si_addr() as usize;
        let Some((pc, regs)) = registers(ctx) else {
            eprintln!("\nfault at address {addr:#x}");
            return;
        };
        let mut where_ = String::from("outside the code space");
        if let Ok(p) = PIECES.try_lock() {
            if let Some((s, _, w)) = p.iter().find(|(s, l, _)| (*s..s + l).contains(&pc)) {
                where_ = if cfg!(target_arch = "x86_64") { format!("{w}, byte {}", pc - s) } else { format!("{w}, instruction {}", (pc - s) / 4) };
            }
        }
        eprintln!("\nfault at pc {pc:#x} ({where_}), address {addr:#x}");
        for (i, (name, v)) in regs.iter().enumerate() {
            eprint!("{name}={v:#x} ");
            if i % 4 == 3 {
                eprintln!();
            }
        }
        eprintln!();
    }
}
