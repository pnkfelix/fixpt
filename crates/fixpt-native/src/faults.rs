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

/// The faulting pc, the 29 general registers, and fp, lr and sp, from the
/// kernel's ucontext for this thread; `None` where that is not arm64.
///
/// # Safety
/// `ctx` must be the ucontext a signal handler was given.
unsafe fn registers(ctx: *mut libc::c_void) -> Option<(usize, [u64; 29], [u64; 3])> {
    let uc = ctx as *mut libc::ucontext_t;
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    // SAFETY: the caller's ucontext (macOS, arm64).
    unsafe {
        let ss = &(*(*uc).uc_mcontext).__ss;
        Some((ss.__pc as usize, ss.__x, [ss.__fp, ss.__lr, ss.__sp]))
    }
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    // SAFETY: the caller's ucontext (Linux, arm64).
    unsafe {
        let mc = &(*uc).uc_mcontext;
        let mut x = [0; 29];
        x.copy_from_slice(&mc.regs[..29]);
        Some((mc.pc as usize, x, [mc.regs[29], mc.regs[30], mc.sp]))
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = uc;
        None
    }
}

extern "C" fn handler(_sig: libc::c_int, info: *mut libc::siginfo_t, ctx: *mut libc::c_void) {
    // SAFETY: the kernel's siginfo and ucontext for this thread.
    unsafe {
        let addr = (*info).si_addr() as usize;
        let Some((pc, xs, [fp, lr, sp])) = registers(ctx) else {
            eprintln!("\nfault at address {addr:#x}");
            return;
        };
        let mut where_ = String::from("outside the code space");
        if let Ok(p) = PIECES.try_lock() {
            if let Some((s, _, w)) = p.iter().find(|(s, l, _)| (*s..s + l).contains(&pc)) {
                where_ = format!("{w}, instruction {}", (pc - s) / 4);
            }
        }
        eprintln!("\nfault at pc {pc:#x} ({where_}), address {addr:#x}");
        for (i, x) in xs.iter().enumerate() {
            eprint!("x{i}={x:#x} ");
            if i % 4 == 3 {
                eprintln!();
            }
        }
        eprintln!("fp={fp:#x} lr={lr:#x} sp={sp:#x}");
    }
}
