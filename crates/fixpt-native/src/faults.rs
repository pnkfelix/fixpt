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

extern "C" fn handler(_sig: libc::c_int, info: *mut libc::siginfo_t, ctx: *mut libc::c_void) {
    // SAFETY: the kernel's ucontext for this thread (macOS, arm64).
    unsafe {
        let uc = ctx as *mut libc::ucontext_t;
        let ss = &(*(*uc).uc_mcontext).__ss;
        let pc = ss.__pc as usize;
        let addr = (*info).si_addr as usize;
        let mut where_ = String::from("outside the code space");
        if let Ok(p) = PIECES.try_lock() {
            if let Some((s, _, w)) = p.iter().find(|(s, l, _)| (*s..s + l).contains(&pc)) {
                where_ = format!("{w}, instruction {}", (pc - s) / 4);
            }
        }
        eprintln!("\nfault at pc {pc:#x} ({where_}), address {addr:#x}");
        for (i, x) in ss.__x.iter().enumerate() {
            eprint!("x{i}={x:#x} ");
            if i % 4 == 3 {
                eprintln!();
            }
        }
        eprintln!("fp={:#x} lr={:#x} sp={:#x}", ss.__fp, ss.__lr, ss.__sp);
    }
}
