//! A second, read+execute view of part of a heap's words, for the code area
//! (`docs/object-model.md`, "A collected code area"): the heap writes code
//! and fields through its own read+write view, and code runs from this one.
//! No address is ever both writable and executable, and nothing is ever
//! re-protected; the two views are the same pages at a fixed distance.
//!
//! Only a *shared* mapping can be mapped twice so that both views see the
//! same pages, and a heap's words are a private mapping, so the range is
//! first replaced by a shared anonymous mapping, zero, as it was. Done once,
//! for the whole range, before anything is written there: nothing is
//! committed until touched, so the view never has to grow.

use crate::Words;
use std::io;
use std::ops::Range;

#[cfg(target_os = "macos")]
unsafe extern "C" {
    fn sys_icache_invalidate(start: *mut libc::c_void, len: usize);
    fn mach_task_self() -> libc::mach_port_t;
    fn mach_vm_remap(
        target: libc::mach_port_t,
        target_addr: *mut u64,
        size: u64,
        mask: u64,
        flags: libc::c_int,
        src_task: libc::mach_port_t,
        src_addr: u64,
        copy: libc::boolean_t,
        cur: *mut libc::c_int,
        max: *mut libc::c_int,
        inherit: libc::c_uint,
    ) -> libc::c_int;
}

#[cfg(target_os = "macos")]
const VM_FLAGS_ANYWHERE: libc::c_int = 1;
#[cfg(target_os = "macos")]
const VM_INHERIT_SHARE: libc::c_uint = 1;

/// Map a second, read+execute view of the `bytes` bytes of the *shared*
/// mapping at `rw`, at an address the kernel chooses, and return it. The
/// views share their pages for as long as both are mapped.
///
/// # Safety
/// `rw..rw + bytes` must be (part of) a shared mapping, page-aligned.
pub unsafe fn map_exec_alias(rw: *mut libc::c_void, bytes: usize) -> io::Result<*mut libc::c_void> {
    #[cfg(target_os = "macos")]
    let alias = {
        let mut alias: u64 = 0;
        let (mut cur, mut max) = (0, 0);
        // SAFETY: remaps the caller's shared mapping into a fresh address
        // the kernel chooses (VM_FLAGS_ANYWHERE), sharing the same pages.
        let kr = unsafe {
            mach_vm_remap(
                mach_task_self(),
                &mut alias,
                bytes as u64,
                0,
                VM_FLAGS_ANYWHERE,
                mach_task_self(),
                rw as u64,
                0,
                &mut cur,
                &mut max,
                VM_INHERIT_SHARE,
            )
        };
        if kr != 0 {
            return Err(io::Error::other(format!("mach_vm_remap failed: {kr}")));
        }
        alias as *mut libc::c_void
    };
    #[cfg(target_os = "linux")]
    let alias = {
        // SAFETY: an old size of zero asks for a new mapping of the same
        // pages, which the kernel allows only of a shared mapping (the
        // caller's); MREMAP_MAYMOVE lets it choose where.
        let alias = unsafe { libc::mremap(rw, 0, bytes, libc::MREMAP_MAYMOVE) };
        if alias == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }
        alias
    };
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    let alias: *mut libc::c_void = {
        let _ = (rw, bytes);
        return Err(io::Error::new(io::ErrorKind::Unsupported, "an execute view is made only on macOS and Linux"));
    };
    // SAFETY: `alias` is the mapping just made, `bytes` long.
    if unsafe { libc::mprotect(alias, bytes, libc::PROT_READ | libc::PROT_EXEC) } != 0 {
        let e = io::Error::last_os_error();
        // SAFETY: unmapping the view made above.
        unsafe { libc::munmap(alias, bytes) };
        return Err(e);
    }
    Ok(alias)
}

/// After instructions are written at `at..at + len`: make instruction fetch
/// at those (executable) addresses see them.
///
/// # Safety
/// The range must be mapped.
pub unsafe fn flush_icache(at: *mut libc::c_void, len: usize) {
    #[cfg(target_os = "macos")]
    // SAFETY: the caller promises the range is mapped.
    unsafe {
        sys_icache_invalidate(at, len)
    };
    #[cfg(all(not(target_os = "macos"), target_arch = "aarch64"))]
    // SAFETY: as above. Cache maintenance by address on mapped memory, what
    // compiler-rt's `__clear_cache` does: clean each data-cache line to the
    // point of unification, then invalidate each instruction-cache line.
    unsafe {
        let ctr: u64;
        std::arch::asm!("mrs {}, ctr_el0", out(reg) ctr, options(nomem, nostack));
        let dline = 4usize << ((ctr >> 16) & 15);
        let iline = 4usize << (ctr & 15);
        let (start, end) = (at as usize, at as usize + len);
        let mut a = start & !(dline - 1);
        while a < end {
            std::arch::asm!("dc cvau, {}", in(reg) a, options(nostack));
            a += dline;
        }
        std::arch::asm!("dsb ish", options(nostack));
        let mut a = start & !(iline - 1);
        while a < end {
            std::arch::asm!("ic ivau, {}", in(reg) a, options(nostack));
            a += iline;
        }
        std::arch::asm!("dsb ish", "isb", options(nostack));
    }
    // Elsewhere (x86) instruction fetch sees stores without being told.
    #[cfg(all(not(target_os = "macos"), not(target_arch = "aarch64")))]
    let _ = (at, len);
}

/// The read+execute view of a range of words. Dropping it unmaps the view;
/// the words themselves stay the heap's.
pub struct ExecView {
    /// Where the range's first word is, in each view.
    rw: usize,
    rx: usize,
    bytes: usize,
}

// SAFETY: the view is plain memory owned by whoever holds this value.
unsafe impl Send for ExecView {}

impl Words {
    /// Give words `range` a read+execute view. Their contents are replaced
    /// by zero, so this is for a range nothing has been written in yet. The
    /// range must start and end on page boundaries.
    pub fn exec_view(&mut self, range: Range<usize>) -> io::Result<ExecView> {
        let page = crate::reserve::probe::page();
        assert!(range.start <= range.end && range.end <= self.len, "within the words");
        let (start, bytes) = (range.start * 8, (range.end - range.start) * 8);
        assert!(start % page == 0 && bytes % page == 0, "a whole number of pages");
        // SAFETY: the range is inside this mapping, which nothing else
        // refers into; MAP_FIXED replaces exactly those pages with a shared
        // anonymous mapping, zero, as they were.
        let rw = unsafe {
            libc::mmap(
                (self.base as *mut u8).add(start) as *mut libc::c_void,
                bytes,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_FIXED | libc::MAP_SHARED | libc::MAP_ANON,
                -1,
                0,
            )
        };
        if rw == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: `rw` is the shared mapping just made, page-aligned.
        let rx = unsafe { map_exec_alias(rw, bytes)? };
        Ok(ExecView { rw: rw as usize, rx: rx as usize, bytes })
    }
}

impl ExecView {
    /// The executable address of the byte at `rw`, an address in the
    /// heap's own view of the range.
    pub fn exec_address(&self, rw: usize) -> usize {
        assert!((self.rw..self.rw + self.bytes).contains(&rw), "an address in the viewed range");
        rw - self.rw + self.rx
    }

    /// The read+execute view of the bytes from `rw` (a heap address, on a
    /// page) made `file`'s bytes `part`, mapped privately from the file, as
    /// [`Words::map_from`] maps the heap's own view: for code that is never
    /// written afterwards, so that the two views, each the file's, agree.
    /// The heap's view must be mapped so too, read-only. Linux only: false
    /// elsewhere, and wherever it cannot be, nothing changed.
    pub fn map_from(&self, rw: usize, file: &crate::Mapped, part: &[u8]) -> bool {
        let bytes = part.len().div_ceil(crate::reserve::probe::page()) * crate::reserve::probe::page();
        if !cfg!(target_os = "linux") || rw < self.rw || rw.checked_add(bytes).is_none_or(|e| e > self.rw + self.bytes) {
            return false;
        }
        // SAFETY: whole pages of this view, which is mapped while it lives;
        // what runs there is replaced by the same bytes (the caller's).
        unsafe { file.map_over(part, self.exec_address(rw) as *mut u8, libc::PROT_READ | libc::PROT_EXEC) }
    }

    /// After instructions are written at `rw..rw + len` (heap addresses):
    /// make the instruction cache see them at their executable address.
    /// Fields are data, and need none of this.
    pub fn flush(&self, rw: usize, len: usize) {
        let at = self.exec_address(rw);
        assert!(rw + len <= self.rw + self.bytes, "within the viewed range");
        // SAFETY: a range of this view, which is mapped while it lives.
        unsafe { flush_icache(at as *mut libc::c_void, len) };
    }
}

impl Drop for ExecView {
    fn drop(&mut self) {
        // SAFETY: the view `exec_view` mapped, this long; the shared pages
        // it names stay mapped in the heap's words.
        unsafe { libc::munmap(self.rx as *mut libc::c_void, self.bytes) };
    }
}

#[cfg(test)]
mod tests {
    use crate::Words;

    /// The two views are the same pages: a word written through the heap's
    /// is read through the executable one. Nothing runs, so on any machine.
    #[test]
    fn the_views_share_their_pages() {
        let per_page = crate::reserve::probe::page() / 8;
        let mut w = Words::new(4 * per_page).expect("address space");
        let view = w.exec_view(per_page..3 * per_page).expect("an execute view");
        let at = per_page + 5;
        w.words_mut()[at] = 0xfeed_f00d;
        let rw = w.words().as_ptr() as usize + 8 * at;
        let rx = view.exec_address(rw);
        assert_ne!(rx, rw);
        // SAFETY: an aligned word inside the view, which is readable.
        assert_eq!(unsafe { (rx as *const u64).read_volatile() }, 0xfeed_f00d);
        view.flush(rw, 8);
    }
}
