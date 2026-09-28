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
    #[cfg(target_os = "macos")]
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
        let mut alias: u64 = 0;
        let (mut cur, mut max) = (0, 0);
        // SAFETY: remaps the shared mapping just made into a fresh address
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
        // SAFETY: `alias` is the mapping just made, `bytes` long.
        if unsafe { libc::mprotect(alias as *mut libc::c_void, bytes, libc::PROT_READ | libc::PROT_EXEC) } != 0 {
            let e = io::Error::last_os_error();
            // SAFETY: unmapping the view made above.
            unsafe { libc::munmap(alias as *mut libc::c_void, bytes) };
            return Err(e);
        }
        Ok(ExecView { rw: rw as usize, rx: alias as usize, bytes })
    }

    #[cfg(not(target_os = "macos"))]
    pub fn exec_view(&mut self, _range: Range<usize>) -> io::Result<ExecView> {
        Err(io::Error::new(io::ErrorKind::Unsupported, "an execute view is made only on macOS so far"))
    }
}

impl ExecView {
    /// The executable address of the byte at `rw`, an address in the
    /// heap's own view of the range.
    pub fn exec_address(&self, rw: usize) -> usize {
        assert!((self.rw..self.rw + self.bytes).contains(&rw), "an address in the viewed range");
        rw - self.rw + self.rx
    }

    /// After instructions are written at `rw..rw + len` (heap addresses):
    /// make the instruction cache see them at their executable address.
    /// Fields are data, and need none of this.
    pub fn flush(&self, rw: usize, len: usize) {
        let at = self.exec_address(rw);
        assert!(rw + len <= self.rw + self.bytes, "within the viewed range");
        #[cfg(target_os = "macos")]
        // SAFETY: a range of this view, which is mapped while it lives.
        unsafe {
            sys_icache_invalidate(at as *mut libc::c_void, len)
        };
        #[cfg(not(target_os = "macos"))]
        let _ = at;
    }
}

impl Drop for ExecView {
    fn drop(&mut self) {
        // SAFETY: the view `exec_view` mapped, this long; the shared pages
        // it names stay mapped in the heap's words.
        unsafe { libc::munmap(self.rx as *mut libc::c_void, self.bytes) };
    }
}
