//! The code space: memory that holds machine code, mapped twice.
//!
//! One mapping is read+write and is where code (and the fields of a code
//! bloblet) are written; the other is read+execute and is where code runs from.
//! No address is ever both writable and executable, yet nothing is ever
//! re-protected either: a field can be written while its code runs, which is
//! exactly the "mutable fields, immutable suffix" bloblet the object model asks
//! for (`docs/object-model.md`, "What this machine allows"). The measurement
//! that chose this over `mprotect` and over `MAP_JIT` toggling is there too.
//!
//! The space does not move and does not grow: code addresses are baked into
//! other code and into return addresses, so a routine stays where it was put.
//! When one space fills, the caller makes another.

use std::io;

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

const VM_FLAGS_ANYWHERE: libc::c_int = 1;
const VM_INHERIT_SHARE: libc::c_uint = 1;

/// An offset into a code space. The same offset names a byte in both views.
pub type Offset = usize;

pub struct CodeSpace {
    rw: *mut u8,
    rx: *const u8,
    size: usize,
    top: usize,
}

// The views are plain memory owned by this value; nothing else aliases them.
unsafe impl Send for CodeSpace {}

fn page() -> usize {
    // SAFETY: sysconf has no preconditions.
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
}

impl CodeSpace {
    /// Map a space of at least `bytes` bytes, rounded up to whole pages.
    pub fn new(bytes: usize) -> io::Result<CodeSpace> {
        let p = page();
        let size = bytes.max(1).div_ceil(p) * p;
        // SAFETY: a fresh anonymous shared mapping; nothing else refers to it.
        let rw = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED | libc::MAP_ANON,
                -1,
                0,
            )
        };
        if rw == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }
        let mut alias: u64 = 0;
        let (mut cur, mut max) = (0, 0);
        // SAFETY: remaps the mapping just made, into a fresh address chosen by
        // the kernel (VM_FLAGS_ANYWHERE), sharing the same pages.
        let kr = unsafe {
            mach_vm_remap(
                mach_task_self(),
                &mut alias,
                size as u64,
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
            // SAFETY: unmapping what was mapped above.
            unsafe { libc::munmap(rw, size) };
            return Err(io::Error::other(format!("mach_vm_remap failed: {kr}")));
        }
        // SAFETY: `alias` is the mapping just made, `size` long.
        let r = unsafe { libc::mprotect(alias as *mut _, size, libc::PROT_READ | libc::PROT_EXEC) };
        if r != 0 {
            let e = io::Error::last_os_error();
            // SAFETY: unmapping both views made above.
            unsafe {
                libc::munmap(alias as *mut _, size);
                libc::munmap(rw, size);
            }
            return Err(e);
        }
        Ok(CodeSpace { rw: rw as *mut u8, rx: alias as *const u8, size, top: 0 })
    }

    pub fn size(&self) -> usize {
        self.size
    }

    /// Bytes handed out so far.
    pub fn used(&self) -> usize {
        self.top
    }

    /// Reserve `len` bytes aligned to `align` (a power of two), or `None`
    /// if the space is full. The bytes are zero until written.
    pub fn alloc(&mut self, len: usize, align: usize) -> Option<Offset> {
        debug_assert!(align.is_power_of_two());
        let at = self.top.checked_add(align - 1)? & !(align - 1);
        let end = at.checked_add(len)?;
        if end > self.size {
            return None;
        }
        self.top = end;
        Some(at)
    }

    fn check(&self, at: Offset, len: usize) {
        assert!(at.checked_add(len).is_some_and(|e| e <= self.top), "code space access {at}+{len} past {}", self.top);
    }

    /// Write bytes through the read+write view. Code written this way is not
    /// runnable until [`CodeSpace::flush`] has covered it.
    pub fn write(&mut self, at: Offset, bytes: &[u8]) {
        self.check(at, bytes.len());
        // SAFETY: in bounds (checked), and the RW view is ours.
        unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), self.rw.add(at), bytes.len()) };
    }

    /// Write instructions.
    pub fn write_code(&mut self, at: Offset, code: &[u32]) {
        self.write(at, &crate::arm64::bytes(code));
    }

    /// Write a word, 8-aligned. Words are what bloblet fields are, so this is
    /// how a field of a code bloblet changes while its code may be running.
    pub fn write_u64(&mut self, at: Offset, v: u64) {
        assert!(at.is_multiple_of(8));
        self.check(at, 8);
        // SAFETY: in bounds and aligned; a single store, so a concurrent
        // reader sees the old word or the new one.
        unsafe { (self.rw.add(at) as *mut u64).write_volatile(v) };
    }

    pub fn read_u64(&self, at: Offset) -> u64 {
        assert!(at.is_multiple_of(8));
        self.check(at, 8);
        // SAFETY: in bounds and aligned.
        unsafe { (self.rw.add(at) as *const u64).read_volatile() }
    }

    pub fn read_u32(&self, at: Offset) -> u32 {
        assert!(at.is_multiple_of(4));
        self.check(at, 4);
        // SAFETY: in bounds and aligned.
        unsafe { (self.rw.add(at) as *const u32).read_volatile() }
    }

    /// Make code written in `at..at+len` visible to instruction fetch. Needed
    /// after writing code, not after writing data fields.
    pub fn flush(&self, at: Offset, len: usize) {
        self.check(at, len);
        // SAFETY: the range is inside the RX view.
        unsafe { sys_icache_invalidate(self.rx.add(at) as *mut _, len) };
    }

    /// The address `at` has in the executable view: what a branch, a return
    /// address or a cellular-code cell holds.
    pub fn exec_addr(&self, at: Offset) -> usize {
        self.check(at, 0);
        self.rx as usize + at
    }

    /// The offset an executable address names, if it is in this space.
    pub fn offset_of(&self, addr: usize) -> Option<Offset> {
        let base = self.rx as usize;
        (addr >= base && addr < base + self.size).then(|| addr - base)
    }

    /// The address `at` has in the writable view, for code that runs in the
    /// space and writes its own fields. Never executable.
    pub fn data_addr(&self, at: Offset) -> usize {
        self.check(at, 0);
        self.rw as usize + at
    }

    /// Call the routine at `at` with the C calling convention: up to four
    /// word arguments in, one word out.
    ///
    /// # Safety
    /// The bytes at `at` must be a flushed routine that follows the C calling
    /// convention, takes at most four word arguments, and touches only memory
    /// that is valid while it runs.
    pub unsafe fn call(&self, at: Offset, args: [u64; 4]) -> u64 {
        self.check(at, 4);
        // SAFETY: the caller promises this is such a routine.
        let f: extern "C" fn(u64, u64, u64, u64) -> u64 = unsafe { std::mem::transmute(self.rx.add(at)) };
        f(args[0], args[1], args[2], args[3])
    }
}

impl CodeSpace {
    /// Call a routine of the stencil machines' kind: eight word arguments in
    /// registers, one word out.
    ///
    /// # Safety
    /// As for [`CodeSpace::call`], for a routine with that signature.
    pub unsafe fn call8(&self, at: Offset, args: [u64; 8]) -> u64 {
        self.check(at, 4);
        type R8 = extern "C" fn(u64, u64, u64, u64, u64, u64, u64, u64) -> u64;
        // SAFETY: the caller promises this is such a routine.
        let f: R8 = unsafe { std::mem::transmute(self.rx.add(at)) };
        let [a, b, c, d, e, g, h, i] = args;
        f(a, b, c, d, e, g, h, i)
    }
}

impl Drop for CodeSpace {
    fn drop(&mut self) {
        // SAFETY: both views were mapped by `new`, `size` long, and nothing
        // made by this space outlives it.
        unsafe {
            libc::munmap(self.rx as *mut _, self.size);
            libc::munmap(self.rw as *mut _, self.size);
        }
    }
}
