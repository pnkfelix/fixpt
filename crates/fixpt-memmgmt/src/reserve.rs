//! Address space reserved up front and made usable piece by piece: what
//! the segmented heap (PLAN.md, "Regions that end") takes its memory from,
//! so that a Value's index is from a base that never moves. And, for
//! finding out what the system allows, the probes `tests/reserve.rs` runs.
//! The heap itself holds [`Words`](crate::Words), which are readable and
//! writable throughout.

/// A range of address space, reserved with no access; parts of it are made
/// readable and writable by [`commit`](Reservation::commit).
pub struct Reservation {
    base: *mut u8,
    len: usize,
}

// SAFETY: the reservation is plain memory owned by whoever holds it.
unsafe impl Send for Reservation {}

impl Reservation {
    /// Reserve `len` bytes of address space, with no access; or none, if
    /// the system refuses.
    pub fn new(len: usize) -> Option<Reservation> {
        let base = map(len, libc::PROT_NONE)?;
        Some(Reservation { base, len })
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The first byte's address.
    pub fn base(&self) -> *mut u8 {
        self.base
    }

    /// Make `len` bytes at `offset` readable and writable (zeroed, as all
    /// anonymous memory starts). Whether the system agreed.
    pub fn commit(&mut self, offset: usize, len: usize) -> bool {
        assert!(offset.checked_add(len).is_some_and(|end| end <= self.len), "within the reservation");
        // SAFETY: inside this reservation, which only this value maps.
        unsafe { libc::mprotect(self.base.add(offset) as *mut libc::c_void, len, libc::PROT_READ | libc::PROT_WRITE) == 0 }
    }

    /// Store `word` at `offset`, which must be committed: for the probes.
    pub fn write_word(&mut self, offset: usize, word: u64) {
        assert!(offset + 8 <= self.len && offset.is_multiple_of(8));
        // SAFETY: inside the reservation and aligned; a fault if not
        // committed, which is what a probe would want to see.
        unsafe { *(self.base.add(offset) as *mut u64) = word };
    }
}

impl Drop for Reservation {
    fn drop(&mut self) {
        // SAFETY: the mapping `new` made, of this length.
        unsafe { libc::munmap(self.base as *mut libc::c_void, self.len) };
    }
}

fn map(len: usize, prot: libc::c_int) -> Option<*mut u8> {
    // SAFETY: an anonymous mapping, used only through what it returns.
    let p = unsafe { libc::mmap(std::ptr::null_mut(), len, prot, libc::MAP_PRIVATE | libc::MAP_ANON, -1, 0) };
    (p != libc::MAP_FAILED).then_some(p as *mut u8)
}

/// Probes of the system's limits.
pub mod probe {
    /// The page size.
    pub fn page() -> usize {
        // SAFETY: a query of a constant.
        unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
    }

    /// Whether `len` bytes can be mapped readable and writable at once
    /// (untouched), as a system that promises memory lazily allows.
    pub fn can_map_writable(len: usize) -> bool {
        match super::map(len, libc::PROT_READ | libc::PROT_WRITE) {
            Some(p) => {
                // SAFETY: the mapping just made.
                unsafe { libc::munmap(p as *mut libc::c_void, len) };
                true
            }
            None => false,
        }
    }
}
