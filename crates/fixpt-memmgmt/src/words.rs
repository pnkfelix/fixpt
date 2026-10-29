//! A heap's words: a large range of address space, readable and writable
//! throughout, whose pages the system commits as they are first written.
//! Held as a slice, so that reading and writing a word costs what indexing
//! a `Vec` does.

/// `len` words at a fixed address, zero until written. Dropping them gives
/// the range back.
pub struct Words {
    pub(crate) base: *mut u64,
    pub(crate) len: usize,
}

// SAFETY: the words are plain memory owned by whoever holds this value.
unsafe impl Send for Words {}

impl Words {
    /// `len` words of address space, readable and writable, zero; or none,
    /// if the system refuses the range. Nothing is committed until written.
    pub fn new(len: usize) -> Option<Words> {
        let bytes = len.checked_mul(8)?.max(8);
        // SAFETY: an anonymous mapping, used only through this value.
        let p = unsafe {
            libc::mmap(std::ptr::null_mut(), bytes, libc::PROT_READ | libc::PROT_WRITE, libc::MAP_PRIVATE | libc::MAP_ANON, -1, 0)
        };
        (p != libc::MAP_FAILED).then_some(Words { base: p as *mut u64, len })
    }

    /// The same, at address `at` exactly; or none, if the system will not
    /// put them there (something is there already, or the address is past
    /// what the process may map). Nothing there is replaced.
    pub fn new_at(len: usize, at: usize) -> Option<Words> {
        let bytes = len.checked_mul(8)?.max(8);
        #[cfg(target_os = "linux")]
        let flags = libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_FIXED_NOREPLACE;
        // Elsewhere the address is a hint, taken or not.
        #[cfg(not(target_os = "linux"))]
        let flags = libc::MAP_PRIVATE | libc::MAP_ANON;
        // SAFETY: an anonymous mapping, used only through this value; with
        // no `MAP_FIXED`, nothing already mapped is replaced.
        let p = unsafe { libc::mmap(at as *mut libc::c_void, bytes, libc::PROT_READ | libc::PROT_WRITE, flags, -1, 0) };
        if p == libc::MAP_FAILED {
            return None;
        }
        let w = Words { base: p as *mut u64, len };
        // A kernel that knows no `MAP_FIXED_NOREPLACE` takes it as a hint.
        (p as usize == at).then_some(w)
    }

    /// Ask the system to commit these words in huge pages (2 MiB on
    /// x86_64) where it can: a page first written costs one fault for 512
    /// of the usual size, and its translation one TLB entry. On Linux, where
    /// transparent huge pages are on for those that ask (`madvise`, as a
    /// rule); elsewhere, or if the system declines, nothing changes. Memory
    /// is committed 2 MiB at a time, so for a heap's words, written
    /// densely, not for a sparse table.
    pub fn prefer_huge_pages(&mut self) {
        #[cfg(target_os = "linux")]
        // SAFETY: advice on this mapping, which stays mapped and readable;
        // its contents are unchanged.
        unsafe {
            libc::madvise(self.base as *mut libc::c_void, self.len * 8, libc::MADV_HUGEPAGE)
        };
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn words(&self) -> &[u64] {
        // SAFETY: the mapping is `len` words, readable and writable
        // throughout (an untouched page reads as zero), and only this value
        // hands out references to it, borrowed from it.
        unsafe { std::slice::from_raw_parts(self.base, self.len) }
    }

    #[inline]
    pub fn words_mut(&mut self) -> &mut [u64] {
        // SAFETY: as for `words`, and `&mut self` makes this the only
        // reference.
        unsafe { std::slice::from_raw_parts_mut(self.base, self.len) }
    }

    /// Tell the system that the words in `range` hold nothing wanted: it may
    /// take their pages back, and they read as zero, or as they were, until
    /// written. For space a collection has emptied. Whole pages only; the
    /// rest of the range is left as it is.
    pub fn release(&mut self, range: std::ops::Range<usize>) {
        assert!(range.start <= range.end && range.end <= self.len, "within the words");
        let page = crate::reserve::probe::page();
        let (start, end) = (range.start * 8, range.end * 8);
        let first = start.div_ceil(page) * page;
        let last = end / page * page;
        if first < last {
            // SAFETY: whole pages inside this mapping, which `&mut self`
            // holds no reference into while this runs; they stay mapped
            // and readable, so the slice over them stays valid.
            unsafe { libc::madvise((self.base as *mut u8).add(first) as *mut libc::c_void, last - first, libc::MADV_FREE) };
        }
    }
}

impl Drop for Words {
    fn drop(&mut self) {
        // SAFETY: the mapping `new` made, of this many words.
        unsafe { libc::munmap(self.base as *mut libc::c_void, (self.len * 8).max(8)) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn words_start_zero_and_hold_what_is_written() {
        let mut w = Words::new(1 << 30).expect("8 GB of address space");
        assert_eq!(w.words()[12345], 0);
        w.words_mut()[12345] = 7;
        w.words_mut()[(1 << 30) - 1] = 9;
        assert_eq!(w.words()[12345], 7);
        assert_eq!(w.words()[(1 << 30) - 1], 9);
        w.release(0..1 << 20);
        let _ = w.words()[12345];
    }
}
