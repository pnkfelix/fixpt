//! A file's bytes, mapped read-only rather than read into a buffer: for an
//! image read once from start to end, the page cache's pages themselves,
//! with no copy into memory of the process's own (`TODO.md` §160).

use std::io;

/// The bytes of a file, mapped privately and read-only. Dropping them
/// unmaps them.
pub struct Mapped {
    base: *const u8,
    len: usize,
    /// The file, for mapping parts of it elsewhere ([`map_over`](Mapped::map_over)).
    file: Option<std::fs::File>,
}

// SAFETY: a read-only mapping owned by whoever holds this value.
unsafe impl Send for Mapped {}

impl Mapped {
    /// The whole of the file at `path`. A file someone writes while it is
    /// mapped is seen to change; the files mapped here are replaced by a
    /// rename, never written in place.
    pub fn open(path: &std::path::Path) -> io::Result<Mapped> {
        use std::os::fd::AsRawFd as _;
        let f = std::fs::File::open(path)?;
        let len = usize::try_from(f.metadata()?.len()).map_err(io::Error::other)?;
        if len == 0 {
            return Ok(Mapped { base: std::ptr::NonNull::dangling().as_ptr(), len, file: None });
        }
        // SAFETY: a fresh read-only private mapping of an open file, used
        // only through this value.
        let p = unsafe { libc::mmap(std::ptr::null_mut(), len, libc::PROT_READ, libc::MAP_PRIVATE, f.as_raw_fd(), 0) };
        if p == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }
        #[cfg(target_os = "linux")]
        // SAFETY: advice on the mapping just made; its contents are unchanged.
        unsafe {
            libc::madvise(p, len, libc::MADV_SEQUENTIAL | libc::MADV_WILLNEED)
        };
        Ok(Mapped { base: p as *const u8, len, file: Some(f) })
    }

    /// The part `part` of these bytes (a slice of them) mapped over the
    /// memory at `to`, privately: what is written there afterwards is the
    /// process's own copy, page by page, and the file is not written. The
    /// whole pages that hold it, `part` from a page's start, `to` on one;
    /// what the last page holds past `part` is the file's too (zeros, where
    /// the file is laid out for it). Protected as `prot` says. False, and
    /// nothing changed, where it cannot be ([`can_map`](Mapped::can_map)).
    /// For [`Words::map_from`](crate::Words::map_from) and
    /// [`ExecView::map_from`](crate::ExecView::map_from).
    ///
    /// # Safety
    ///
    /// The memory at `to`, the pages `part` spans, must be this process's,
    /// mapped already (a reservation's), and nothing may hold a reference
    /// into it while it is replaced.
    pub(crate) unsafe fn map_over(&self, part: &[u8], to: *mut u8, prot: libc::c_int) -> bool {
        use std::os::fd::AsRawFd as _;
        let Some(f) = &self.file else { return false };
        if !self.can_map(part) || !(to as usize).is_multiple_of(crate::reserve::probe::page()) {
            return false;
        }
        let offset = part.as_ptr() as usize - self.base as usize;
        let len = part.len().div_ceil(crate::reserve::probe::page()) * crate::reserve::probe::page();
        // SAFETY: the caller's: `to` is this process's mapped memory, which
        // a fixed mapping replaces; the file is open, `offset` a page's.
        let p = unsafe { libc::mmap(to as *mut libc::c_void, len, prot, libc::MAP_PRIVATE | libc::MAP_FIXED, f.as_raw_fd(), offset as libc::off_t) };
        p == to as *mut libc::c_void
    }

    /// Whether `part`, a slice of these bytes, may be mapped elsewhere
    /// ([`map_over`](Mapped::map_over)): not empty, from a page's start in
    /// the file.
    pub fn can_map(&self, part: &[u8]) -> bool {
        let offset = (part.as_ptr() as usize).wrapping_sub(self.base as usize);
        let inside = offset <= self.len && part.len() <= self.len - offset;
        self.file.is_some() && inside && !part.is_empty() && offset.is_multiple_of(crate::reserve::probe::page())
    }
}

impl std::ops::Deref for Mapped {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        // SAFETY: `len` readable bytes, mapped while this value lives.
        unsafe { std::slice::from_raw_parts(self.base, self.len) }
    }
}

impl Drop for Mapped {
    fn drop(&mut self) {
        if self.len > 0 {
            // SAFETY: the mapping `open` made, of this many bytes.
            unsafe { libc::munmap(self.base as *mut libc::c_void, self.len) };
        }
    }
}
