//! A file's bytes, mapped read-only rather than read into a buffer: for an
//! image read once from start to end, the page cache's pages themselves,
//! with no copy into memory of the process's own (`TODO.md` §160).

use std::io;

/// The bytes of a file, mapped privately and read-only. Dropping them
/// unmaps them.
pub struct Mapped {
    base: *const u8,
    len: usize,
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
            return Ok(Mapped { base: std::ptr::NonNull::dangling().as_ptr(), len });
        }
        // SAFETY: a fresh read-only private mapping of an open file, used
        // only through this value; the descriptor may close once mapped.
        let p = unsafe { libc::mmap(std::ptr::null_mut(), len, libc::PROT_READ, libc::MAP_PRIVATE, f.as_raw_fd(), 0) };
        if p == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }
        #[cfg(target_os = "linux")]
        // SAFETY: advice on the mapping just made; its contents are unchanged.
        unsafe {
            libc::madvise(p, len, libc::MADV_SEQUENTIAL | libc::MADV_WILLNEED)
        };
        Ok(Mapped { base: p as *const u8, len })
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
