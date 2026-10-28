//! Heap images: dump, load, and the three shipping modes.
//!
//! Larceny's heap format got the essential idea right — write the roots and the
//! heap words with every reference expressed relative to base 0, so loading is a
//! read rather than a relocation pass. This is that idea with the variants
//! removed: Larceny has bootstrap-single, bootstrap-split and dumped forms; a
//! compacting collector means one form suffices, because the live region is
//! already contiguous when we write it.
//!
//! The thing Larceny never shipped, and this does, is the coupled single
//! binary: [`embed_into`] appends an image plus a 16-byte trailer to a copy of
//! the runtime executable, and [`extract_embedded`] finds it again at startup.
//! No linker support and no rebuild is needed, so `fixpt build` is just a file
//! copy and an append.
//!
//! ```text
//! offset  size  field
//!      0     8  magic "FIXPTHP\0"
//!      8     4  format version
//!     12     4  flags
//!     16     8  heap word count
//!     24     8  global slot count
//!     32     8  interned symbol count
//!     40     8  explicit root count
//!     48     -  heap words     (little-endian u64, references relative to 0)
//!      -     -  global slots   (little-endian u64)
//!      -     -  symbol table   (little-endian u64)
//!      -     -  explicit roots (little-endian u64; root 0 is the runtime's
//!                               error-object record type)
//!      -     -  the code area, each of its two parts: its word count, its
//!               free blocks' count, its words (references as the heap
//!               words'), its free blocks (start and length, each a u64)
//!      -     4  CRC-32 of everything above
//! ```

use crate::heap::Heap;
use crate::value::Value;

pub const MAGIC: &[u8; 8] = b"FIXPTHP\0";
/// Bumped when the *contents* change shape, not just the envelope: version 2
/// carries the Core IR as heap objects, so a version-1 image's `Code` objects
/// would be read with the wrong layout. Version 3 gives a continuation its
/// marks (`[stack, frames, mark-vals, mark-meta, flags]` rather than
/// `[stack, frames]`), and its prelude keeps handlers and `dynamic-wind`
/// extents in marks rather than globals. Version 4 lays every object out as a
/// bloblet (`docs/object-model.md`): the header gives the field count and the
/// suffix length rather than one payload length, and bloblet pointers and
/// trailers may appear. Version 5 points at raw data (strings, bytevectors,
/// numbers' bits) with bloblet pointers, and gives code its nodes or
/// constants as its own fields. Version 6 has every object a bloblet, pointed
/// at its suffix (tag `010` retired); objects with fields have trailers, and
/// closures and environment frames their own fixed layouts. Version 8 carries
/// the code area, where every word is (`docs/research/code-stubs.md`), its
/// references counted from where the heap's memory starts.
pub const VERSION: u32 = 8;
const HEADER_BYTES: usize = 48;

/// Trailer written after an image appended to an executable.
pub const EMBED_MAGIC: &[u8; 8] = b"FIXPTEMB";
const TRAILER_BYTES: usize = 16;

#[derive(Debug)]
pub enum ImageError {
    BadMagic,
    BadVersion(u32),
    Truncated { expected: usize, found: usize },
    BadChecksum { expected: u32, found: u32 },
    Malformed(String),
}

impl std::fmt::Display for ImageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ImageError::BadMagic => write!(f, "not a fixpt heap image (bad magic)"),
            ImageError::BadVersion(v) => {
                write!(f, "heap image version {v}, this runtime understands {VERSION}")
            }
            ImageError::Truncated { expected, found } => {
                write!(f, "heap image truncated: expected {expected} bytes, found {found}")
            }
            ImageError::BadChecksum { expected, found } => {
                write!(f, "heap image checksum mismatch: expected {expected:#x}, got {found:#x}")
            }
            ImageError::Malformed(m) => write!(f, "malformed heap image: {m}"),
        }
    }
}

impl std::error::Error for ImageError {}

/// Serialise the live heap. The collector has already compacted it, so this is
/// a copy of a contiguous region plus the two root arrays.
pub fn dump(heap: &Heap) -> Vec<u8> {
    // Rebased to word 0, whichever semispace is active: an image loads there.
    let (words, globals, symbols, roots) = heap.image_parts();
    let (words, globals, symbols, roots) = (&words[..], &globals[..], &symbols[..], &roots[..]);

    let mut out = Vec::with_capacity(
        HEADER_BYTES + (words.len() + globals.len() + symbols.len() + roots.len()) * 8 + 4,
    );
    out.extend_from_slice(MAGIC);
    out.extend_from_slice(&VERSION.to_le_bytes());
    out.extend_from_slice(&0u32.to_le_bytes()); // flags
    out.extend_from_slice(&(words.len() as u64).to_le_bytes());
    out.extend_from_slice(&(globals.len() as u64).to_le_bytes());
    out.extend_from_slice(&(symbols.len() as u64).to_le_bytes());
    out.extend_from_slice(&(roots.len() as u64).to_le_bytes());
    for w in words {
        out.extend_from_slice(&w.to_le_bytes());
    }
    for v in globals {
        out.extend_from_slice(&v.raw().to_le_bytes());
    }
    for v in symbols {
        out.extend_from_slice(&v.raw().to_le_bytes());
    }
    for v in roots {
        out.extend_from_slice(&v.raw().to_le_bytes());
    }
    for (words, free) in heap.image_code() {
        out.extend_from_slice(&(words.len() as u64).to_le_bytes());
        out.extend_from_slice(&(free.len() as u64).to_le_bytes());
        for w in words {
            out.extend_from_slice(&w.to_le_bytes());
        }
        for (s, n) in free {
            out.extend_from_slice(&(s as u64).to_le_bytes());
            out.extend_from_slice(&(n as u64).to_le_bytes());
        }
    }
    let crc = crc32(&out);
    out.extend_from_slice(&crc.to_le_bytes());
    out
}

/// Parse an image and rebuild the heap. Verifies the checksum, then the heap's
/// own structural invariants — a corrupt image should fail here rather than
/// somewhere deep inside the collector later on.
pub fn load(bytes: &[u8]) -> Result<Heap, ImageError> {
    if bytes.len() < HEADER_BYTES + 4 {
        return Err(ImageError::Truncated { expected: HEADER_BYTES + 4, found: bytes.len() });
    }
    if &bytes[0..8] != MAGIC {
        return Err(ImageError::BadMagic);
    }
    let version = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    if version != VERSION {
        return Err(ImageError::BadVersion(version));
    }
    let n_words = u64::from_le_bytes(bytes[16..24].try_into().unwrap()) as usize;
    let n_globals = u64::from_le_bytes(bytes[24..32].try_into().unwrap()) as usize;
    let n_symbols = u64::from_le_bytes(bytes[32..40].try_into().unwrap()) as usize;
    let n_roots = u64::from_le_bytes(bytes[40..48].try_into().unwrap()) as usize;

    // The code area's parts after the roots: each its counts, then its
    // words and free blocks.
    let read_at = |at: usize| u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap()) as usize;
    let mut body = HEADER_BYTES + (n_words + n_globals + n_symbols + n_roots) * 8;
    let mut code_counts = [(0, 0); 2];
    for c in &mut code_counts {
        if bytes.len() < body + 16 + 4 {
            return Err(ImageError::Truncated { expected: body + 16 + 4, found: bytes.len() });
        }
        *c = (read_at(body), read_at(body + 8));
        body = c.1.checked_mul(2).and_then(|f| f.checked_add(c.0)).and_then(|n| n.checked_mul(8)).and_then(|n| (body + 16).checked_add(n)).ok_or_else(|| ImageError::Malformed("a code area larger than memory".into()))?;
    }
    let total = body + 4;
    if bytes.len() < total {
        return Err(ImageError::Truncated { expected: total, found: bytes.len() });
    }
    let expected = u32::from_le_bytes(bytes[body..body + 4].try_into().unwrap());
    let found = crc32(&bytes[..body]);
    if expected != found {
        return Err(ImageError::BadChecksum { expected, found });
    }

    let mut at = HEADER_BYTES;
    let read_u64 = |at: &mut usize| {
        let w = u64::from_le_bytes(bytes[*at..*at + 8].try_into().unwrap());
        *at += 8;
        w
    };
    let words: Vec<u64> = (0..n_words).map(|_| read_u64(&mut at)).collect();
    let globals: Vec<Value> = (0..n_globals).map(|_| Value(read_u64(&mut at))).collect();
    let symbols: Vec<Value> = (0..n_symbols).map(|_| Value(read_u64(&mut at))).collect();
    let roots: Vec<Value> = (0..n_roots).map(|_| Value(read_u64(&mut at))).collect();
    let code = code_counts.map(|(n, f)| {
        at += 16;
        let words: Vec<u64> = (0..n).map(|_| read_u64(&mut at)).collect();
        let free: Vec<(usize, usize)> = (0..f).map(|_| (read_u64(&mut at) as usize, read_u64(&mut at) as usize)).collect();
        (words, free)
    });
    // Free blocks in order, apart, within their part.
    let apart = |w: &Vec<u64>, free: &Vec<(usize, usize)>| {
        let mut end = 0;
        free.iter().all(|&(s, n)| {
            let ok = n > 0 && s >= end && s.checked_add(n).is_some_and(|e| e <= w.len());
            end = s.saturating_add(n);
            ok
        })
    };
    if !code.iter().all(|(w, free)| apart(w, free)) {
        return Err(ImageError::Malformed("the code area's free blocks out of order or outside it".into()));
    }

    let heap = Heap::from_image_with_code(&words, code, globals, symbols, roots).map_err(ImageError::Malformed)?;
    heap.verify().map_err(ImageError::Malformed)?;
    Ok(heap)
}

/// Append `image` plus a locating trailer to `exe_bytes`, producing a runtime
/// that carries its own heap. This is the "one shippable binary" mode.
pub fn embed_into(exe_bytes: &[u8], image: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(exe_bytes.len() + image.len() + TRAILER_BYTES);
    out.extend_from_slice(exe_bytes);
    out.extend_from_slice(image);
    out.extend_from_slice(&(image.len() as u64).to_le_bytes());
    out.extend_from_slice(EMBED_MAGIC);
    out
}

/// Recover an image appended by [`embed_into`], if there is one. A plain
/// runtime binary simply has no trailer, so this returns `None` and the caller
/// falls back to `--heap` or to building a fresh heap.
pub fn extract_embedded(exe_bytes: &[u8]) -> Option<&[u8]> {
    if exe_bytes.len() < TRAILER_BYTES {
        return None;
    }
    let tail = exe_bytes.len() - TRAILER_BYTES;
    if &exe_bytes[tail + 8..] != EMBED_MAGIC {
        return None;
    }
    let len = u64::from_le_bytes(exe_bytes[tail..tail + 8].try_into().ok()?) as usize;
    let start = tail.checked_sub(len)?;
    Some(&exe_bytes[start..tail])
}

/// CRC-32 (IEEE), from tables the compiler builds, so that no dependency is
/// needed: eight bytes a step, as a cached front end's image is 21 MB.
pub fn crc32(data: &[u8]) -> u32 {
    // "Slicing by 8": `TABLES[k][b]` is byte `b`'s CRC moved on `k` more
    // bytes, so a word's eight lookups are one step. The same CRC as a byte
    // at a time (`crc32_bytewise`): 42 ms that way over the front end's.
    const TABLES: [[u32; 256]; 8] = {
        let mut t = [[0u32; 256]; 8];
        let mut i = 0;
        while i < 256 {
            let mut c = i as u32;
            let mut k = 0;
            while k < 8 {
                c = if c & 1 != 0 { (c >> 1) ^ 0xedb8_8320 } else { c >> 1 };
                k += 1;
            }
            t[0][i] = c;
            i += 1;
        }
        let mut k = 1;
        while k < 8 {
            let mut i = 0;
            while i < 256 {
                let prev = t[k - 1][i];
                t[k][i] = (prev >> 8) ^ t[0][(prev & 0xff) as usize];
                i += 1;
            }
            k += 1;
        }
        t
    };
    let mut crc: u32 = 0xffff_ffff;
    let mut words = data.chunks_exact(8);
    for w in &mut words {
        let lo = u32::from_le_bytes([w[0], w[1], w[2], w[3]]) ^ crc;
        let hi = u32::from_le_bytes([w[4], w[5], w[6], w[7]]);
        crc = TABLES[7][(lo & 0xff) as usize]
            ^ TABLES[6][((lo >> 8) & 0xff) as usize]
            ^ TABLES[5][((lo >> 16) & 0xff) as usize]
            ^ TABLES[4][(lo >> 24) as usize]
            ^ TABLES[3][(hi & 0xff) as usize]
            ^ TABLES[2][((hi >> 8) & 0xff) as usize]
            ^ TABLES[1][((hi >> 16) & 0xff) as usize]
            ^ TABLES[0][(hi >> 24) as usize];
    }
    for b in words.remainder() {
        crc = (crc >> 8) ^ TABLES[0][((crc ^ *b as u32) & 0xff) as usize];
    }
    !crc
}

/// CRC-32 a byte at a time, as [`crc32`] was: what it is checked against.
#[cfg(test)]
fn crc32_bytewise(data: &[u8]) -> u32 {
    let mut crc: u32 = 0xffff_ffff;
    for b in data {
        let mut c = (crc ^ *b as u32) & 0xff;
        for _ in 0..8 {
            c = if c & 1 != 0 { (c >> 1) ^ 0xedb8_8320 } else { c >> 1 };
        }
        crc = (crc >> 8) ^ c;
    }
    !crc
}

#[cfg(test)]
mod crc_tests {
    #[test]
    fn eight_bytes_a_step_is_the_same_crc() {
        // The standard check value, and lengths around a word's.
        assert_eq!(super::crc32(b"123456789"), 0xcbf4_3926);
        let data: Vec<u8> = (0..1000u32).map(|i| (i.wrapping_mul(2654435761) >> 13) as u8).collect();
        for n in [0, 1, 7, 8, 9, 15, 16, 17, 100, 999, 1000] {
            assert_eq!(super::crc32(&data[..n]), super::crc32_bytewise(&data[..n]), "{n} bytes");
        }
    }
}
