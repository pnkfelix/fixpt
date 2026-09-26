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
/// closures and environment frames their own fixed layouts.
pub const VERSION: u32 = 7;
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
    let words = heap.live_words();
    let globals = heap.globals_slice();
    let symbols = heap.symbols_slice();
    let roots = heap.roots_slice();

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

    let body = HEADER_BYTES + (n_words + n_globals + n_symbols + n_roots) * 8;
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

    let heap = Heap::from_image(&words, globals, symbols, roots).map_err(ImageError::Malformed)?;
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

/// CRC-32 (IEEE), computed without a static table: the table is small and this
/// runs once per image, so the bit-at-a-time form keeps the dependency count at
/// zero for no measurable cost.
pub fn crc32(data: &[u8]) -> u32 {
    let mut crc: u32 = 0xffff_ffff;
    for b in data {
        crc ^= *b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xedb8_8320 & mask);
        }
    }
    !crc
}
