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
//!     12     4  flags (0)
//!     16     8  the base its references are made for, in words: the fixed
//!               base a process's first heap is at
//!     24     4  section count
//!     28     4  0
//!     32     -  the section table, 48 bytes a section ([`Section`]): its
//!               kind, its space, what it is ([`MOVES`], [`WRITTEN`],
//!               [`RUNS`]), its alignment in the file (log2 bytes, 0 for
//!               none; u32 each); its offset from the image's start and its
//!               length (bytes), where in the heap's memory it goes and how
//!               much of it its space spans there (words; u64 each)
//!      -     -  the sections, in the table's order
//!      -     4  CRC-32 of everything above
//! ```
//!
//! The sections (`TODO.md` §165): one of metadata, read and never mapped;
//! one of words for each space of the heap the image fills, each where in
//! the heap's memory that space is, so that what moves and may be written
//! (the old space's words) is apart from what never moves (the code area's
//! two parts), and each may go to pages of its own. A heap of more spaces
//! than these (static areas, regions, more generations) is more sections,
//! each of its space. Code is written still (its fields, as what they
//! refer to moves) until the static area (§161) makes what it refers to
//! stay. A word section's words are as the heap has them, its references
//! addresses of a heap at the base; every place, of a fixup or a free
//! block, is a place in the heap's memory, whatever section it is in.
//!
//! ```text
//! the metadata: four counts (u64): global slots, interned symbols,
//! explicit roots, fixups; the global slots, the symbol table and the
//! explicit roots (each a u64 value; root 0 is the runtime's error-object
//! record type); the fixups: where a word is that a load at the base still
//! writes (a reference to an interned symbol); then, for each word section
//! in the table's order, its free blocks' count and its free blocks (start
//! and length, u64 each): room in a space that holds no object.
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
/// references counted from where the heap's memory starts. Version 9 has
/// references as addresses of the heap it was made of, its base and the
/// fixups (`TODO.md` §160): loaded at the same base, nothing else moves.
/// Version 10 has a call-out as the call-out itself, encoded, the same in
/// every machine, not a number in the table of the machine that made it.
/// Version 11 is a table of sections (`TODO.md` §165).
pub const VERSION: u32 = 11;
const HEADER_BYTES: usize = 32;
const SECTION_BYTES: usize = 48;

/// The page an image is aligned to for mapping: 16 KiB, macOS on arm64's,
/// and so a whole number of x86_64's and Linux on arm64's.
pub const PAGE: usize = 16 * 1024;
/// What a section is: what may move, what may be written, what runs.
pub const MOVES: u32 = 1;
pub const WRITTEN: u32 = 2;
pub const RUNS: u32 = 4;

/// The kinds of section: the metadata, or a space's words.
pub const META: u32 = 1;
pub const WORDS: u32 = 2;

/// The spaces of a heap a word section may be of. A space a reader does not
/// know is refused, not ignored: its words would be lost.
pub const OLD: u32 = 1;
pub const CODE_STUBBED: u32 = 2;
pub const CODE_NATIVE: u32 = 3;
/// Static data, immutable and mutable (`TODO.md` §161): no image has them
/// yet.
pub const STATIC: u32 = 4;
pub const STATIC_MUTABLE: u32 = 5;

/// A section, as the table has it.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Section {
    pub kind: u32,
    /// Its space (a word section's), 0 for the metadata.
    pub space: u32,
    pub what: u32,
    /// Its offset's alignment, log2 bytes, 0 for none.
    pub align: u32,
    pub offset: usize,
    pub bytes: usize,
    /// Where in the heap's memory its words go, and how many words its
    /// space spans there (at least its own).
    pub place: usize,
    pub extent: usize,
}

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
/// a copy of a contiguous region plus the two root arrays. Packed: for an
/// image that is read, as a `.fasl`'s is.
pub fn dump_packed(heap: &Heap) -> Vec<u8> {
    dump_with(heap, false, false)
}

/// [`dump_packed`], each word section page-aligned ([`PAGE`]) from its
/// start, for an image that may be mapped (one per process: the front end's
/// cache, a heap a program dumped, an executable's own). Where it is kept, it
/// must start on a page too (`embed_into`, the cache's file).
pub fn dump_mappable(heap: &Heap) -> Vec<u8> {
    dump_with(heap, true, false)
}

/// [`dump_mappable`], the old space's words the image's static area
/// (`TODO.md` §161): where it is read, nothing of it moves or is copied. For
/// a heap of its own made to be an image, the front end's, with no static
/// area of its own.
pub fn dump_static(heap: &Heap) -> Vec<u8> {
    dump_with(heap, true, true)
}

fn dump_with(heap: &Heap, aligned: bool, old_static: bool) -> Vec<u8> {
    let base = Heap::image_base_word();
    let [(immutable_at, half), (mutable_at, _)] = crate::heap::static_area();
    // Its active semispace the first, whichever it is, or, made static,
    // each object in the static area's half it belongs in: an image loads
    // there.
    let (words, [immutable, statics], globals, symbols, roots, code) = if old_static {
        let (halves, globals, symbols, roots, code) = heap.image_split_static(base);
        (Vec::new(), halves, globals, symbols, roots, code)
    } else {
        let (words, globals, symbols, roots) = heap.image_parts_at(base, 0);
        (words, heap.image_static(base, 0), globals, symbols, roots, heap.image_code(base, 0))
    };
    let [stubbed_at, native_at] = crate::heap::code_part_bases();
    let fixups = crate::heap::image_fixups(&[(0, &words), (immutable_at, &immutable), (mutable_at, &statics), (stubbed_at, &code[0].0), (native_at, &code[1].0)], &symbols);
    let le = |out: &mut Vec<u8>, ws: &mut dyn Iterator<Item = u64>| {
        for w in ws {
            out.extend_from_slice(&w.to_le_bytes());
        }
    };
    // Each space's words: where they go, how much of the heap's memory the
    // space spans, and its free blocks (each from its part's start in the
    // heap, made places in the heap's memory).
    let (code_at, code_words) = (crate::heap::code_part_bases(), crate::heap::code_part_words());
    let spaces: [(u32, u32, usize, usize, &[u64], Vec<(usize, usize)>); 5] = [
        (OLD, MOVES | WRITTEN, 0, words.len(), &words, Vec::new()),
        (STATIC, 0, immutable_at, half, &immutable, Vec::new()),
        (STATIC_MUTABLE, WRITTEN, mutable_at, half, &statics, Vec::new()),
        (CODE_STUBBED, WRITTEN | RUNS, code_at[0], code_words, &code[0].0, code[0].1.iter().map(|&(s, n)| (code_at[0] + s, n)).collect()),
        (CODE_NATIVE, WRITTEN | RUNS, code_at[1], code_words, &code[1].0, code[1].1.iter().map(|&(s, n)| (code_at[1] + s, n)).collect()),
    ];
    let mut meta = Vec::new();
    le(&mut meta, &mut [globals.len(), symbols.len(), roots.len(), fixups.len()].into_iter().map(|n| n as u64));
    le(&mut meta, &mut globals.iter().chain(&symbols).chain(&roots).map(|v| v.raw()));
    le(&mut meta, &mut fixups.iter().map(|&f| f as u64));
    for (.., free) in &spaces {
        le(&mut meta, &mut std::iter::once(free.len() as u64).chain(free.iter().flat_map(|&(s, n)| [s as u64, n as u64])));
    }
    let n = 1 + spaces.len();
    let mut at = HEADER_BYTES + n * SECTION_BYTES;
    let mut table = vec![Section { kind: META, space: 0, what: 0, align: 0, offset: at, bytes: meta.len(), place: 0, extent: 0 }];
    at += meta.len();
    let align = if aligned { PAGE.trailing_zeros() } else { 0 };
    for &(space, what, place, extent, ws, _) in &spaces {
        at = at.div_ceil(1 << align) << align;
        table.push(Section { kind: WORDS, space, what, align, offset: at, bytes: ws.len() * 8, place, extent });
        at += ws.len() * 8;
    }
    let mut out = Vec::with_capacity(at + 4);
    out.extend_from_slice(MAGIC);
    out.extend_from_slice(&VERSION.to_le_bytes());
    out.extend_from_slice(&0u32.to_le_bytes());
    out.extend_from_slice(&(base as u64).to_le_bytes());
    out.extend_from_slice(&(n as u32).to_le_bytes());
    out.extend_from_slice(&0u32.to_le_bytes());
    for t in &table {
        for v in [t.kind, t.space, t.what, t.align] {
            out.extend_from_slice(&v.to_le_bytes());
        }
        for v in [t.offset, t.bytes, t.place, t.extent] {
            out.extend_from_slice(&(v as u64).to_le_bytes());
        }
    }
    out.extend_from_slice(&meta);
    for (t, (.., ws, _)) in table[1..].iter().zip(&spaces) {
        out.resize(t.offset, 0);
        le(&mut out, &mut ws.iter().copied());
    }
    let crc = crc32(&out);
    out.extend_from_slice(&crc.to_le_bytes());
    out
}

/// An image's section table, read: each section, within the image, its
/// header and table whole, an offset as aligned as it says.
pub fn sections(bytes: &[u8]) -> Result<Vec<Section>, ImageError> {
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
    let u32_at = |at: usize| u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap());
    let u64_at = |at: usize| u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap()) as usize;
    let n = u32_at(24) as usize;
    let Some(table_end) = n.checked_mul(SECTION_BYTES).and_then(|t| t.checked_add(HEADER_BYTES)).filter(|&e| e + 4 <= bytes.len()) else {
        return Err(ImageError::Truncated { expected: HEADER_BYTES + n.saturating_mul(SECTION_BYTES) + 4, found: bytes.len() });
    };
    let table: Vec<Section> = (0..n)
        .map(|i| {
            let at = HEADER_BYTES + i * SECTION_BYTES;
            Section {
                kind: u32_at(at),
                space: u32_at(at + 4),
                what: u32_at(at + 8),
                align: u32_at(at + 12),
                offset: u64_at(at + 16),
                bytes: u64_at(at + 24),
                place: u64_at(at + 32),
                extent: u64_at(at + 40),
            }
        })
        .collect();
    let body = bytes.len() - 4;
    for t in &table {
        let inside = t.offset >= table_end && t.offset.checked_add(t.bytes).is_some_and(|e| e <= body);
        let aligned = t.align < 32 && t.offset.is_multiple_of(1 << t.align);
        let words = t.kind != WORDS || (t.bytes.is_multiple_of(8) && t.bytes / 8 <= t.extent);
        if !inside || !aligned || !words {
            return Err(ImageError::Malformed(format!("section {} (space {}) outside the image, or not as it says", t.kind, t.space)));
        }
    }
    Ok(table)
}

/// Parse an image and rebuild the heap. Verifies the checksum, then the heap's
/// own structural invariants — a corrupt image should fail here rather than
/// somewhere deep inside the collector later on.
pub fn load(bytes: &[u8]) -> Result<Heap, ImageError> {
    load_checking(bytes, true)
}

/// [`load`] for an image this executable wrote, by a rename, and keyed by
/// it (its own embedded image, the front end's cache, a `.fasl`): neither
/// its checksum nor the heap's invariants checked, each a read of every
/// page (`TODO.md` §159). Neither is security: an image holds native code.
pub fn load_trusted(bytes: &[u8]) -> Result<Heap, ImageError> {
    load_checking(bytes, false)
}

/// An image's parts, read but not yet made a heap: its live region's words
/// as the file has them (little-endian), its roots, globals and symbols,
/// and each part of its code area, its words (the same) and free blocks.
/// For [`load`], and for [`Heap::splice_image`], which puts them in a heap
/// that holds something already.
pub struct Parts<'a> {
    pub words: &'a [u8],
    /// The static area's words, as the file has them: its immutable half's,
    /// and its mutable half's.
    pub immutable: &'a [u8],
    pub statics: &'a [u8],
    pub globals: Vec<Value>,
    pub symbols: Vec<Value>,
    pub roots: Vec<Value>,
    pub code: [(&'a [u8], Vec<(usize, usize)>); 2],
    /// Where the memory of the heap it was made of started, in words: its
    /// references are addresses there.
    pub base: usize,
    /// The words a load at `base` still writes, by place.
    pub fixups: Vec<usize>,
}

impl Parts<'_> {
    pub fn n_words(&self) -> usize {
        self.words.len() / 8
    }

    /// The word the image puts at place `i` of the heap's memory: of its
    /// old space, its static area, or a part of its code area.
    pub fn word(&self, i: usize) -> u64 {
        let [(immutable_at, _), (static_at, _)] = crate::heap::static_area();
        let (bytes, at) = match crate::heap::code_part_of(i) {
            Some((k, at)) => (self.code[k].0, at),
            None if i >= static_at => (self.statics, i - static_at),
            None if i >= immutable_at => (self.immutable, i - immutable_at),
            None => (self.words, i),
        };
        u64::from_le_bytes(bytes[at * 8..at * 8 + 8].try_into().unwrap())
    }

    /// A pair's car and cdr, in the image's own terms.
    pub fn car(&self, p: Value) -> Value {
        Value(self.word(p.index() - self.base))
    }

    pub fn cdr(&self, p: Value) -> Value {
        Value(self.word(p.index() - self.base + 1))
    }
}

/// Little-endian words, as a `Vec`.
pub(crate) fn words_of(b: &[u8]) -> Vec<u64> {
    b.chunks_exact(8).map(|w| u64::from_le_bytes(w.try_into().unwrap())).collect()
}

/// An image's [`Parts`], its checksum checked if `check`. Of a heap of the
/// spaces this one has: the old space's words, the static area's (mutable,
/// all of it so far), and the code area's two parts; a section of another
/// space is refused.
pub fn parts(bytes: &[u8], check: bool) -> Result<Parts<'_>, ImageError> {
    // The checksum before the table, so that a corruption anywhere is said
    // as one, before the table it may be in is read; after the magic and
    // version, which say what the bytes are.
    let version_ok = bytes.len() >= HEADER_BYTES + 4 && &bytes[0..8] == MAGIC && u32::from_le_bytes(bytes[8..12].try_into().unwrap()) == VERSION;
    if check && version_ok {
        let body = bytes.len() - 4;
        let expected = u32::from_le_bytes(bytes[body..].try_into().unwrap());
        let found = crc32(&bytes[..body]);
        if expected != found {
            return Err(ImageError::BadChecksum { expected, found });
        }
    }
    let table = sections(bytes)?;
    let base = u64::from_le_bytes(bytes[16..24].try_into().unwrap()) as usize;
    let code_at = crate::heap::code_part_bases();
    let [(immutable_at, _), (static_at, _)] = crate::heap::static_area();
    let words_of_space: Vec<&Section> = table.iter().filter(|t| t.kind == WORDS).collect();
    let mut by_space: [Option<&[u8]>; 5] = [None; 5];
    for t in &words_of_space {
        let (k, place) = match t.space {
            OLD => (0, 0),
            CODE_STUBBED => (1, code_at[0]),
            CODE_NATIVE => (2, code_at[1]),
            STATIC_MUTABLE => (3, static_at),
            STATIC => (4, immutable_at),
            s => return Err(ImageError::Malformed(format!("a section of space {s}, which this heap has not"))),
        };
        if t.place != place || by_space[k].is_some() {
            return Err(ImageError::Malformed(format!("space {}'s section elsewhere than this heap has it, or twice", t.space)));
        }
        by_space[k] = Some(&bytes[t.offset..t.offset + t.bytes]);
    }
    let meta = table.iter().find(|t| t.kind == META).ok_or_else(|| ImageError::Malformed("no metadata".into()))?;
    let meta = &bytes[meta.offset..meta.offset + meta.bytes];
    let mut at = 0;
    let mut read = |n: usize| -> Result<Vec<u64>, ImageError> {
        let end = n.checked_mul(8).and_then(|b| b.checked_add(at)).filter(|&e| e <= meta.len()).ok_or_else(|| ImageError::Malformed("the metadata ends early".into()))?;
        let ws = words_of(&meta[at..end]);
        at = end;
        Ok(ws)
    };
    let counts: Vec<usize> = read(4)?.into_iter().map(|n| n as usize).collect();
    let values = |ws: Vec<u64>| ws.into_iter().map(Value).collect::<Vec<Value>>();
    let globals = values(read(counts[0])?);
    let symbols = values(read(counts[1])?);
    let roots = values(read(counts[2])?);
    let fixups: Vec<usize> = read(counts[3])?.into_iter().map(|f| f as usize).collect();
    // Each word section's free blocks, by its place in the table; made
    // places in its part again.
    let mut free: [Vec<(usize, usize)>; 5] = Default::default();
    for t in &words_of_space {
        let n = read(1)?[0] as usize;
        let blocks = read(n.checked_mul(2).ok_or_else(|| ImageError::Malformed("free blocks past memory".into()))?)?;
        let k = match t.space {
            OLD => 0,
            CODE_STUBBED => 1,
            CODE_NATIVE => 2,
            STATIC_MUTABLE => 3,
            _ => 4,
        };
        free[k] = blocks.chunks_exact(2).map(|p| ((p[0] as usize).wrapping_sub(t.place), p[1] as usize)).collect();
    }
    if !free[0].is_empty() || !free[3].is_empty() || !free[4].is_empty() {
        return Err(ImageError::Malformed("free blocks in the old space or the static area".into()));
    }
    let empty: &[u8] = &[];
    let words = by_space[0].unwrap_or(empty);
    let statics = by_space[3].unwrap_or(empty);
    let immutable = by_space[4].unwrap_or(empty);
    let [_, free0, free1, _, _] = free;
    let code = [(by_space[1].unwrap_or(empty), free0), (by_space[2].unwrap_or(empty), free1)];
    // Free blocks in order, apart, within their part.
    let apart = |w: &[u8], free: &Vec<(usize, usize)>| {
        let mut end = 0;
        free.iter().all(|&(s, n)| {
            let ok = n > 0 && s >= end && s.checked_add(n).is_some_and(|e| e <= w.len() / 8);
            end = s.saturating_add(n);
            ok
        })
    };
    if !code.iter().all(|(w, free)| apart(w, free)) {
        return Err(ImageError::Malformed("the code area's free blocks out of order or outside it".into()));
    }
    let (n_words, n_statics, n_immutable) = (words.len() / 8, statics.len() / 8, immutable.len() / 8);
    let inside = |f: usize| {
        f < n_words
            || (static_at..static_at + n_statics).contains(&f)
            || (immutable_at..immutable_at + n_immutable).contains(&f)
            || crate::heap::code_part_of(f).is_some_and(|(k, i)| i < code[k].0.len() / 8)
    };
    if !fixups.iter().all(|&f| inside(f)) {
        return Err(ImageError::Malformed("a fixup outside the image".into()));
    }
    Ok(Parts { words, immutable, statics, globals, symbols, roots, code, base, fixups })
}

fn load_checking(bytes: &[u8], check: bool) -> Result<Heap, ImageError> {
    let Parts { words, immutable, statics, globals, symbols, roots, code, base, fixups } = parts(bytes, check)?;
    let code = code.map(|(w, free)| (words_of(w), free));
    let heap = Heap::from_image_with_code(words.len() / 8, |w| {
        for (w, b) in w.iter_mut().zip(words.chunks_exact(8)) {
            *w = u64::from_le_bytes(b.try_into().unwrap());
        }
    }, [&words_of(immutable), &words_of(statics)], code, globals, symbols, roots, base, &fixups).map_err(ImageError::Malformed)?;
    if check {
        heap.verify().map_err(ImageError::Malformed)?;
    }
    Ok(heap)
}

/// Append `image` plus a locating trailer to `exe_bytes`, producing a runtime
/// that carries its own heap. This is the "one shippable binary" mode.
pub fn embed_into(exe_bytes: &[u8], image: &[u8]) -> Vec<u8> {
    // The image on a page of the file, so that it may be mapped from it.
    let at = exe_bytes.len().div_ceil(PAGE) * PAGE;
    let mut out = Vec::with_capacity(at + image.len() + TRAILER_BYTES);
    out.extend_from_slice(exe_bytes);
    out.resize(at, 0);
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

/// The image appended to the file at `path`, read without reading the rest:
/// the trailer first, and the image only if [`EMBED_MAGIC`] is there. A plain
/// runtime binary costs one seek and one 16-byte read.
pub fn read_embedded(path: &std::path::Path) -> std::io::Result<Option<Vec<u8>>> {
    use std::io::{Read as _, Seek as _, SeekFrom};
    let mut f = std::fs::File::open(path)?;
    let len = f.metadata()?.len();
    if len < TRAILER_BYTES as u64 {
        return Ok(None);
    }
    let mut trailer = [0u8; TRAILER_BYTES];
    f.seek(SeekFrom::Start(len - TRAILER_BYTES as u64))?;
    f.read_exact(&mut trailer)?;
    if &trailer[8..] != EMBED_MAGIC {
        return Ok(None);
    }
    let n = u64::from_le_bytes(trailer[..8].try_into().unwrap());
    let Some(start) = (len - TRAILER_BYTES as u64).checked_sub(n) else {
        return Ok(None);
    };
    let mut img = vec![0u8; n as usize];
    f.seek(SeekFrom::Start(start))?;
    f.read_exact(&mut img)?;
    Ok(Some(img))
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
