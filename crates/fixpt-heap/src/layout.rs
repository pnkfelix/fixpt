//! The object layout, specified once.
//!
//! Everything about how a value and a heap object are laid out in words — the
//! tags, the header's bit fields, the kinds — is a table here, and nowhere else.
//! `value.rs` and `heap.rs` are written against these constants, and the FX-26
//! side's copy, `crates/fixpt-fx26/src/layout.fx`, is *generated* from the same
//! table by [`fx26_module`], with a test that the checked-in file is what the
//! generator produces. So the two languages cannot drift apart: changing the
//! layout means changing this file, regenerating, and committing both.
//!
//! The design is `docs/object-model.md`. The short version: a heap object is a
//! **bloblet** — a header, `F` tagged fields, and `B` bytes of untraced suffix —
//! and the collector needs only `F` and `B` to trace it, never its kind.

/// One of the eight 3-bit tags a word can carry.
#[derive(Copy, Clone, Debug)]
pub struct Tag {
    pub name: &'static str,
    pub bits: u64,
    pub meaning: &'static str,
}

pub const TAG_BITS: u32 = 3;
pub const TAG_MASK: u64 = (1 << TAG_BITS) - 1;

pub const TAGS: &[Tag] = &[
    Tag { name: "fixnum", bits: 0b000, meaning: "61-bit signed integer; also what a zeroed word is" },
    Tag { name: "pair", bits: 0b001, meaning: "index of a two-word car/cdr cell, which has no header" },
    Tag { name: "object", bits: 0b010, meaning: "index of an object's header (the older pointer style)" },
    Tag { name: "immediate", bits: 0b011, meaning: "#f, #t, (), unit, eof, characters, …" },
    Tag { name: "bloblet", bits: 0b100, meaning: "index of the start of a bloblet's suffix" },
    Tag { name: "trailer", bits: 0b101, meaning: "the last field of a bloblet that has one; runtime-reserved payload" },
    Tag { name: "header", bits: 0b110, meaning: "never a value: starts an object" },
    Tag { name: "forward", bits: 0b111, meaning: "a forwarding pointer, only during a collection" },
];

/// Look up a tag's bits by name. Only for the table's own users; the hot paths
/// use the constants in `value.rs`.
pub const fn tag(name: &str) -> u64 {
    let mut i = 0;
    while i < TAGS.len() {
        if const_str_eq(TAGS[i].name, name) {
            return TAGS[i].bits;
        }
        i += 1;
    }
    panic!("no such tag")
}

/// A bit field of the header word.
#[derive(Copy, Clone, Debug)]
pub struct Field {
    pub name: &'static str,
    /// The lowest bit.
    pub lo: u32,
    pub width: u32,
    pub meaning: &'static str,
}

impl Field {
    pub const fn mask(&self) -> u64 {
        if self.width == 64 { u64::MAX } else { (1u64 << self.width) - 1 }
    }
    #[inline]
    pub const fn get(&self, w: u64) -> u64 {
        (w >> self.lo) & self.mask()
    }
    #[inline]
    pub const fn put(&self, w: u64, v: u64) -> u64 {
        (w & !(self.mask() << self.lo)) | ((v & self.mask()) << self.lo)
    }
    pub const fn max(&self) -> u64 {
        self.mask()
    }
}

pub const H_TAG: Field = Field { name: "tag", lo: 0, width: 3, meaning: "110, the header tag" };
pub const H_KIND: Field = Field { name: "kind", lo: 3, width: 8, meaning: "what the object is to the language" };
pub const H_LARGE: Field =
    Field { name: "large", lo: 11, width: 1, meaning: "F is too big for this word: it is in the next one" };
pub const H_FIELDS_FROZEN: Field =
    Field { name: "fields-frozen", lo: 12, width: 1, meaning: "the fields are immutable" };
pub const H_SUFFIX_FROZEN: Field =
    Field { name: "suffix-frozen", lo: 13, width: 1, meaning: "the suffix is immutable" };
pub const H_FIELDS: Field = Field { name: "fields", lo: 14, width: 18, meaning: "F, the number of tagged fields" };
pub const H_BYTES: Field = Field { name: "bytes", lo: 32, width: 32, meaning: "B, the suffix length in bytes" };

pub const HEADER_FIELDS: &[Field] =
    &[H_TAG, H_KIND, H_LARGE, H_FIELDS_FROZEN, H_SUFFIX_FROZEN, H_FIELDS, H_BYTES];

/// The second header word of a `large` object: header-tagged, so that neither
/// a linear scan nor a backward scan can mistake it for a field, with the kind
/// [`KIND_EXTENSION`] and the full field count above it.
pub const X_KIND: Field = H_KIND;
pub const X_FIELDS: Field =
    Field { name: "fields", lo: 11, width: 53, meaning: "F, for an object whose F does not fit the main header" };

/// The trailer's payload. The runtime's own: `docs/object-model.md` reserves
/// every bit of a trailer beyond its tag, and no program may read one. The
/// runtime stores the distance, in words, from the trailer back to the header.
pub const T_DISTANCE: Field =
    Field { name: "distance", lo: 3, width: 61, meaning: "words from the trailer back to the header" };

/// A kind: what an object is to the language. The collector never asks.
#[derive(Copy, Clone, Debug)]
pub struct Kind {
    pub name: &'static str,
    pub code: u8,
    /// How the older, header-pointed objects of this kind split their payload:
    /// all traced fields, or all raw suffix.
    pub traced: bool,
}

/// Every kind. Codes 1–19 are the object types the system has always had;
/// `ObjType` in `value.rs` names the same codes. 255 marks a large header's
/// extension word, never an object.
pub const KINDS: &[Kind] = &[
    Kind { name: "string", code: 1, traced: false },
    Kind { name: "symbol", code: 2, traced: true },
    Kind { name: "vector", code: 3, traced: true },
    Kind { name: "bytevector", code: 4, traced: false },
    Kind { name: "flonum", code: 5, traced: false },
    Kind { name: "bignum", code: 6, traced: false },
    Kind { name: "ratnum", code: 7, traced: true },
    Kind { name: "closure", code: 8, traced: true },
    Kind { name: "code", code: 9, traced: true },
    Kind { name: "box", code: 10, traced: true },
    Kind { name: "record", code: 11, traced: true },
    Kind { name: "record-type", code: 12, traced: true },
    Kind { name: "port", code: 13, traced: true },
    Kind { name: "continuation", code: 14, traced: true },
    Kind { name: "values", code: 15, traced: true },
    Kind { name: "promise", code: 16, traced: true },
    Kind { name: "hash-table", code: 17, traced: true },
    Kind { name: "environment", code: 18, traced: true },
    Kind { name: "primitive", code: 19, traced: true },
    // Bloblets proper, pointed at their suffix.
    Kind { name: "bloblet", code: 32, traced: true },
    Kind { name: "threaded-code", code: 33, traced: true },
    Kind { name: "compiled-code", code: 34, traced: true },
];

pub const KIND_EXTENSION: u8 = 255;

const fn const_str_eq(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// The FX-26 module generated from this table: the same numbers, as FX-26
/// definitions, for FX-26 code that lays out or reads objects. Checked in as
/// `crates/fixpt-fx26/src/layout.fx`; a test there requires the file to be
/// exactly this.
pub fn fx26_module() -> String {
    let mut out = String::new();
    out.push_str(";;; The object layout, generated from `crates/fixpt-heap/src/layout.rs`.\n");
    out.push_str(";;; Do not edit: change the table there and regenerate, with\n");
    out.push_str(";;;   FIXPT_BLESS=1 cargo test -p fixpt-fx26 --test layout\n");
    out.push_str(";;; See `docs/object-model.md`.\n\n");
    out.push_str(";;; Tags: the low three bits of every word.\n");
    for t in TAGS {
        out.push_str(&format!("(define tag-{} int {})  ; {}\n", t.name, t.bits, t.meaning));
    }
    out.push_str(&format!("(define tag-bits int {TAG_BITS})\n\n"));
    out.push_str(";;; The header word's bit fields: lowest bit, and width.\n");
    for f in HEADER_FIELDS {
        out.push_str(&format!(
            "(define header-{}-lo int {})\n(define header-{}-width int {})  ; {}\n",
            f.name, f.lo, f.name, f.width, f.meaning
        ));
    }
    out.push_str(&format!(
        "(define extension-fields-lo int {})\n(define extension-fields-width int {})  ; {}\n\n",
        X_FIELDS.lo, X_FIELDS.width, X_FIELDS.meaning
    ));
    out.push_str(";;; Kinds.\n");
    for k in KINDS {
        out.push_str(&format!("(define kind-{} int {})\n", k.name, k.code));
    }
    out.push_str(&format!("(define kind-extension int {KIND_EXTENSION})\n"));
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_header_fields_tile_the_word() {
        let mut covered = 0u64;
        for f in HEADER_FIELDS {
            let bits = f.mask() << f.lo;
            assert_eq!(covered & bits, 0, "{} overlaps", f.name);
            covered |= bits;
        }
        assert_eq!(covered, u64::MAX, "the header has unassigned bits");
    }

    #[test]
    fn tags_are_distinct_and_complete() {
        let mut seen = [false; 8];
        for t in TAGS {
            assert!(!seen[t.bits as usize], "tag {} reused", t.name);
            seen[t.bits as usize] = true;
        }
        assert!(seen.iter().all(|s| *s));
    }

    #[test]
    fn kinds_fit_and_are_distinct() {
        let mut seen = std::collections::HashSet::new();
        for k in KINDS {
            assert!((k.code as u64) <= H_KIND.max());
            assert_ne!(k.code, KIND_EXTENSION, "{} takes the extension code", k.name);
            assert!(seen.insert(k.code), "kind code {} reused", k.code);
        }
    }
}
