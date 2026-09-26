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
    Tag { name: "unused", bits: 0b010, meaning: "retired: pointed at an object's header, before every object was a bloblet" },
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
    // The AST engine's environment frames: `layout::frame`.
    Kind { name: "env-frame", code: 35, traced: true },
];

pub const KIND_EXTENSION: u8 = 255;

/// A closure (kind `closure`): its code and what it closed over. Laid out
/// `[extra…][code][trailer]`, so that the code, read on every call, and
/// extra value `i`, read on every free-variable reference, are each at a
/// fixed offset from the suffix: one load, whatever the closure's size. The
/// AST engine's one extra value is the environment chain; the bytecode
/// engine's are the captured values.
pub mod closure {
    pub const CLOSURE_CODE: usize = 2;
    /// Extra value `i` is at `CLOSURE_EXTRA0 + i`.
    pub const CLOSURE_EXTRA0: usize = 3;
}

/// An AST-engine environment frame (kind `env-frame`), laid out like a
/// closure: `[slot…][parent][trailer]`, so a variable reference reads the
/// parent and a slot at fixed offsets, one load each.
pub mod frame {
    pub const FRAME_PARENT: usize = 2;
    /// Slot `i` is at `FRAME_SLOT0 + i`.
    pub const FRAME_SLOT0: usize = 3;
    pub const KIND: u8 = 35;
}

/// The fields of a code bloblet (kind `code`), named by their negative offset
/// from the suffix, which is the code itself. Field 1 is the trailer, then
/// the metadata, then the code's **items**: item `i` is at offset
/// `CODE_ITEM0 + i`, a fixed distance from the code whatever the item count.
/// For interpreted code the items are its nodes; for compiled code, whose
/// instructions are the suffix, they are its constants. Either way the
/// engine reads one with one load.
pub mod code {
    /// Node offset, or bytecode entry offset (in 32-bit words).
    pub const CODE_ENTRY: usize = 2;
    /// Compiled code only: how many stack slots one activation needs.
    pub const CODE_FRAME: usize = 3;
    /// Compiled code only: how many values the closure captures.
    pub const CODE_FREE: usize = 4;
    pub const CODE_HAS_REST: usize = 5;
    pub const CODE_ARITY: usize = 6;
    pub const CODE_NAME: usize = 7;
    /// How many items follow.
    pub const CODE_ITEMS: usize = 8;
    /// Item 0; item `i` is at `CODE_ITEM0 + i`.
    pub const CODE_ITEM0: usize = 9;
    /// The fixed fields, the trailer not counted.
    pub const CODE_FIXED: usize = 7;

    pub const ALL: &[(&str, usize)] = &[
        ("entry", CODE_ENTRY),
        ("frame", CODE_FRAME),
        ("free", CODE_FREE),
        ("has-rest", CODE_HAS_REST),
        ("arity", CODE_ARITY),
        ("name", CODE_NAME),
        ("items", CODE_ITEMS),
        ("item0", CODE_ITEM0),
    ];
}

/// A threaded word (kind `threaded-code`): Forth's threaded code, as a
/// bloblet. Laid out `[cell…][name][entry][trailer]`. `entry` is the fixnum
/// number of the routine that runs the word: `ROUTINE_DOCOL` for a word made
/// of cells, which runs them in increasing `k` from `WORD_CELL0`. It is a
/// number, not an address, so a heap image does not hold machine addresses.
/// A compiled word gets a routine of its own and a new number.
///
/// A cell is a fixnum, which names a primitive routine directly (token
/// threading, no word object needed), or a pointer to another word, which
/// runs that word's entry routine. A primitive that takes an operand, such
/// as `lit` or `branch`, takes it from the next cell.
///
/// The return stack holds pairs, the word and the fixnum `k` of the next
/// cell to run in it, so every entry is a Value and the stack is a root like
/// any other.
pub mod threaded {
    pub const KIND: u8 = 33;
    pub const WORD_ENTRY: usize = 2;
    pub const WORD_NAME: usize = 3;
    /// Cell `i` is at `WORD_CELL0 + i`.
    pub const WORD_CELL0: usize = 4;

    /// The routines, by number, with their stack effects. The first
    /// `PRIMITIVES` of them may appear as cells.
    pub const ROUTINES: &[(&str, &str)] = &[
        ("docol", "run a word's cells"),
        ("exit", "return to the calling word"),
        ("halt", "stop, leaving the data stack as the result"),
        ("lit", "( -- x ), x the next cell"),
        ("branch", "skip the next cell's fixnum of cells, counted after it"),
        ("0branch", "( flag -- ), branch if flag is #f"),
        ("execute", "( w -- ), run a word, or a primitive given as its fixnum"),
        ("dup", "( a -- a a )"),
        ("drop", "( a -- )"),
        ("swap", "( a b -- b a )"),
        ("over", "( a b -- a b a )"),
        ("+", "( a b -- a+b ), fixnums"),
        ("-", "( a b -- a-b ), fixnums"),
        ("<", "( a b -- a<b ), fixnums"),
        ("eq", "( a b -- flag ), the same Value"),
        ("field@", "( obj k -- x ), field k of a bloblet"),
        ("field!", "( x obj k -- ), field k of a bloblet"),
        ("cons", "( a b -- pair )"),
        ("car", "( pair -- a )"),
        ("cdr", "( pair -- b )"),
    ];
    pub const PRIMITIVES: usize = ROUTINES.len();

    pub const fn routine(name: &str) -> u64 {
        let mut i = 0;
        while i < ROUTINES.len() {
            if super::const_str_eq(ROUTINES[i].0, name) {
                return i as u64;
            }
            i += 1;
        }
        panic!("no such routine")
    }

    pub const ROUTINE_DOCOL: u64 = routine("docol");
}

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
    out.push_str(&format!("(define kind-extension int {KIND_EXTENSION})\n\n"));
    out.push_str(";;; A closure's fields, and an environment frame's, by negative offset.\n");
    out.push_str(&format!("(define closure-code int {})\n", closure::CLOSURE_CODE));
    out.push_str(&format!("(define closure-extra0 int {})\n", closure::CLOSURE_EXTRA0));
    out.push_str(&format!("(define frame-parent int {})\n", frame::FRAME_PARENT));
    out.push_str(&format!("(define frame-slot0 int {})\n\n", frame::FRAME_SLOT0));
    out.push_str(";;; A code bloblet's fields, by negative offset from its code. 1 is the trailer.\n");
    for (name, k) in code::ALL {
        out.push_str(&format!("(define code-{name} int {k})\n"));
    }
    out.push_str("\n;;; A threaded word's fields, by negative offset, and its routines by number.\n");
    out.push_str(&format!("(define word-entry int {})\n", threaded::WORD_ENTRY));
    out.push_str(&format!("(define word-name int {})\n", threaded::WORD_NAME));
    out.push_str(&format!("(define word-cell0 int {})\n", threaded::WORD_CELL0));
    for (i, (name, effect)) in threaded::ROUTINES.iter().enumerate() {
        out.push_str(&format!("(define routine-{} int {i})  ; {effect}\n", fx_name(name)));
    }
    out
}

/// A routine's name as an FX-26 identifier.
fn fx_name(name: &str) -> String {
    match name {
        "+" => "add".into(),
        "-" => "sub".into(),
        "<" => "less".into(),
        "field@" => "field-ref".into(),
        "field!" => "field-set".into(),
        "0branch" => "zbranch".into(),
        n => n.into(),
    }
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
