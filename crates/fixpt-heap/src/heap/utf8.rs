//! UTF-8 text (FX-26's `utf8`, `TODO.md` §306): a frozen bloblet of no
//! fields whose suffix is its text, valid UTF-8, the header's B its length
//! in bytes; or a *slice* of one (§310), a view of a piece of another's
//! text, nothing copied. Indexed by byte offset, as Rust's `str` is: a
//! character is read where one starts, in O(1); the `i`th character is a
//! walk, and so is its count of characters, which is not kept (§310), but
//! for text all ASCII, marked so where it is made, a kind of its own
//! (`utf8-ascii`), whose count is its length. Made only of a `&str`, so
//! never invalid; a slice only between two characters' starts, so never
//! either.
//!
//! A slice is frozen, of the kind `utf8-slice`, its values its owner (a
//! whole `utf8`, never a slice: a slice of a slice is one of the first's
//! owner; or a bytevector frozen, its bytes validated, `utf8_of_bytes`),
//! its start and end, offsets into the owner's suffix in bytes,
//! and whether it is marked all ASCII, its owner's mark (never found by
//! looking at its piece). It has a trailer, so the word before its
//! (empty) suffix is never a header, as a whole one's is: what native code
//! tests to read a whole one in line.

use super::Heap;
use crate::value::Value;

const UTF8: u8 = crate::layout::kind("utf8");
const UTF8_ASCII: u8 = crate::layout::kind("utf8-ascii");
const UTF8_SLICE: u8 = crate::layout::kind("utf8-slice");

/// Where a bytevector's bytes start in its suffix: after its length.
const BYTEVECTOR_BYTES: usize = 8;

/// A slice's values (`Heap::make_frozen`'s order).
const SLICE_OWNER: usize = 0;
const SLICE_START: usize = 1;
const SLICE_END: usize = 2;
const SLICE_ASCII: usize = 3;

impl Heap {
    /// The `utf8` of `text`: marked all ASCII, if it is, here.
    pub fn make_utf8(&mut self, text: &str) -> Value {
        let kind = if text.is_ascii() { UTF8_ASCII } else { UTF8 };
        let u = self.make_bloblet(kind, 0, text.len(), false);
        self.set_bloblet_bytes(u, 0, text.as_bytes()).expect("the suffix made for it");
        self.freeze_bloblet(u, true, true);
        u
    }

    /// Whether `v` is a `utf8`, whole or a slice.
    pub fn is_utf8(&self, v: Value) -> bool {
        v.is_bloblet() && !v.is_suffix_ref() && matches!(self.bloblet_kind(v), UTF8 | UTF8_ASCII | UTF8_SLICE)
    }

    /// Whether `utf8` `u` is a slice.
    pub fn utf8_is_slice(&self, u: Value) -> bool {
        debug_assert!(self.is_utf8(u), "{u:?} is not a utf8");
        self.bloblet_kind(u) == UTF8_SLICE
    }

    /// Where `u`'s text is: the whole `utf8` (or frozen bytevector) whose
    /// suffix holds it, the offset there it starts at, and its length in
    /// bytes.
    fn utf8_span(&self, u: Value) -> (Value, usize, usize) {
        debug_assert!(self.is_utf8(u), "{u:?} is not a utf8");
        if self.bloblet_kind(u) != UTF8_SLICE {
            return (u, 0, self.bloblet_head(u).bytes);
        }
        let at = |i| self.bloblet_value(u, i).as_fixnum() as usize;
        let (start, end) = (at(SLICE_START), at(SLICE_END));
        (self.bloblet_value(u, SLICE_OWNER), start, end - start)
    }

    /// A `utf8` viewing the bytes of bytes view `v` (`TODO.md` §310),
    /// nothing copied, if they are UTF-8: else the offset they are valid up
    /// to. Its owner the bytevector holding them, which must be frozen,
    /// never written after (the caller's type says so: `bytes`, `(bytesof
    /// const)`); marked all ASCII if they are, found here, as they are
    /// validated.
    pub fn utf8_of_bytes(&mut self, v: Value) -> Result<Value, usize> {
        let (owner, start, len) = self.bytes_span(v).expect("a bytes view");
        let bytes = self.bytes_of(v);
        std::str::from_utf8(&bytes).map_err(|e| e.valid_up_to())?;
        let at = BYTEVECTOR_BYTES + start;
        let fields =
            [owner, Value::fixnum(at as i64), Value::fixnum((at + len) as i64), Value::boolean(bytes.is_ascii())];
        Ok(self.make_frozen(UTF8_SLICE, &fields))
    }

    /// Whether `utf8` `u` is marked all ASCII.
    pub fn utf8_is_ascii(&self, u: Value) -> bool {
        match self.bloblet_kind(u) {
            UTF8_SLICE => self.bloblet_value(u, SLICE_ASCII).is_true(),
            k => k == UTF8_ASCII,
        }
    }

    /// `u`'s length in characters: its length in bytes if it is marked all
    /// ASCII, else counted, a walk.
    pub fn utf8_chars(&self, u: Value) -> usize {
        if self.utf8_is_ascii(u) {
            return self.utf8_len(u);
        }
        self.utf8_bytes(u).iter().filter(|b| *b & 0xc0 != 0x80).count()
    }

    /// `u`'s length in bytes.
    pub fn utf8_len(&self, u: Value) -> usize {
        self.utf8_span(u).2
    }

    /// `u`'s bytes, copied out.
    pub fn utf8_bytes(&self, u: Value) -> Vec<u8> {
        let (owner, start, len) = self.utf8_span(u);
        (start..start + len).map(|i| self.bloblet_byte(owner, i).expect("in its owner")).collect()
    }

    /// `u`'s text, copied out.
    pub fn utf8_string(&self, u: Value) -> String {
        String::from_utf8(self.utf8_bytes(u)).expect("a utf8 is made valid")
    }

    /// The byte of `u` at `k`, which must be in range.
    fn utf8_byte(&self, u: Value, k: usize) -> u8 {
        let (owner, start, len) = self.utf8_span(u);
        debug_assert!(k < len, "{k} is past {u:?}");
        self.bloblet_byte(owner, start + k).expect("in range")
    }

    /// A slice of `u`'s bytes from `a` to `b`, each a boundary
    /// (`utf8_boundary`), nothing copied; none if either is not, or
    /// `a > b`. Its owner `u`'s, and its mark.
    pub fn utf8_slice(&mut self, u: Value, a: usize, b: usize) -> Option<Value> {
        if a > b || !self.utf8_boundary(u, a) || !self.utf8_boundary(u, b) {
            return None;
        }
        let (owner, start, _) = self.utf8_span(u);
        let ascii = Value::boolean(self.utf8_is_ascii(u));
        let fields = [owner, Value::fixnum((start + a) as i64), Value::fixnum((start + b) as i64), ascii];
        Some(self.make_frozen(UTF8_SLICE, &fields))
    }

    /// Whether byte offset `k` is where a character of `u` starts (or its
    /// end, `k` its length): in range, and the byte there no continuation
    /// byte (`10xxxxxx`), which, the text valid, makes it a start. O(1).
    pub fn utf8_boundary(&self, u: Value, k: usize) -> bool {
        k == self.utf8_len(u) || (k < self.utf8_len(u) && self.utf8_byte(u, k) & 0xc0 != 0x80)
    }

    /// The character of `u` starting at byte `k`, and the offset after it;
    /// none if no character starts there. O(1): at most four bytes read.
    pub fn utf8_char_at(&self, u: Value, k: usize) -> Option<(char, usize)> {
        if k >= self.utf8_len(u) || !self.utf8_boundary(u, k) {
            return None;
        }
        let b0 = self.utf8_byte(u, k);
        let n = match b0 {
            0x00..=0x7f => 1,
            0xc0..=0xdf => 2,
            0xe0..=0xef => 3,
            _ => 4,
        };
        let bytes: Vec<u8> = (k..k + n).map(|i| self.utf8_byte(u, i)).collect();
        let c = std::str::from_utf8(&bytes).ok()?.chars().next()?;
        Some((c, k + n))
    }

    /// The `utf8` of `u`'s bytes from `a` to `b`, each a boundary
    /// (`utf8_boundary`); none if either is not, or `a > b`.
    pub fn utf8_substring(&mut self, u: Value, a: usize, b: usize) -> Option<Value> {
        if a > b || !self.utf8_boundary(u, a) || !self.utf8_boundary(u, b) {
            return None;
        }
        let bytes: Vec<u8> = (a..b).map(|i| self.utf8_byte(u, i)).collect();
        let text = String::from_utf8(bytes).expect("between boundaries of valid text");
        Some(self.make_utf8(&text))
    }

    /// Whether two `utf8`s have the same text.
    pub fn utf8_eq(&self, a: Value, b: Value) -> bool {
        self.utf8_len(a) == self.utf8_len(b) && self.utf8_bytes(a) == self.utf8_bytes(b)
    }
}
