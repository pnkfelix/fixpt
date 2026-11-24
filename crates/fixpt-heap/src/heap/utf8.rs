//! UTF-8 text (FX-26's `utf8`, `TODO.md` §306): a frozen bloblet of no
//! fields whose suffix is its text, valid UTF-8, the header's B its length
//! in bytes. Indexed by byte offset, as Rust's `str` is: a character is
//! read where one starts, in O(1); the `i`th character is a walk, and so
//! is its count of characters, which is not kept (§310), but for text all
//! ASCII, marked so where it is made, a kind of its own (`utf8-ascii`),
//! whose count is its length. Made only of a `&str`, so never invalid.

use super::Heap;
use crate::value::Value;

const UTF8: u8 = crate::layout::kind("utf8");
const UTF8_ASCII: u8 = crate::layout::kind("utf8-ascii");

impl Heap {
    /// The `utf8` of `text`: marked all ASCII, if it is, here.
    pub fn make_utf8(&mut self, text: &str) -> Value {
        let kind = if text.is_ascii() { UTF8_ASCII } else { UTF8 };
        let u = self.make_bloblet(kind, 0, text.len(), false);
        self.set_bloblet_bytes(u, 0, text.as_bytes()).expect("the suffix made for it");
        self.freeze_bloblet(u, true, true);
        u
    }

    /// Whether `v` is a `utf8`.
    pub fn is_utf8(&self, v: Value) -> bool {
        v.is_bloblet() && !v.is_suffix_ref() && matches!(self.bloblet_kind(v), UTF8 | UTF8_ASCII)
    }

    /// Whether `utf8` `u` is marked all ASCII.
    pub fn utf8_is_ascii(&self, u: Value) -> bool {
        debug_assert!(self.is_utf8(u), "{u:?} is not a utf8");
        self.bloblet_kind(u) == UTF8_ASCII
    }

    /// `u`'s length in characters: its length in bytes if it is marked all
    /// ASCII, else counted, a walk.
    pub fn utf8_chars(&self, u: Value) -> usize {
        if self.utf8_is_ascii(u) {
            return self.utf8_len(u);
        }
        self.bloblet_bytes(u).iter().filter(|b| *b & 0xc0 != 0x80).count()
    }

    /// `u`'s length in bytes.
    pub fn utf8_len(&self, u: Value) -> usize {
        debug_assert!(self.is_utf8(u), "{u:?} is not a utf8");
        self.bloblet_head(u).bytes
    }

    /// `u`'s text, copied out.
    pub fn utf8_string(&self, u: Value) -> String {
        debug_assert!(self.is_utf8(u), "{u:?} is not a utf8");
        String::from_utf8(self.bloblet_bytes(u)).expect("a utf8 is made valid")
    }

    /// The byte of `u` at `k`, which must be in range.
    fn utf8_byte(&self, u: Value, k: usize) -> u8 {
        self.bloblet_byte(u, k).expect("in range")
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
        self.utf8_len(a) == self.utf8_len(b) && self.bloblet_bytes(a) == self.bloblet_bytes(b)
    }
}
