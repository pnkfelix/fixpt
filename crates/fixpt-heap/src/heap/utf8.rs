//! UTF-8 text (FX-26's `utf8`, `TODO.md` §306): a frozen bloblet whose one
//! field is its length in characters and whose suffix is its text, valid
//! UTF-8, the header's B its length in bytes. Indexed by byte offset, as
//! Rust's `str` is: a character is read where one starts, in O(1); the
//! `i`th character is a walk. Made only of a `&str`, so never invalid.

use super::Heap;
use crate::value::Value;

const UTF8: u8 = crate::layout::kind("utf8");
const UTF8_CHARS: usize = 2;

impl Heap {
    /// The `utf8` of `text`: its characters counted once, here.
    pub fn make_utf8(&mut self, text: &str) -> Value {
        let u = self.make_bloblet(UTF8, 1, text.len(), true);
        self.set_bloblet_slot(u, UTF8_CHARS, Value::fixnum(text.chars().count() as i64));
        self.set_bloblet_bytes(u, 0, text.as_bytes()).expect("the suffix made for it");
        self.freeze_bloblet(u, true, true);
        u
    }

    /// Whether `v` is a `utf8`.
    pub fn is_utf8(&self, v: Value) -> bool {
        v.is_bloblet() && !v.is_suffix_ref() && self.bloblet_kind(v) == UTF8
    }

    /// `u`'s length in characters.
    pub fn utf8_chars(&self, u: Value) -> usize {
        debug_assert!(self.is_utf8(u), "{u:?} is not a utf8");
        self.bloblet_slot(u, UTF8_CHARS).as_fixnum() as usize
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
