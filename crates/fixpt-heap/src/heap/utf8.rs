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
//! A slice is of the kind `utf8-slice`, its values its owner (a whole
//! `utf8`, never a slice: a slice of a slice is one of the first's owner;
//! or a bytevector frozen, its bytes validated, `utf8_of_bytes`), its
//! start and end, offsets into the owner's suffix in bytes, and its count
//! of characters once known (§310, the user's): known where it is made if
//! that is free (its owner all ASCII, or bytes counted as they are
//! validated), else by the first walk that counts it, which keeps it, so
//! `utf8-length` of a slice is a walk once, O(1) after. Its piece is all
//! ASCII exactly when its count is its length in bytes. So its fields are
//! not frozen: the count is written once, from unknown to known, an
//! immediate, the same whoever writes it, the bytes', so no program sees
//! the write; its kind settable, so an image never puts it in the half a
//! write would fault in. Its owner, start and end are never written. It
//! has a trailer, so the word before its (empty) suffix is never a header,
//! as a whole one's is: what native code tests to read a whole one in
//! line.

use super::Heap;
use crate::value::Value;

const UTF8: u8 = crate::layout::kind("utf8");
const UTF8_ASCII: u8 = crate::layout::kind("utf8-ascii");
const UTF8_SLICE: u8 = crate::layout::kind("utf8-slice");

/// Where a bytevector's bytes start in its suffix: after its length.
const BYTEVECTOR_BYTES: usize = 8;

/// A slice's values (`Heap::bloblet_value`'s order): its fields
/// (`layout::utf8_slice`, native code's) less the trailer's and the one
/// field before value 0.
use crate::layout::utf8_slice;
const SLICE_OWNER: usize = utf8_slice::OWNER - 2;
const SLICE_START: usize = utf8_slice::START - 2;
const SLICE_END: usize = utf8_slice::END - 2;
const SLICE_COUNT: usize = utf8_slice::COUNT - 2;

/// A slice's count as its field holds it: a fixnum, or `#f`, not known yet.
fn count_field(count: Option<usize>) -> Value {
    count.map_or(Value::boolean(false), |n| Value::fixnum(n as i64))
}

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
    #[inline]
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
    #[inline]
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
        let count = count_chars(&bytes);
        Ok(self.make_slice(owner, at, at + len, Some(count)))
    }

    /// A slice of `owner`'s suffix from `start` to `end`, its count `count`
    /// if known: its fields not frozen, for the count (the module's note).
    fn make_slice(&mut self, owner: Value, start: usize, end: usize, count: Option<usize>) -> Value {
        let fields = [owner, Value::fixnum(start as i64), Value::fixnum(end as i64), count_field(count)];
        let b = self.make_bloblet(UTF8_SLICE, fields.len(), 0, true);
        for (i, v) in fields.iter().enumerate() {
            self.set_bloblet_slot(b, i + 2, *v);
        }
        self.freeze_bloblet(b, false, true);
        b
    }

    /// `u`'s count of characters if it is known without a walk: a whole
    /// one's marked all ASCII, its length; a slice's, once kept.
    pub fn utf8_known_chars(&self, u: Value) -> Option<usize> {
        match self.bloblet_kind(u) {
            UTF8_SLICE => {
                let c = self.bloblet_value(u, SLICE_COUNT);
                c.is_fixnum().then(|| c.as_fixnum() as usize)
            }
            UTF8_ASCII => Some(self.bloblet_head(u).bytes),
            _ => None,
        }
    }

    /// Whether `utf8` `u` is known all ASCII: a whole one marked so, or a
    /// slice whose count, known, is its length in bytes.
    pub fn utf8_is_ascii(&self, u: Value) -> bool {
        self.utf8_known_chars(u) == Some(self.utf8_len(u))
    }

    /// `u`'s length in characters: known (`utf8_known_chars`), else
    /// counted, a walk, and a slice keeps it.
    pub fn utf8_chars(&mut self, u: Value) -> usize {
        if let Some(n) = self.utf8_known_chars(u) {
            return n;
        }
        let n = count_chars(self.utf8_text(u));
        if self.utf8_is_slice(u) {
            self.set_bloblet_slot(u, utf8_slice::COUNT, Value::fixnum(n as i64));
        }
        n
    }

    /// `u`'s length in bytes.
    #[inline]
    pub fn utf8_len(&self, u: Value) -> usize {
        self.utf8_span(u).2
    }

    /// `u`'s bytes, lent in place: where its text is found once
    /// (`utf8_span`), then read as a slice, not a byte at a time.
    #[inline]
    pub fn utf8_text(&self, u: Value) -> &[u8] {
        let (owner, start, len) = self.utf8_span(u);
        &self.bloblet_suffix(owner)[start..start + len]
    }

    /// `u`'s bytes, copied out.
    pub fn utf8_bytes(&self, u: Value) -> Vec<u8> {
        self.utf8_text(u).to_vec()
    }

    /// `u`'s text, copied out.
    pub fn utf8_string(&self, u: Value) -> String {
        std::str::from_utf8(self.utf8_text(u)).expect("a utf8 is made valid").to_owned()
    }

    /// A slice of `u`'s bytes from `a` to `b`, each a boundary
    /// (`utf8_boundary`), nothing copied; none if either is not, or
    /// `a > b`. Its owner `u`'s; its count known if `u` is known all
    /// ASCII, or it is the whole of `u` and `u`'s is known, never found by
    /// looking at the piece (a walk, left to the first that counts).
    pub fn utf8_slice(&mut self, u: Value, a: usize, b: usize) -> Option<Value> {
        if a > b || !self.utf8_boundary(u, a) || !self.utf8_boundary(u, b) {
            return None;
        }
        let (owner, start, len) = self.utf8_span(u);
        let count = if self.utf8_is_ascii(u) {
            Some(b - a)
        } else {
            self.utf8_known_chars(u).filter(|_| (a, b) == (0, len))
        };
        Some(self.make_slice(owner, start + a, start + b, count))
    }

    /// Whether byte offset `k` is where a character of `u` starts (or its
    /// end, `k` its length): in range, and the byte there no continuation
    /// byte (`10xxxxxx`), which, the text valid, makes it a start. O(1).
    #[inline]
    pub fn utf8_boundary(&self, u: Value, k: usize) -> bool {
        let t = self.utf8_text(u);
        k == t.len() || t.get(k).is_some_and(|b| b & 0xc0 != 0x80)
    }

    /// The character of `u` starting at byte `k`, and the offset after it;
    /// none if no character starts there. O(1): at most four bytes read.
    #[inline]
    pub fn utf8_char_at(&self, u: Value, k: usize) -> Option<(char, usize)> {
        let t = self.utf8_text(u);
        let b0 = *t.get(k)?;
        // Its continuation bytes' six bits each, after the lead byte's own:
        // valid text, so the lead says how many follow, and they do.
        let (n, lead) = match b0 {
            0x00..=0x7f => return Some((b0 as char, k + 1)),
            0x80..=0xbf => return None,
            0xc0..=0xdf => (2, b0 & 0x1f),
            0xe0..=0xef => (3, b0 & 0x0f),
            _ => (4, b0 & 0x07),
        };
        let c = t[k + 1..k + n].iter().fold(u32::from(lead), |c, b| (c << 6) | u32::from(b & 0x3f));
        Some((char::from_u32(c).expect("a utf8 is made valid"), k + n))
    }

    /// The `utf8` of `u`'s bytes from `a` to `b`, each a boundary
    /// (`utf8_boundary`); none if either is not, or `a > b`.
    pub fn utf8_substring(&mut self, u: Value, a: usize, b: usize) -> Option<Value> {
        if a > b || !self.utf8_boundary(u, a) || !self.utf8_boundary(u, b) {
            return None;
        }
        let text = std::str::from_utf8(&self.utf8_text(u)[a..b]).expect("between boundaries of valid text").to_owned();
        Some(self.make_utf8(&text))
    }

    /// Whether two `utf8`s have the same text.
    pub fn utf8_eq(&self, a: Value, b: Value) -> bool {
        self.utf8_text(a) == self.utf8_text(b)
    }
}

/// How many characters valid UTF-8 `bytes` holds: its bytes that are no
/// continuation byte (`10xxxxxx`, as an `i8` below -64).
fn count_chars(bytes: &[u8]) -> usize {
    bytes.iter().filter(|&&b| (b as i8) >= -64).count()
}
