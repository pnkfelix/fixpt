//! Views into bytes and into a string (`TODO.md` §310): a *slice*, a view
//! of a piece of a whole bytevector or string, nothing copied. To FX-26 a
//! `(bytesof r)` or a `(strof r)` is a whole buffer or a slice of one;
//! read only, so a slice is frozen, and sees the writes made to its owner.
//!
//! A slice is a frozen bloblet of a kind of its own, `bytes-slice` or
//! `str-slice`, its values its owner (a whole buffer, never a slice: a
//! slice of a slice is one of the first's owner) and its start and end,
//! counted in the owner's elements (bytes, or characters); a trailer. A
//! `utf8`'s slice is its own (`utf8.rs`).

use super::Heap;
use crate::value::Value;
use crate::ObjType;

const BYTES_SLICE: u8 = crate::layout::kind("bytes-slice");
const STR_SLICE: u8 = crate::layout::kind("str-slice");

/// A slice's values (`Heap::make_frozen`'s order).
const SLICE_OWNER: usize = 0;
const SLICE_START: usize = 1;
const SLICE_END: usize = 2;

impl Heap {
    /// Where the bytes of `v` are, if it is a bytes view: the whole
    /// bytevector that holds them, where they start in it, and how many.
    pub fn bytes_span(&self, v: Value) -> Option<(Value, usize, usize)> {
        if self.is_a(v, ObjType::Bytevector) {
            return Some((v, 0, self.bytevector_len(v)));
        }
        self.slice_span(v, BYTES_SLICE)
    }

    /// Where the characters of `v` are, if it is a string view, as
    /// `bytes_span` says of bytes.
    pub fn str_span(&self, v: Value) -> Option<(Value, usize, usize)> {
        if self.is_a(v, ObjType::String) {
            return Some((v, 0, self.string_len(v)));
        }
        self.slice_span(v, STR_SLICE)
    }

    fn slice_span(&self, v: Value, kind: u8) -> Option<(Value, usize, usize)> {
        if !v.is_bloblet() || v.is_suffix_ref() || self.bloblet_kind(v) != kind {
            return None;
        }
        let at = |i| self.bloblet_value(v, i).as_fixnum() as usize;
        let (start, end) = (at(SLICE_START), at(SLICE_END));
        Some((self.bloblet_value(v, SLICE_OWNER), start, end - start))
    }

    /// A slice of bytes view `v`, its elements `a` to `b` (`a ≤ b ≤` its
    /// length, the caller's to check), of its owner.
    pub fn bytes_slice(&mut self, v: Value, a: usize, b: usize) -> Value {
        let (owner, start, len) = self.bytes_span(v).expect("a bytes view");
        debug_assert!(a <= b && b <= len, "{a}..{b} is not in {len}");
        self.make_frozen(BYTES_SLICE, &[owner, Value::fixnum((start + a) as i64), Value::fixnum((start + b) as i64)])
    }

    /// A slice of string view `v`, its characters `a` to `b`, so.
    pub fn str_slice(&mut self, v: Value, a: usize, b: usize) -> Value {
        let (owner, start, len) = self.str_span(v).expect("a string view");
        debug_assert!(a <= b && b <= len, "{a}..{b} is not in {len}");
        self.make_frozen(STR_SLICE, &[owner, Value::fixnum((start + a) as i64), Value::fixnum((start + b) as i64)])
    }

    /// Whether `v` is a slice of bytes or of a string (not a whole buffer).
    pub fn is_view_slice(&self, v: Value) -> bool {
        v.is_bloblet() && !v.is_suffix_ref() && matches!(self.bloblet_kind(v), BYTES_SLICE | STR_SLICE)
    }

    /// The bytes of bytes view `v`, copied out.
    pub fn bytes_of(&self, v: Value) -> Vec<u8> {
        let (owner, start, len) = self.bytes_span(v).expect("a bytes view");
        (start..start + len).map(|i| self.bytevector_ref(owner, i)).collect()
    }

    /// The characters of string view `v`, copied out.
    pub fn str_chars(&self, v: Value) -> Vec<char> {
        let (owner, start, len) = self.str_span(v).expect("a string view");
        (start..start + len).map(|i| self.string_ref(owner, i)).collect()
    }
}
