//! The `Value` representation: one 64-bit word, low-3-bit tagged.
//!
//! Every reference is a **word offset into the active semispace**, never a Rust
//! pointer. That is what lets the collector move objects, lets a heap image be
//! written with `write_all` and read back with no relocation pass, and lets the
//! whole system avoid reference counting.
//!
//! ```text
//! tag 000  fixnum       value = (w as i64) >> 3          (61-bit signed)
//! tag 001  pair         (w >> 3) = index of a 2-word car/cdr cell
//! tag 010  object       (w >> 3) = index of a header word
//! tag 011  immediate    subtag in bits 3..8, payload in bits 8..64
//! tag 100  reserved
//! tag 101  reserved
//! tag 110  header       never a Value; marks an object header word (see below)
//! tag 111  forwarding   GC-internal; never observable outside a collection
//! ```
//!
//! Tag `110` is deliberately not producible by any constructor here. That is
//! what makes a linear scan of to-space unambiguous: at any object boundary the
//! first word is either a header (tag `110`, so an object of known length
//! follows) or an ordinary `Value` (so a 2-word pair cell follows). Without a
//! reserved pattern, a pair whose car happened to look like a header would
//! desynchronise the scan.

use core::fmt;

pub const TAG_MASK: u64 = 0b111;
pub const TAG_FIXNUM: u64 = 0b000;
pub const TAG_PAIR: u64 = 0b001;
pub const TAG_OBJECT: u64 = 0b010;
pub const TAG_IMMEDIATE: u64 = 0b011;
pub const TAG_HEADER: u64 = 0b110;
pub const TAG_FORWARD: u64 = 0b111;

/// Fixnums are 61-bit signed.
pub const FIXNUM_BITS: u32 = 61;
pub const FIXNUM_MAX: i64 = (1 << (FIXNUM_BITS - 1)) - 1;
pub const FIXNUM_MIN: i64 = -(1 << (FIXNUM_BITS - 1));

// Immediate subtags, bits 3..8.
const IMM_FALSE: u64 = 0;
const IMM_TRUE: u64 = 1;
const IMM_NULL: u64 = 2;
const IMM_UNIT: u64 = 3;
const IMM_EOF: u64 = 4;
const IMM_UNSPECIFIED: u64 = 5;
const IMM_DEFAULT: u64 = 6;
const IMM_UNBOUND: u64 = 7;
const IMM_CHAR: u64 = 8;

const IMM_SHIFT: u32 = 3;
const IMM_MASK: u64 = 0b1_1111;
const IMM_PAYLOAD_SHIFT: u32 = 8;

/// A Scheme value. `Copy`, so it is cheap to pass around — but see the module
/// docs in `heap`: a `Value` held across a *collection* is stale. It stays
/// valid across allocation, which never moves anything.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Value(pub u64);

impl Value {
    #[inline]
    pub const fn raw(self) -> u64 {
        self.0
    }
    #[inline]
    pub const fn tag(self) -> u64 {
        self.0 & TAG_MASK
    }

    // ---------------------------------------------------------------- fixnums
    #[inline]
    pub const fn fixnum(n: i64) -> Value {
        Value((n as u64) << 3)
    }
    #[inline]
    pub const fn is_fixnum(self) -> bool {
        self.tag() == TAG_FIXNUM
    }
    #[inline]
    pub const fn as_fixnum(self) -> i64 {
        (self.0 as i64) >> 3
    }
    /// `None` when `n` does not fit in 61 bits, so callers can promote to a bignum.
    #[inline]
    pub const fn try_fixnum(n: i64) -> Option<Value> {
        if n >= FIXNUM_MIN && n <= FIXNUM_MAX { Some(Value::fixnum(n)) } else { None }
    }

    // ------------------------------------------------------------- references
    #[inline]
    pub const fn pair(index: usize) -> Value {
        Value(((index as u64) << 3) | TAG_PAIR)
    }
    #[inline]
    pub const fn is_pair(self) -> bool {
        self.tag() == TAG_PAIR
    }
    #[inline]
    pub const fn object(index: usize) -> Value {
        Value(((index as u64) << 3) | TAG_OBJECT)
    }
    #[inline]
    pub const fn is_object(self) -> bool {
        self.tag() == TAG_OBJECT
    }
    /// Word index of the referent. Only meaningful for pairs and objects.
    #[inline]
    pub const fn index(self) -> usize {
        (self.0 >> 3) as usize
    }
    /// True for anything the collector must trace.
    #[inline]
    pub const fn is_ref(self) -> bool {
        matches!(self.tag(), TAG_PAIR | TAG_OBJECT)
    }

    // ------------------------------------------------------------- immediates
    #[inline]
    const fn imm(subtag: u64, payload: u64) -> Value {
        Value((payload << IMM_PAYLOAD_SHIFT) | (subtag << IMM_SHIFT) | TAG_IMMEDIATE)
    }
    #[inline]
    pub const fn is_immediate(self) -> bool {
        self.tag() == TAG_IMMEDIATE
    }
    #[inline]
    const fn subtag(self) -> u64 {
        (self.0 >> IMM_SHIFT) & IMM_MASK
    }
    #[inline]
    const fn is_imm(self, subtag: u64) -> bool {
        self.is_immediate() && self.subtag() == subtag
    }

    pub const FALSE: Value = Value::imm(IMM_FALSE, 0);
    pub const TRUE: Value = Value::imm(IMM_TRUE, 0);
    /// The empty list, `'()`.
    pub const NULL: Value = Value::imm(IMM_NULL, 0);
    /// FX's unit value, `#u`. Distinct from `unspecified`, which is Scheme's.
    pub const UNIT: Value = Value::imm(IMM_UNIT, 0);
    pub const EOF: Value = Value::imm(IMM_EOF, 0);
    pub const UNSPECIFIED: Value = Value::imm(IMM_UNSPECIFIED, 0);
    /// The value of an omitted optional argument.
    pub const DEFAULT: Value = Value::imm(IMM_DEFAULT, 0);
    /// Fills an unassigned global slot or a `letrec` binding before its
    /// initialiser runs; referencing one is an error, which is how R7RS
    /// `letrec` restrictions get enforced.
    pub const UNBOUND: Value = Value::imm(IMM_UNBOUND, 0);

    #[inline]
    pub const fn boolean(b: bool) -> Value {
        if b { Value::TRUE } else { Value::FALSE }
    }
    #[inline]
    pub const fn is_false(self) -> bool {
        self.0 == Value::FALSE.0
    }
    /// Scheme truthiness: everything except `#f` is true.
    #[inline]
    pub const fn is_true(self) -> bool {
        self.0 != Value::FALSE.0
    }
    #[inline]
    pub const fn is_null(self) -> bool {
        self.is_imm(IMM_NULL)
    }
    #[inline]
    pub const fn is_unit(self) -> bool {
        self.is_imm(IMM_UNIT)
    }
    #[inline]
    pub const fn is_eof(self) -> bool {
        self.is_imm(IMM_EOF)
    }
    #[inline]
    pub const fn is_unbound(self) -> bool {
        self.is_imm(IMM_UNBOUND)
    }
    #[inline]
    pub const fn is_boolean(self) -> bool {
        self.is_imm(IMM_FALSE) || self.is_imm(IMM_TRUE)
    }

    #[inline]
    pub const fn char(c: char) -> Value {
        Value::imm(IMM_CHAR, c as u64)
    }
    #[inline]
    pub const fn is_char(self) -> bool {
        self.is_imm(IMM_CHAR)
    }
    #[inline]
    pub fn as_char(self) -> char {
        char::from_u32((self.0 >> IMM_PAYLOAD_SHIFT) as u32).expect("valid char payload")
    }

    // --------------------------------------------------------- GC-private bits
    #[inline]
    pub(crate) const fn forward(index: usize) -> Value {
        Value(((index as u64) << 3) | TAG_FORWARD)
    }
    #[inline]
    pub(crate) const fn is_forward(self) -> bool {
        self.tag() == TAG_FORWARD
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.tag() {
            TAG_FIXNUM => write!(f, "{}", self.as_fixnum()),
            TAG_PAIR => write!(f, "#<pair @{}>", self.index()),
            TAG_OBJECT => write!(f, "#<obj @{}>", self.index()),
            TAG_IMMEDIATE => match self.subtag() {
                IMM_FALSE => f.write_str("#f"),
                IMM_TRUE => f.write_str("#t"),
                IMM_NULL => f.write_str("()"),
                IMM_UNIT => f.write_str("#u"),
                IMM_EOF => f.write_str("#<eof>"),
                IMM_UNSPECIFIED => f.write_str("#<unspecified>"),
                IMM_DEFAULT => f.write_str("#<default>"),
                IMM_UNBOUND => f.write_str("#<unbound>"),
                IMM_CHAR => write!(f, "#\\{}", self.as_char()),
                s => write!(f, "#<immediate {s}>"),
            },
            TAG_FORWARD => write!(f, "#<forward @{}>", self.index()),
            t => write!(f, "#<bad-tag {t} {:#x}>", self.0),
        }
    }
}

// ---------------------------------------------------------------------- header

/// Object header word. `len` counts payload words, uniformly for every object
/// type, so the collector can skip a non-scanned payload without knowing what
/// it means.
///
/// ```text
/// bits 24..64  len (payload words)
/// bits  8..24  type code
/// bits  0..8   TAG_HEADER
/// ```
#[inline]
pub const fn make_header(ty: ObjType, len: usize) -> u64 {
    ((len as u64) << 24) | ((ty as u64) << 8) | TAG_HEADER
}
#[inline]
pub const fn header_len(h: u64) -> usize {
    (h >> 24) as usize
}
#[inline]
pub const fn header_type_code(h: u64) -> u16 {
    ((h >> 8) & 0xffff) as u16
}
#[inline]
pub const fn is_header(w: u64) -> bool {
    w & TAG_MASK == TAG_HEADER
}

/// Every kind of heap object. Deliberately a small closed set: FX's own runtime
/// shapes (`*module*`, `*sum*`, `*product*`) are ordinary [`ObjType::Record`]s
/// rather than new cases, exactly as `code.scm` builds them out of ordinary
/// Scheme lists and vectors.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u16)]
pub enum ObjType {
    /// `[charlen, packed u32 code points, 2 per word]`
    String = 1,
    /// `[name:String, hash, global-slot]`
    Symbol = 2,
    /// `[elems…]`
    Vector = 3,
    /// `[bytelen, bytes…]`
    Bytevector = 4,
    /// `[f64 bits]`
    Flonum = 5,
    /// `[negative?, nlimbs, u64 limbs…]` little-endian
    Bignum = 6,
    /// `[numerator, denominator]`, both exact integers, den > 1, gcd 1
    Ratnum = 7,
    /// `[code:Code, captured…]`
    Closure = 8,
    /// `[name, arity, consts:Vector, bytecode:Bytevector]`
    Code = 9,
    /// `[value]` — the cell an assignment-converted variable lives in
    Box = 10,
    /// `[rtd:RecordType, fields…]`
    Record = 11,
    /// `[name:Symbol, field-names:Vector]`
    RecordType = 12,
    /// `[kind, id, buffer, position]`
    Port = 13,
    /// `[saved-stack:Vector, winders]`
    Continuation = 14,
    /// `[vals…]` — the result of `(values …)` with n /= 1
    Values = 15,
    /// `[forced?, value-or-thunk]`
    Promise = 16,
    /// `[kind, count, buckets:Vector]`
    HashTable = 17,
    /// `[parent, names:Vector, values:Vector]` — first-class `eval` environments
    Environment = 18,
    /// `[name:Symbol, index, arity-min, arity-max]`
    Primitive = 19,
}

impl ObjType {
    pub fn from_code(c: u16) -> Option<ObjType> {
        use ObjType::*;
        Some(match c {
            1 => String,
            2 => Symbol,
            3 => Vector,
            4 => Bytevector,
            5 => Flonum,
            6 => Bignum,
            7 => Ratnum,
            8 => Closure,
            9 => Code,
            10 => Box,
            11 => Record,
            12 => RecordType,
            13 => Port,
            14 => Continuation,
            15 => Values,
            16 => Promise,
            17 => HashTable,
            18 => Environment,
            19 => Primitive,
            _ => return None,
        })
    }

    /// Whether the payload words are `Value`s the collector must trace.
    ///
    /// The four `false` cases hold raw bits — characters, bytes, an `f64`,
    /// bignum limbs — which would be catastrophic to trace as if they were
    /// references.
    #[inline]
    pub const fn payload_is_scanned(self) -> bool {
        !matches!(self, ObjType::String | ObjType::Bytevector | ObjType::Flonum | ObjType::Bignum)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixnum_roundtrip() {
        for n in [0i64, 1, -1, 42, -42, FIXNUM_MAX, FIXNUM_MIN] {
            let v = Value::fixnum(n);
            assert!(v.is_fixnum(), "{n} should be a fixnum");
            assert_eq!(v.as_fixnum(), n);
        }
        assert!(Value::try_fixnum(FIXNUM_MAX).is_some());
        assert!(Value::try_fixnum(FIXNUM_MAX + 1).is_none());
        assert!(Value::try_fixnum(FIXNUM_MIN - 1).is_none());
    }

    #[test]
    fn immediates_are_distinct() {
        let all = [
            Value::FALSE,
            Value::TRUE,
            Value::NULL,
            Value::UNIT,
            Value::EOF,
            Value::UNSPECIFIED,
            Value::DEFAULT,
            Value::UNBOUND,
        ];
        for (i, a) in all.iter().enumerate() {
            for (j, b) in all.iter().enumerate() {
                assert_eq!(i == j, a == b, "{a:?} vs {b:?}");
            }
            assert!(a.is_immediate());
            assert!(!a.is_ref());
        }
    }

    #[test]
    fn scheme_truthiness_is_only_false() {
        assert!(Value::FALSE.is_false());
        for v in [Value::TRUE, Value::NULL, Value::UNIT, Value::fixnum(0), Value::char('\0')] {
            assert!(v.is_true(), "{v:?} must be true in Scheme");
        }
    }

    #[test]
    fn chars_roundtrip() {
        for c in ['a', '\0', 'λ', '\u{10FFFF}'] {
            let v = Value::char(c);
            assert!(v.is_char());
            assert_eq!(v.as_char(), c);
        }
    }

    #[test]
    fn header_tag_is_unreachable_from_any_value_constructor() {
        // The whole linear-scan design rests on this.
        let candidates = [
            Value::fixnum(-1),
            Value::fixnum(i64::MAX >> 3),
            Value::pair(usize::MAX >> 3),
            Value::object(usize::MAX >> 3),
            Value::TRUE,
            Value::char('\u{10FFFF}'),
            Value::UNBOUND,
        ];
        for v in candidates {
            assert_ne!(v.tag(), TAG_HEADER, "{v:?} collides with the header tag");
        }
    }

    #[test]
    fn header_roundtrip() {
        for ty in [ObjType::String, ObjType::Vector, ObjType::Code, ObjType::Primitive] {
            for len in [0usize, 1, 7, 1 << 20] {
                let h = make_header(ty, len);
                assert!(is_header(h));
                assert_eq!(header_len(h), len);
                assert_eq!(ObjType::from_code(header_type_code(h)), Some(ty));
            }
        }
    }

    #[test]
    fn raw_payload_types_are_not_scanned() {
        for ty in [ObjType::String, ObjType::Bytevector, ObjType::Flonum, ObjType::Bignum] {
            assert!(!ty.payload_is_scanned(), "{ty:?} holds raw bits");
        }
        for ty in [ObjType::Vector, ObjType::Closure, ObjType::Record, ObjType::Code] {
            assert!(ty.payload_is_scanned(), "{ty:?} holds references");
        }
    }
}
