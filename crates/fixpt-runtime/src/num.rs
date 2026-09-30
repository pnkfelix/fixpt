//! The numeric tower: fixnum, bignum, exact rational, flonum.
//!
//! Scope, per the project brief: exact integers of unbounded size, exact
//! rationals, and inexact reals. No complex numbers, and none of the deeper
//! exactness-contagion corner cases. Rationals are in rather than out
//! specifically so that `/` behaves the way R7RS says — `(/ 1 3)` is `1/3`, not
//! a silently inexact `0.333…`, which would be a divergence visible in the
//! first minute of using the thing.
//!
//! Numbers move between the heap and [`N`] for arithmetic. The heap
//! representation is a fixnum where one fits and a boxed object otherwise;
//! [`N::store`] always renormalises down, so `(+ (expt 2 100) (- (expt 2 100)))`
//! comes back a fixnum `0` and `eqv?` works as expected.

use fixpt_heap::{Heap, ObjType, Value};
use num_bigint::{BigInt, Sign};
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};

/// A number lifted out of the heap.
#[derive(Clone, Debug, PartialEq)]
pub enum N {
    Fix(i64),
    Big(BigInt),
    /// Always in lowest terms with a positive denominator greater than one —
    /// [`N::store`] and [`N::rat`] maintain that, so a rational is never an
    /// integer in disguise.
    Rat(BigRational),
    Flo(f64),
}

impl N {
    pub fn is_exact(&self) -> bool {
        !matches!(self, N::Flo(_))
    }
    pub fn is_integer(&self) -> bool {
        match self {
            N::Fix(_) | N::Big(_) => true,
            N::Rat(_) => false,
            N::Flo(x) => x.fract() == 0.0 && x.is_finite(),
        }
    }
    pub fn is_zero(&self) -> bool {
        match self {
            N::Fix(n) => *n == 0,
            N::Big(b) => b.is_zero(),
            N::Rat(r) => r.is_zero(),
            N::Flo(x) => *x == 0.0,
        }
    }
    pub fn is_negative(&self) -> bool {
        match self {
            N::Fix(n) => *n < 0,
            N::Big(b) => b.is_negative(),
            N::Rat(r) => r.is_negative(),
            N::Flo(x) => *x < 0.0,
        }
    }

    /// Build a rational, collapsing to an integer when the denominator is 1.
    pub fn rat(r: BigRational) -> N {
        if r.denom().eq(&BigInt::from(1)) { N::big(r.numer().clone()) } else { N::Rat(r) }
    }
    /// Build an integer, collapsing to a fixnum when it fits.
    pub fn big(b: BigInt) -> N {
        match b.to_i64() {
            Some(n) if Value::try_fixnum(n).is_some() => N::Fix(n),
            _ => N::Big(b),
        }
    }

    pub fn to_bigint(&self) -> Option<BigInt> {
        match self {
            N::Fix(n) => Some(BigInt::from(*n)),
            N::Big(b) => Some(b.clone()),
            N::Rat(_) => None,
            N::Flo(x) if x.fract() == 0.0 && x.is_finite() => Some(BigInt::from(*x as i128)),
            N::Flo(_) => None,
        }
    }

    pub fn to_f64(&self) -> f64 {
        match self {
            N::Fix(n) => *n as f64,
            N::Big(b) => b.to_f64().unwrap_or(f64::INFINITY),
            N::Rat(r) => r.to_f64().unwrap_or(f64::NAN),
            N::Flo(x) => *x,
        }
    }

    fn to_rational(&self) -> BigRational {
        match self {
            N::Fix(n) => BigRational::from(BigInt::from(*n)),
            N::Big(b) => BigRational::from(b.clone()),
            N::Rat(r) => r.clone(),
            N::Flo(_) => unreachable!("to_rational is only called on exact values"),
        }
    }

    // ------------------------------------------------------------- heap I/O
    pub fn load(heap: &Heap, v: Value) -> Option<N> {
        if v.is_fixnum() {
            return Some(N::Fix(v.as_fixnum()));
        }
        match heap.obj_type(v)? {
            ObjType::Flonum => Some(N::Flo(heap.flonum_value(v))),
            ObjType::Bignum => Some(N::Big(read_bignum(heap, v))),
            ObjType::Ratnum => {
                let num = N::load(heap, heap.obj_ref(v, 0))?.to_bigint()?;
                let den = N::load(heap, heap.obj_ref(v, 1))?.to_bigint()?;
                Some(N::Rat(BigRational::new_raw(num, den)))
            }
            _ => None,
        }
    }

    pub fn store(&self, heap: &mut Heap) -> Value {
        match self {
            N::Fix(n) => match Value::try_fixnum(*n) {
                Some(v) => v,
                None => write_bignum(heap, &BigInt::from(*n)),
            },
            N::Big(b) => match b.to_i64().and_then(Value::try_fixnum) {
                Some(v) => v,
                None => write_bignum(heap, b),
            },
            N::Rat(r) => {
                if r.denom().eq(&BigInt::from(1)) {
                    return N::big(r.numer().clone()).store(heap);
                }
                let num = N::big(r.numer().clone()).store(heap);
                let den = N::big(r.denom().clone()).store(heap);
                let o = heap.alloc(ObjType::Ratnum, 2, Value::fixnum(0));
                heap.obj_set(o, 0, num);
                heap.obj_set(o, 1, den);
                o
            }
            N::Flo(x) => heap.make_flonum(*x),
        }
    }

    // ---------------------------------------------------------- arithmetic
    /// Raise both operands to a common representation. Inexactness is
    /// contagious, as R7RS requires.
    fn unify(a: &N, b: &N) -> (N, N) {
        use N::*;
        match (a, b) {
            (Flo(_), _) | (_, Flo(_)) => (Flo(a.to_f64()), Flo(b.to_f64())),
            (Rat(_), _) | (_, Rat(_)) => (Rat(a.to_rational()), Rat(b.to_rational())),
            (Big(_), _) | (_, Big(_)) => {
                (Big(a.to_bigint().unwrap()), Big(b.to_bigint().unwrap()))
            }
            (Fix(x), Fix(y)) => (Fix(*x), Fix(*y)),
        }
    }

    pub fn add(&self, other: &N) -> N {
        match N::unify(self, other) {
            // Overflow promotes rather than wrapping: silent wraparound in an
            // exact integer would be a correctness bug, not a performance
            // trade-off.
            (N::Fix(a), N::Fix(b)) => match a.checked_add(b) {
                Some(n) => N::big(BigInt::from(n)),
                None => N::big(BigInt::from(a) + BigInt::from(b)),
            },
            (N::Big(a), N::Big(b)) => N::big(a + b),
            (N::Rat(a), N::Rat(b)) => N::rat(a + b),
            (N::Flo(a), N::Flo(b)) => N::Flo(a + b),
            _ => unreachable!("unify returns a matched pair"),
        }
    }

    pub fn sub(&self, other: &N) -> N {
        match N::unify(self, other) {
            (N::Fix(a), N::Fix(b)) => match a.checked_sub(b) {
                Some(n) => N::big(BigInt::from(n)),
                None => N::big(BigInt::from(a) - BigInt::from(b)),
            },
            (N::Big(a), N::Big(b)) => N::big(a - b),
            (N::Rat(a), N::Rat(b)) => N::rat(a - b),
            (N::Flo(a), N::Flo(b)) => N::Flo(a - b),
            _ => unreachable!(),
        }
    }

    pub fn mul(&self, other: &N) -> N {
        match N::unify(self, other) {
            (N::Fix(a), N::Fix(b)) => match a.checked_mul(b) {
                Some(n) => N::big(BigInt::from(n)),
                None => N::big(BigInt::from(a) * BigInt::from(b)),
            },
            (N::Big(a), N::Big(b)) => N::big(a * b),
            (N::Rat(a), N::Rat(b)) => N::rat(a * b),
            (N::Flo(a), N::Flo(b)) => N::Flo(a * b),
            _ => unreachable!(),
        }
    }

    /// `/`. Exact division of exact operands yields an exact rational — this is
    /// the reason rationals are in scope at all.
    pub fn div(&self, other: &N) -> Result<N, NumError> {
        if other.is_zero() && other.is_exact() {
            return Err(NumError::DivideByZero);
        }
        Ok(match N::unify(self, other) {
            (N::Flo(a), N::Flo(b)) => N::Flo(a / b),
            (a, b) => N::rat(a.to_rational() / b.to_rational()),
        })
    }

    pub fn quotient(&self, other: &N) -> Result<N, NumError> {
        self.int_div(other, |a, b| a / b)
    }
    pub fn remainder(&self, other: &N) -> Result<N, NumError> {
        self.int_div(other, |a, b| a % b)
    }
    /// `modulo` takes the sign of the divisor; `remainder` takes the sign of
    /// the dividend. Conflating them is a classic source of off-by-a-modulus.
    pub fn modulo(&self, other: &N) -> Result<N, NumError> {
        self.int_div(other, |a, b| a.mod_floor(&b))
    }

    fn int_div(&self, other: &N, f: impl Fn(BigInt, BigInt) -> BigInt) -> Result<N, NumError> {
        if other.is_zero() {
            return Err(NumError::DivideByZero);
        }
        let inexact = !self.is_exact() || !other.is_exact();
        let a = self.to_bigint().ok_or(NumError::NotAnInteger)?;
        let b = other.to_bigint().ok_or(NumError::NotAnInteger)?;
        let r = N::big(f(a, b));
        Ok(if inexact { N::Flo(r.to_f64()) } else { r })
    }

    pub fn neg(&self) -> N {
        N::Fix(0).sub(self)
    }

    pub fn abs(&self) -> N {
        if self.is_negative() { self.neg() } else { self.clone() }
    }

    pub fn cmp_num(&self, other: &N) -> Option<std::cmp::Ordering> {
        match N::unify(self, other) {
            (N::Fix(a), N::Fix(b)) => Some(a.cmp(&b)),
            (N::Big(a), N::Big(b)) => Some(a.cmp(&b)),
            (N::Rat(a), N::Rat(b)) => Some(a.cmp(&b)),
            (N::Flo(a), N::Flo(b)) => a.partial_cmp(&b),
            _ => unreachable!(),
        }
    }

    pub fn num_eq(&self, other: &N) -> bool {
        self.cmp_num(other) == Some(std::cmp::Ordering::Equal)
    }

    pub fn expt(&self, other: &N) -> Result<N, NumError> {
        match other {
            N::Fix(e) if self.is_exact() => {
                let e = *e;
                if e >= 0 {
                    let n = u32::try_from(e).map_err(|_| NumError::ExponentTooLarge)?;
                    Ok(match self {
                        N::Rat(r) => N::rat(r.pow(n as i32)),
                        _ => N::big(self.to_bigint().unwrap().pow(n)),
                    })
                } else {
                    let n = u32::try_from(-e).map_err(|_| NumError::ExponentTooLarge)?;
                    let base = self.to_rational();
                    if base.is_zero() {
                        return Err(NumError::DivideByZero);
                    }
                    Ok(N::rat(base.recip().pow(n as i32)))
                }
            }
            _ => Ok(N::Flo(self.to_f64().powf(other.to_f64()))),
        }
    }

    pub fn gcd(&self, other: &N) -> Result<N, NumError> {
        let a = self.to_bigint().ok_or(NumError::NotAnInteger)?;
        let b = other.to_bigint().ok_or(NumError::NotAnInteger)?;
        Ok(N::big(a.gcd(&b)))
    }

    pub fn exact(&self) -> Result<N, NumError> {
        Ok(match self {
            N::Flo(x) => {
                if !x.is_finite() {
                    return Err(NumError::NotExact);
                }
                N::rat(BigRational::from_float(*x).ok_or(NumError::NotExact)?)
            }
            n => n.clone(),
        })
    }
    pub fn inexact(&self) -> N {
        N::Flo(self.to_f64())
    }

    /// `floor`, `ceiling`, `truncate` and `round`, sharing one implementation
    /// so their exactness behaviour cannot drift apart.
    pub fn round_with(&self, mode: RoundMode) -> N {
        match self {
            N::Fix(_) | N::Big(_) => self.clone(),
            N::Rat(r) => N::rat(match mode {
                RoundMode::Floor => r.floor(),
                RoundMode::Ceiling => r.ceil(),
                RoundMode::Truncate => r.trunc(),
                // R7RS `round` is round-half-to-even.
                RoundMode::Round => r.round_ties_even_impl(),
            }),
            N::Flo(x) => N::Flo(match mode {
                RoundMode::Floor => x.floor(),
                RoundMode::Ceiling => x.ceil(),
                RoundMode::Truncate => x.trunc(),
                RoundMode::Round => round_half_even(*x),
            }),
        }
    }

    pub fn numerator(&self) -> N {
        match self {
            N::Rat(r) => N::big(r.numer().clone()),
            n => n.clone(),
        }
    }
    pub fn denominator(&self) -> N {
        match self {
            N::Rat(r) => N::big(r.denom().clone()),
            _ => N::Fix(1),
        }
    }

    pub fn sqrt(&self) -> N {
        // An exact perfect square stays exact, which R7RS recommends and which
        // programs that compute with integer geometry rely on.
        if self.is_exact()
            && !self.is_negative()
            && let Some(b) = self.to_bigint()
        {
            let r = b.sqrt();
            if &r * &r == b {
                return N::big(r);
            }
        }
        N::Flo(self.to_f64().sqrt())
    }

    pub fn to_string_radix(&self, radix: u32) -> String {
        match self {
            N::Fix(n) => match radix {
                10 => n.to_string(),
                r => BigInt::from(*n).to_str_radix(r),
            },
            N::Big(b) => b.to_str_radix(radix),
            N::Rat(r) => {
                format!("{}/{}", r.numer().to_str_radix(radix), r.denom().to_str_radix(radix))
            }
            N::Flo(x) => format_flonum(*x),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum RoundMode {
    Floor,
    Ceiling,
    Truncate,
    Round,
}

/// FX-26's `int` operation `op` (`add`, `sub`, `mul`, `quotient`,
/// `modulo`, `remainder`, `less`, `eq`) on exact integers, fixnums or bignums: what every
/// machine's slow path computes, and the lowering's primitives. A result
/// that fits a fixnum is one. None where an operand is no exact integer, or
/// a divisor is 0. It allocates, and never collects.
pub fn int_op(heap: &mut Heap, op: &str, a: Value, b: Value) -> Option<Value> {
    let (x, y) = (N::load(heap, a)?, N::load(heap, b)?);
    if !(x.is_exact() && x.is_integer() && y.is_exact() && y.is_integer()) {
        return None;
    }
    let n = match op {
        "add" => x.add(&y),
        "sub" => x.sub(&y),
        "mul" => x.mul(&y),
        "quotient" => x.quotient(&y).ok()?,
        "modulo" => x.modulo(&y).ok()?,
        "remainder" => x.remainder(&y).ok()?,
        "less" => return Some(Value::boolean(x.cmp_num(&y) == Some(std::cmp::Ordering::Less))),
        "eq" => return Some(Value::boolean(x.num_eq(&y))),
        _ => return None,
    };
    Some(n.store(heap))
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum NumError {
    DivideByZero,
    NotAnInteger,
    NotExact,
    ExponentTooLarge,
}

impl std::fmt::Display for NumError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            NumError::DivideByZero => "division by zero",
            NumError::NotAnInteger => "expected an integer",
            NumError::NotExact => "cannot be represented exactly",
            NumError::ExponentTooLarge => "exponent is too large",
        })
    }
}

/// An `f32`, as `format_flonum` writes a double: the shortest decimal that
/// reads back as the same binary32.
pub fn format_f32(x: f32) -> String {
    if x.is_nan() {
        return "+nan.0".into();
    }
    if x.is_infinite() {
        return if x > 0.0 { "+inf.0".into() } else { "-inf.0".into() };
    }
    let s = format!("{x}");
    if s.contains(['.', 'e', 'E']) { s } else { format!("{s}.0") }
}

/// R7RS `number->string` on an inexact value must produce something `read`
/// turns back into an inexact number, so an integral flonum keeps its `.0`.
pub fn format_flonum(x: f64) -> String {
    if x.is_nan() {
        return "+nan.0".into();
    }
    if x.is_infinite() {
        return if x > 0.0 { "+inf.0".into() } else { "-inf.0".into() };
    }
    if x == x.trunc() && x.abs() < 1e21 {
        format!("{x:.1}")
    } else {
        let s = format!("{x}");
        if s.contains(['.', 'e', 'E']) { s } else { format!("{s}.0") }
    }
}

fn round_half_even(x: f64) -> f64 {
    let r = x.round();
    if (x - x.trunc()).abs() == 0.5 && r % 2.0 != 0.0 { r - x.signum() } else { r }
}

/// Bignum payload: `[negative?, limb count, limbs…]`, little-endian.
fn write_bignum(heap: &mut Heap, b: &BigInt) -> Value {
    let (sign, mag) = b.to_u64_digits();
    let o = heap.alloc(ObjType::Bignum, 2 + mag.len(), Value::fixnum(0));
    let neg = matches!(sign, Sign::Minus);
    heap.obj_set(o, 0, Value::fixnum(neg as i64));
    heap.obj_set(o, 1, Value::fixnum(mag.len() as i64));
    for (i, limb) in mag.iter().enumerate() {
        // Limbs are raw bits, not values: `Bignum` is one of the four object
        // types the collector does not trace into, precisely for this.
        heap.obj_set(o, 2 + i, Value(*limb));
    }
    o
}

fn read_bignum(heap: &Heap, v: Value) -> BigInt {
    let neg = heap.obj_ref(v, 0).as_fixnum() != 0;
    let n = heap.obj_ref(v, 1).as_fixnum() as usize;
    let limbs: Vec<u64> = (0..n).map(|i| heap.obj_ref(v, 2 + i).raw()).collect();
    BigInt::from_slice(
        if neg { Sign::Minus } else { Sign::Plus },
        &limbs
            .iter()
            .flat_map(|l| [(*l & 0xffff_ffff) as u32, (*l >> 32) as u32])
            .collect::<Vec<u32>>(),
    )
}

/// `round` on a `BigRational`, ties to even. `num-rational`'s own `round` ties
/// away from zero, which is not what R7RS specifies.
trait RoundTiesEven {
    fn round_ties_even_impl(&self) -> BigRational;
}

impl RoundTiesEven for BigRational {
    fn round_ties_even_impl(&self) -> BigRational {
        let floor = self.floor();
        let diff = self - &floor;
        let half = BigRational::new(BigInt::from(1), BigInt::from(2));
        match diff.cmp(&half) {
            std::cmp::Ordering::Less => floor,
            std::cmp::Ordering::Greater => floor + BigRational::from(BigInt::from(1)),
            std::cmp::Ordering::Equal => {
                if floor.numer().is_even() {
                    floor
                } else {
                    floor + BigRational::from(BigInt::from(1))
                }
            }
        }
    }
}
