//! `fixpt-runtime` — the numeric tower, equality, printing, primitives, and the
//! session state they share.
//!
//! Everything here is engine-independent: the AST interpreter and the bytecode
//! VM use the same primitives, the same `equal?`, the same printer, so a
//! difference between them cannot come from this layer.

pub mod equal;
pub mod error;
pub mod num;
pub mod port;
pub mod prim;
pub mod print;
pub mod runtime;

pub use error::{Outcome, Thrown};
pub use num::N;
pub use prim::{EngineOp, PrimDef, PrimKind, PRIMITIVES};
pub use print::{display_value, write_value};
pub use runtime::{Runtime, Sink};

use fixpt_heap::Value;

/// Convert a reader literal into a heap number.
pub fn num_from_literal(rt: &mut Runtime, n: &fixpt_read::Num) -> Value {
    lift(n).store(&mut rt.heap)
}

fn lift(n: &fixpt_read::Num) -> N {
    use fixpt_read::Num as L;
    match n {
        L::Int(i) => N::Fix(*i),
        L::Real(x) => N::Flo(*x),
        L::Big { negative, digits, radix } => {
            let b = num_bigint::BigInt::parse_bytes(digits.as_bytes(), *radix)
                .unwrap_or_else(|| num_bigint::BigInt::from(0));
            N::big(if *negative { -b } else { b })
        }
        L::Ratio(a, b) => {
            let (na, nb) = (lift(a), lift(b));
            match na.div(&nb) {
                Ok(v) => v,
                // `n/0` in source: leave it as the numerator rather than
                // failing in the reader, and let arithmetic report it.
                Err(_) => na,
            }
        }
    }
}
