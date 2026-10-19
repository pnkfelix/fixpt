//! `fixpt-runtime` — the numeric tower, equality, printing, primitives, and the
//! session state they share.
//!
//! Everything here is engine-independent: the AST interpreter and the bytecode
//! VM use the same primitives, the same `equal?`, the same printer, so a
//! difference between them cannot come from this layer.

pub mod cmarks;

/// fixpt's native convention on the machine this is, declared (`TODO.md`
/// §97, `docs/research/declared-conventions.md`): its clauses, one to a
/// line, canonical, as `fixpt_native::direct::native_convention_of` makes
/// them (a test there says so). Both checkers compare a program's
/// `define-convention` with it, and `native-convention` gives it to a
/// program: x86_64's on x86_64, arm64's everywhere else.
#[cfg(target_arch = "x86_64")]
pub const NATIVE_CONVENTION: &str = NATIVE_CONVENTION_X86_64;
#[cfg(not(target_arch = "x86_64"))]
pub const NATIVE_CONVENTION: &str = NATIVE_CONVENTION_ARM64;
/// Each machine's, whichever this is.
pub const NATIVE_CONVENTION_ARM64: &str = include_str!("native-arm64.conv");
pub const NATIVE_CONVENTION_X86_64: &str = include_str!("native-x86_64.conv");

pub mod crossing;
pub mod disasm;
pub mod eqtable;
pub mod equal;
pub mod literal;
pub mod error;
pub mod num;
pub mod port;
pub mod prim;
pub mod print;
pub mod runtime;
pub mod sched;
pub mod tty;
pub mod world;

pub use error::{Outcome, Thrown};
pub use num::N;
pub use prim::{integer_value, low_64_bits, never_collects, EngineOp, PrimDef, PrimKind, PRIMITIVES};
pub use print::{display_value, write_value};
pub use runtime::{CallNative, MachineCode, NativeExit, PlaceCode, RunWord, Runtime, Sink};

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
