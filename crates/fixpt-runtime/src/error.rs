//! Raised conditions.
//!
//! A raise carries exactly one thing across the unwind: the condition
//! [`Value`]. That is deliberate — anything else (a `Vec<Value>` of irritants,
//! say) would be a set of heap references living in a Rust error type, outside
//! the collector's root set, and would go stale the moment a handler allocated.
//! Packaging the whole condition into one object before unwinding keeps the
//! engine's rooting story to a single register.

use fixpt_heap::Value;

#[derive(Copy, Clone, Debug)]
pub struct Thrown {
    /// The condition object.
    pub obj: Value,
    /// When false, the engine hands the condition to the prelude's `raise`, so
    /// that user handlers installed with `with-exception-handler` see it.
    /// When true, it unwinds all the way out instead — which is how
    /// `%raise-uncaught` terminates the search without re-entering it.
    pub fatal: bool,
    /// Not a condition at all: `%host` has paused the machine to ask its
    /// native caller something, and `obj` is the question. The machine is
    /// left exactly as it was, and the caller answers by *resuming* it
    /// (`Interp::answer_host`, `Vm::answer_host`). Always also `fatal`, so no Scheme
    /// handler intercepts it.
    pub suspended: bool,
}

impl Thrown {
    /// A condition a Scheme handler should get a chance at.
    pub fn raise(obj: Value) -> Thrown {
        Thrown { obj, fatal: false, suspended: false }
    }
    /// A condition that has already been through the handler chain.
    pub fn fatal(obj: Value) -> Thrown {
        Thrown { obj, fatal: true, suspended: false }
    }
    /// The machine paused to ask its caller `request`.
    pub fn suspend(request: Value) -> Thrown {
        Thrown { obj: request, fatal: true, suspended: true }
    }
}

pub type Outcome<T> = Result<T, Thrown>;
