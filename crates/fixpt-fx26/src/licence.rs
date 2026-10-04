//! Effects as licences: what a speculation driver may let run.
//!
//! A licence is effect masking, relative to an observer. Masking asks what
//! anything outside *an expression* can observe, and answers from types:
//! whatever the free variables and the result can reach. A licence asks what
//! the *user's program* can observe of code a driver runs early, repeatedly,
//! or not at all. The answer has the same shape. Effects on regions the
//! program cannot name are invisible to it.
//!
//! So an effect is licensed when, masked for that observer, nothing is left
//! but allocation. Every atom must be
//!
//! * an allocation, anywhere — a new object is invisible until something
//!   that can see it is handed it, and that would be a read or a write; or
//! * a read, a write or a control effect on a region the observer cannot
//!   name.
//!
//! An effect variable is never licensed: it could be anything.
//!
//! Which regions the observer cannot name is not asserted by the driver. It
//! is established by construction, in either of two ways:
//!
//! * **Fresh regions.** Inference instantiates a region nothing constrains
//!   with a fresh, uninterned one, and masking then removes effects on it.
//!   The REPL's speculation relies on this: it owns no region, and runs an
//!   expression early only if masking left nothing but allocation.
//! * **Private regions.** A program that says `(private-regions @s …)` is
//!   instantiated at regions of its own: each `@s` in it is a fresh region,
//!   uninterned, which no other program can write. The eager reader does
//!   this, so a driver can check its entry points against exactly those
//!   regions (`Checker::private_licence`). Its effects stay visible in its
//!   types, as they must, because the driver holds its states. But nothing
//!   the user writes can reach them.
//!
//! Two things a licence needs that masking does not: running early may not
//! terminate, and may fail, and neither is an effect. So a speculative run
//! has a step budget of its own, and a failure is shown, not raised.

use crate::ast::{Atom, Effect, Region};
use crate::check::Checker;

/// The first atom of `effect` that the licence does not cover, or `None`
/// when all of it is licensed.
pub fn unlicensed(effect: &Effect, owned: &[Region]) -> Option<Atom> {
    effect.0.iter().copied().find(|a| match *a {
        Atom::Alloc(_) => false,
        // Reading globals, which it defined itself, is seen by no one else.
        Atom::Read(r) if r.is_globals() => false,
        Atom::Read(r) | Atom::Write(r) | Atom::Goto(r) | Atom::Comefrom(r) | Atom::Await(r) => !owned.contains(&r),
        Atom::Var(_) | Atom::App(_) => true,
        // A speculative run has a step budget of its own.
        Atom::Spin => false,
    })
}

/// The eager reader's entry points: what a driver calls.
pub const READER_ENTRY_POINTS: &[&str] = &[
    "eager-start",
    "eager-start-fx26",
    "eager-feed",
    "eager-feed-string",
    "eager-status",
    "eager-state-kind",
    "eager-state-position",
    "eager-state-message",
    "eager-state-data",
    "eager-context",
    "eager-hole-closers",
    "eager-state-syntax",
    "parse-program",
];

impl Checker {
    /// The region constant written `name`.
    pub fn region_named(&mut self, name: &str) -> Region {
        Region::Const(self.interner.intern(name))
    }

    /// Whether calling `name` is licensed for a driver that owns `owned`: the
    /// latent effect of its type must be. An error says why not.
    pub fn licensed_call(&mut self, name: &str, owned: &[Region]) -> Result<(), String> {
        let sym = self.interner.intern(name);
        let Some(t) = self.type_of_name(sym) else {
            return Err(format!("`{name}` is not defined"));
        };
        let Some((effect, _, _)) = self.arena.get(t).as_subr() else {
            return Err(format!("`{name}` is a {}, not a subroutine", self.show_ty(t)));
        };
        match unlicensed(&effect, owned) {
            None => Ok(()),
            Some(a) => Err(format!(
                "`{name}` may {}, which is not the program's own to touch",
                self.show_atom(a)
            )),
        }
    }

    /// Check that every one of `entry_points` is licensed when the only
    /// regions it may touch are the program's own private ones: that is,
    /// that the program's effects are invisible to any other program.
    pub fn private_licence(&mut self, entry_points: &[&str]) -> Result<(), String> {
        let owned = self.private_regions.clone();
        for name in entry_points {
            self.licensed_call(name, &owned)?;
        }
        Ok(())
    }

    /// The eager reader's licence: `private_licence` of its entry points.
    pub fn reader_licence(&mut self) -> Result<(), String> {
        self.private_licence(READER_ENTRY_POINTS)
    }
}
