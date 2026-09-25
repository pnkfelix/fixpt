//! Effects as licences: what a speculation driver may let run.
//!
//! "Pure" is the wrong test for running something before it is asked for.
//! The eager reader hands its checkpoint continuation back to its caller, so
//! its control effects are never masked, and every character it reads
//! allocates. It is safe to run on each keystroke all the same, because
//! everything it does is to regions its driver owns. So the licence is
//! relative to the regions the driver owns (`docs/fx26.md`, "What licence to
//! speculate means"). An effect is licensed when every atom of it is
//!
//! * an allocation, anywhere — a new object is invisible until something
//!   that can see it is handed it, and that would be a read or a write;
//! * a read, a write or a control effect on a region the driver owns.
//!
//! An effect variable is never licensed: it could be anything.

use crate::ast::{Atom, Effect, Region};
use crate::check::Checker;

/// The first atom of `effect` that the licence does not cover, or `None`
/// when all of it is licensed.
pub fn unlicensed(effect: &Effect, owned: &[Region]) -> Option<Atom> {
    effect.0.iter().copied().find(|a| match *a {
        Atom::Alloc(_) => false,
        Atom::Read(r) | Atom::Write(r) | Atom::Goto(r) | Atom::Comefrom(r) => !owned.contains(&r),
        Atom::Var(_) => true,
    })
}

/// The eager reader's entry points: what a driver calls.
pub const READER_ENTRY_POINTS: &[&str] = &[
    "eager-start",
    "eager-feed",
    "eager-status",
    "eager-state-kind",
    "eager-state-position",
    "eager-state-message",
    "eager-state-data",
    "eager-context",
    "eager-hole-closers",
];

/// The regions the eager reader's driver owns: the reader's data, its
/// prompt tag, its mark key, and the lists it hands back.
pub const READER_REGIONS: &[&str] = &["@s", "@e", "@m", "@c"];

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
                "`{name}` may {}, on a region the driver does not own",
                self.show_atom(a)
            )),
        }
    }

    /// Check that every entry point of the eager reader, once loaded into
    /// this checker, is licensed for a driver that owns the reader's regions.
    pub fn reader_licence(&mut self) -> Result<(), String> {
        let owned: Vec<Region> = READER_REGIONS.iter().map(|r| self.region_named(r)).collect();
        for name in READER_ENTRY_POINTS {
            self.licensed_call(name, &owned)?;
        }
        Ok(())
    }
}
