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
//! * **Regions given.** Code that is a `plambda` over regions, which whoever
//!   makes it gives, can name no other: in its type, each entry point's
//!   effect is on those binders, whichever regions they become, and on no
//!   region of its own choosing (`Checker::parametric_licence`). The eager
//!   reader and the parser are such code: module files of the reader's
//!   regions (`(module-parameters …)`), made by the front end at the regions
//!   it names (`reader.fx`). Their effects stay visible in their types, as
//!   they must, because the driver holds their states; but they can touch
//!   only what they made or were handed, so nothing the user writes is
//!   touched, and the user is handed nothing of theirs.
//!
//! Two things a licence needs that masking does not: running early may not
//! terminate, and may fail, and neither is an effect. So a speculative run
//! has a step budget of its own, and a failure is shown, not raised.

use crate::ast::{Atom, Effect, Kind, Region, Ty, TyId};
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

/// The global the front end makes the reader from (`reader.fx`): the last
/// of its module files, loaded, a `plambda` over the reader's regions.
pub const READER_MAKER: &str = "make-reader";

/// The regions the front end makes the reader at (`reader.fx`), which its
/// entry points, as the driver calls them, may touch.
pub const READER_REGIONS: &[&str] = &["@s", "@e", "@m", "@c", "@p"];

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

    /// Check that `maker`, a `(poly ((r region) …) (subr F () (moduleof
    /// …)))`, makes each of `entry_points`, wherever it is in the module it
    /// makes (in a module of it too), at a type whose latent effect is
    /// licensed when the regions it may touch are the binders; and that
    /// making it is. Whichever regions it is given, it touches those only.
    pub fn parametric_licence(&mut self, maker: &str, entry_points: &[&str]) -> Result<(), String> {
        let sym = self.interner.intern(maker);
        let Some(t) = self.type_of_name(sym) else {
            return Err(format!("`{maker}` is not defined"));
        };
        let not = |c: &Checker| format!("`{maker}` is a {}, not a `plambda` over regions making a module", c.show_ty(t));
        let Ty::Poly { binders, body } = self.arena.get(self.arena.resolve(t)).clone() else { return Err(not(self)) };
        let owned: Vec<Region> = binders.iter().filter(|(_, k)| matches!(k, Kind::Region)).map(|(v, _)| Region::Var(*v)).collect();
        let Some((effect, params, made)) = self.arena.get(self.arena.resolve(body)).as_subr() else { return Err(not(self)) };
        if !params.is_empty() {
            return Err(not(self));
        }
        if let Some(a) = unlicensed(&effect, &owned) {
            return Err(format!("making `{maker}` may {}, which is not among the regions it is given", self.show_atom(a)));
        }
        for name in entry_points {
            let mut found = Vec::new();
            let n = self.interner.intern(name);
            self.vals_named(made, n, &mut found);
            if found.is_empty() {
                return Err(format!("`{maker}` makes no `{name}`"));
            }
            for v in found {
                let Some((effect, _, _)) = self.arena.get(self.arena.resolve(v)).as_subr() else {
                    return Err(format!("`{name}`, as `{maker}` makes it, is a {}, not a subroutine", self.show_ty(v)));
                };
                if let Some(a) = unlicensed(&effect, &owned) {
                    return Err(format!(
                        "`{name}`, as `{maker}` makes it, may {}, which is not among the regions it is given",
                        self.show_atom(a)
                    ));
                }
            }
        }
        Ok(())
    }

    /// The types of the values named `name` in module type `t` and in the
    /// modules among its values, onto `out`.
    fn vals_named(&self, t: TyId, name: fixpt_read::Sym, out: &mut Vec<TyId>) {
        if let Ty::Module { vals, .. } = self.arena.get(self.arena.resolve(t)) {
            for (n, v) in vals {
                if *n == name {
                    out.push(*v);
                }
                self.vals_named(*v, name, out);
            }
        }
    }

    /// The eager reader's licence: what makes it, [`READER_MAKER`], makes
    /// its entry points touching only the regions it is given
    /// (`parametric_licence`); and as the driver calls them, made at
    /// [`READER_REGIONS`], they touch only those.
    pub fn reader_licence(&mut self) -> Result<(), String> {
        self.parametric_licence(READER_MAKER, READER_ENTRY_POINTS)?;
        let owned: Vec<Region> = READER_REGIONS.iter().map(|r| self.region_named(r)).collect();
        for name in READER_ENTRY_POINTS {
            self.licensed_call(name, &owned)?;
        }
        Ok(())
    }
}
