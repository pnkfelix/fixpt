//! Printing descriptions, in FX-87's notation.

use crate::ast::{Atom, Effect, Kind, Region, Ty, TyId};
use crate::check::Checker;
use std::collections::HashSet;

impl Checker {
    pub fn show_region(&self, r: Region) -> String {
        match r {
            Region::Const(s) => self.interner.name(s).to_string(),
            Region::Var(v) => self.interner.name(self.arena.dvar_name(v)).to_string(),
        }
    }

    pub fn show_atom(&self, a: Atom) -> String {
        let (op, r) = match a {
            Atom::Read(r) => ("read", r),
            Atom::Write(r) => ("write", r),
            Atom::Alloc(r) => ("alloc", r),
            Atom::Goto(r) => ("goto", r),
            Atom::Comefrom(r) => ("comefrom", r),
            Atom::Var(v) => return self.interner.name(self.arena.dvar_name(v)).to_string(),
        };
        format!("({op} {})", self.show_region(r))
    }

    /// `pure`, a single atom, or `(maxeff …)`.
    pub fn show_effect(&self, e: &Effect) -> String {
        let atoms: Vec<String> = e.0.iter().map(|a| self.show_atom(*a)).collect();
        match atoms.len() {
            0 => "pure".into(),
            1 => atoms[0].clone(),
            _ => format!("(maxeff {})", atoms.join(" ")),
        }
    }

    /// A type. A recursive type prints as far as its first repetition, which
    /// is shown as `…` — enough to read, and it always terminates.
    pub fn show_ty(&self, t: TyId) -> String {
        self.show_ty_on(t, &mut HashSet::new())
    }

    fn show_ty_on(&self, t: TyId, path: &mut HashSet<TyId>) -> String {
        let t = self.arena.resolve(t);
        if !path.insert(t) {
            return "…".into();
        }
        let out = match self.arena.get(t).clone() {
            Ty::Base(s) => self.interner.name(s).to_string(),
            Ty::Void => "void".into(),
            Ty::Var(v) => self.interner.name(self.arena.dvar_name(v)).to_string(),
            Ty::Link(None) => "?".into(),
            Ty::Link(Some(_)) => unreachable!("resolved"),
            Ty::Subr { effect, params, result } => {
                let ps: Vec<String> = params.iter().map(|p| self.show_ty_on(*p, path)).collect();
                format!("(subr {} ({}) {})", self.show_effect(&effect), ps.join(" "), self.show_ty_on(result, path))
            }
            Ty::Poly { binders, body } => {
                let bs: Vec<String> = binders
                    .iter()
                    .map(|(v, k)| {
                        let k = match k {
                            Kind::Region => "region",
                            Kind::Effect => "effect",
                            Kind::Type => "type",
                        };
                        format!("({} {k})", self.interner.name(self.arena.dvar_name(*v)))
                    })
                    .collect();
                format!("(poly ({}) {})", bs.join(" "), self.show_ty_on(body, path))
            }
            Ty::Ref(a, r) => format!("(ref {} {})", self.show_ty_on(a, path), self.show_region(r)),
            Ty::Pair(a, b, r) => format!(
                "(pairof {} {} {})",
                self.show_ty_on(a, path),
                self.show_ty_on(b, path),
                self.show_region(r)
            ),
        };
        path.remove(&t);
        out
    }
}
