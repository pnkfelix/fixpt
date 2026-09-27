//! Printing descriptions, in FX-87's notation.

use crate::ast::{Atom, Effect, Kind, Region, Ty, TyId};
use crate::check::Checker;
use std::collections::HashSet;

impl Checker {
    pub fn show_region(&self, r: Region) -> String {
        match r {
            Region::Const(s) => self.interner.name(s).to_string(),
            Region::Var(v) => self.interner.name(self.arena.dvar_name(v)).to_string(),
            Region::Frozen => "const".to_string(),
        }
    }

    pub fn show_atom(&self, a: Atom) -> String {
        let (op, r) = match a {
            Atom::Read(r) => ("read", r),
            Atom::Write(r) => ("write", r),
            Atom::Alloc(r) => ("alloc", r),
            Atom::Goto(r) => ("goto", r),
            Atom::Comefrom(r) => ("comefrom", r),
            Atom::Await(r) => ("await", r),
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

    /// A type. A type that `define-type` named prints as its name. Any other
    /// recursive type prints as far as its first repetition, which is shown
    /// as `…` — enough to read, and it always terminates.
    pub fn show_ty(&self, t: TyId) -> String {
        self.show_ty_on(t, &mut HashSet::new())
    }

    /// A type written out one level, even if it has a name: what a
    /// `define-type` defined the name as.
    pub fn show_definition(&self, t: TyId) -> String {
        self.show_ty_body(self.arena.resolve(t), &mut HashSet::new())
    }

    fn abbreviation(&self, t: TyId) -> Option<&str> {
        self.type_names()
            .into_iter()
            .rev()
            .find(|n| self.type_named(*n).is_some_and(|d| self.arena.resolve(d) == t))
            .map(|n| self.interner.name(n))
    }

    fn show_ty_on(&self, t: TyId, path: &mut HashSet<TyId>) -> String {
        let t = self.arena.resolve(t);
        if let Some(name) = self.abbreviation(t) {
            return name.to_string();
        }
        self.show_ty_body(t, path)
    }

    fn show_ty_body(&self, t: TyId, path: &mut HashSet<TyId>) -> String {
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
                            Kind::Place => "place",
                            Kind::Effect => "effect",
                            Kind::Type => "type",
                        };
                        match self.arena.bound(*v) {
                            Some(b) => format!("({} {k} {})", self.interner.name(self.arena.dvar_name(*v)), self.show_region(b)),
                            None => format!("({} {k})", self.interner.name(self.arena.dvar_name(*v))),
                        }
                    })
                    .collect();
                format!("(poly ({}) {})", bs.join(" "), self.show_ty_on(body, path))
            }
            Ty::Ref(a, r) => format!("(ref {} {})", self.show_ty_on(a, path), self.show_region(r)),
            Ty::Product(parts) | Ty::Sum(parts) => {
                let head = if matches!(self.arena.get(t), Ty::Product(_)) { "productof" } else { "sumof" };
                let ps: Vec<String> =
                    parts.iter().map(|(l, x)| format!(" ({} {})", self.interner.name(*l), self.show_ty_on(*x, path))).collect();
                format!("({head}{})", ps.concat())
            }
            Ty::Array(a, r) => format!("(arrayof {} {})", self.show_ty_on(a, path), self.show_region(r)),
            Ty::ICell(a, r) => format!("(icell {} {})", self.show_ty_on(a, path), self.show_region(r)),
            Ty::Place(r) => format!("(place {})", self.show_region(r)),
            // FX-87's `listof`: a pair whose tail is itself.
            Ty::Pair(a, b, r) if self.arena.resolve(b) == t => {
                format!("(listof {} {})", self.show_ty_on(a, path), self.show_region(r))
            }
            Ty::PromptTag { answer, payload, effect, region } => format!(
                "(prompt-tag {} {} {} {})",
                self.show_ty_on(answer, path),
                self.show_ty_on(payload, path),
                self.show_effect(&effect),
                self.show_region(region)
            ),
            Ty::Composable { arg, answer, effect, region } => format!(
                "(composable {} {} {} {})",
                self.show_ty_on(arg, path),
                self.show_ty_on(answer, path),
                self.show_effect(&effect),
                self.show_region(region)
            ),
            Ty::MarkKey(x, r) => format!("(mark-key {} {})", self.show_ty_on(x, path), self.show_region(r)),
            Ty::Bloblet { fields, frozen, region } => {
                let fs: Vec<String> = fields.iter().map(|f| self.show_ty_on(*f, path)).collect();
                let head = if frozen { "frozen" } else { "fields" };
                let sep = if fs.is_empty() { "" } else { " " };
                format!("(bloblet ({head}{sep}{}) {})", fs.join(" "), self.show_region(region))
            }
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
