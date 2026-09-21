//! The ACUI effect solver — `constraints.scm`.
//!
//! Effects form a set: their union is associative, commutative and idempotent
//! with a unit (`pure`). Unifying under those laws — ACUI unification — is
//! NP-hard in general, so FX-91 does not unify effects at all. It collects
//! *constraints* between effect expressions and asks only whether the set is
//! satisfiable, which Jouvelot and Gifford (POPL '91) reduce to propositional
//! Horn-clause satisfiability, solved by Dowling and Gallier's linear-time
//! algorithm.
//!
//! The encoding: for each effect constant `c` and each unification variable
//! `v`, a three-valued bit saying whether `c` is known *absent* from `v`.
//! A constraint whose two sides disagree about a constant, where one side is
//! fully determined, forces the bit on the other; iterate to a fixed point, and
//! report failure the moment a constant is required to be both present and
//! absent.
//!
//! Most constraints never reach the solver. [`Checker::obvious_constraint`]
//! discharges the easy shapes — either side `pure`, either side a bare
//! unification variable — directly, which is what keeps the iteration small.

use crate::ast::{Constraint, Fx, FxId, Tri};
use crate::check::Checker;
use crate::error::{FxError, R};
use crate::free::free_dvars_of_dexp;

impl Checker<'_> {
    /// `add-constraint!`
    pub fn add_constraint(&mut self, lhs: FxId, rhs: FxId) -> R<bool> {
        let c = Constraint { lhs, rhs };
        if self.obvious_constraint(c)? {
            return Ok(true);
        }
        self.constraints.push(c);
        self.verify_constraints()
    }

    /// `union-constraints!`
    pub fn union_constraints(&mut self, cs: &[Constraint]) -> R<bool> {
        let mut updated = false;
        for c in cs {
            if !self.obvious_constraint(*c)? {
                self.constraints.push(*c);
                updated = true;
            }
        }
        if updated { self.verify_constraints() } else { Ok(true) }
    }

    /// The constraints added since the set had length `mark`, oldest first.
    pub fn diff_constraints(&self, mark: usize) -> Vec<Constraint> {
        self.constraints[mark.min(self.constraints.len())..].to_vec()
    }

    pub fn constraint_mark(&self) -> usize {
        self.constraints.len()
    }

    /// Discharge a constraint directly when its shape allows.
    ///
    /// `(maxeff x …) = (maxeff …)` in general cannot be, and goes to the
    /// solver; everything else is settled here, as early as possible.
    fn obvious_constraint(&mut self, c: Constraint) -> R<bool> {
        let lhs = self.p.arena.find(c.lhs);
        let rhs = self.p.arena.find(c.rhs);
        if lhs == rhs {
            return Ok(true);
        }
        let lpure = self.p.arena.is_pure(lhs);
        let rpure = self.p.arena.is_pure(rhs);
        if lpure && rpure {
            return Ok(true);
        }
        if lpure || rpure {
            // One side is empty, so every member of the other must be too.
            let other = if lpure { rhs } else { lhs };
            let span = self.p.arena.span(other);
            let empty = self.pure(span);
            for member in self.p.arena.effect_list(other) {
                if !self.unify_1(crate::unify::Mode::Unify, empty, member)? {
                    return Err(FxError::user(span, "effect constraint is not satisfiable"));
                }
            }
            return Ok(true);
        }
        let l_unif = self.p.arena.var(lhs).is_some_and(|v| v.is_unification());
        if l_unif {
            return self.obvious_var(lhs, rhs);
        }
        let r_unif = self.p.arena.var(rhs).is_some_and(|v| v.is_unification());
        if r_unif {
            return self.obvious_var(rhs, lhs);
        }
        // Two compound effects over the same variables cannot constrain each
        // other further; otherwise they must go to the solver.
        let fl = free_dvars_of_dexp(self.p.arena, lhs);
        let fr = free_dvars_of_dexp(self.p.arena, rhs);
        let l_covers = fr.iter().all(|y| fl.iter().any(|x| self.p.arena.same_variable(*x, *y)));
        let r_covers = fl.iter().all(|x| fr.iter().any(|y| self.p.arena.same_variable(*x, *y)));
        Ok(l_covers && r_covers)
    }

    /// Bind a unification variable standing alone on one side.
    ///
    /// When it occurs on the other side too, it cannot simply be bound —
    /// `e = (maxeff e read)` — so it is bound to a *fresh* variable unioned
    /// with the rest, which records "at least those, possibly more".
    fn obvious_var(&mut self, var: FxId, other: FxId) -> R<bool> {
        let span = self.p.arena.span(var);
        let frees = free_dvars_of_dexp(self.p.arena, other);
        let occurs = frees.iter().any(|f| self.p.arena.same_variable(var, *f));
        if !occurs {
            return Ok(self.p.arena.forward(var, other));
        }
        let fresh = {
                        self.fresh_unification(span, false, crate::ast::Kind::Effect)
        };
        let mut members = vec![fresh];
        for f in frees {
            if !self.p.arena.same_variable(var, f) {
                members.push(f);
            }
        }
        let union = self.p.arena.add(span, Fx::MaxEff(members));
        Ok(self.p.arena.forward(var, union))
    }

    /// `evaluate-constraints`
    pub fn evaluate_constraints(&mut self, cs: &[Constraint]) -> R<Vec<Constraint>> {
        let mut out = Vec::with_capacity(cs.len());
        for c in cs {
            let lhs = self.evaluate(c.lhs)?;
            let rhs = self.evaluate(c.rhs)?;
            out.push(Constraint { lhs, rhs });
        }
        Ok(out)
    }

    fn verify_constraints(&mut self) -> R<bool> {
        let cs = self.constraints.clone();
        if self.satisfiable(&cs)? {
            return Ok(true);
        }
        let span = cs
            .first()
            .map(|c| self.p.arena.span(c.lhs))
            .unwrap_or(fixpt_read::Span::new(fixpt_read::FileId(0), 0, 0));
        Err(FxError::user(span, "effect constraint is not satisfiable"))
    }

    /// Dowling–Gallier: iterate the valuations to a fixed point, failing as
    /// soon as a constant is forced both ways.
    fn satisfiable(&mut self, cs: &[Constraint]) -> R<bool> {
        // Compare only the *free variables* of each side: under ACUI an effect
        // is exactly the set of constants and variables it mentions.
        let mut normalized: Vec<(Vec<FxId>, Vec<FxId>)> = Vec::with_capacity(cs.len());
        for c in cs {
            let l = free_dvars_of_dexp(self.p.arena, c.lhs);
            let r = free_dvars_of_dexp(self.p.arena, c.rhs);
            normalized.push((l, r));
        }
        let mut frees: Vec<FxId> = Vec::new();
        for (l, r) in &normalized {
            for v in l.iter().chain(r) {
                if !frees.iter().any(|x| self.p.arena.same_variable(*x, *v)) {
                    frees.push(*v);
                }
            }
        }
        let (variables, constants): (Vec<FxId>, Vec<FxId>) = frees
            .into_iter()
            .partition(|v| self.p.arena.var(*v).is_some_and(|d| d.is_unification()));
        let constant_names: Vec<u32> = constants
            .iter()
            .filter_map(|c| self.p.arena.var(*c).map(|v| v.name))
            .collect();
        for v in &variables {
            let valuation: Vec<(u32, Tri)> =
                constant_names.iter().map(|n| (*n, Tri::Unknown)).collect();
            if let Some(data) = self.p.arena.var_mut(*v) {
                data.valuation = valuation;
            }
        }

        loop {
            let mut changed = false;
            for (l, r) in &normalized {
                for c in &constants {
                    match self.check_constraint(l, r, *c)? {
                        Some(true) => changed = true,
                        Some(false) => {}
                        // Inconsistent.
                        None => return Ok(false),
                    }
                }
            }
            if !changed {
                return Ok(true);
            }
        }
    }

    /// `Some(changed)` on progress or no-op, `None` when inconsistent.
    fn check_constraint(
        &mut self,
        lhs: &[FxId],
        rhs: &[FxId],
        constant: FxId,
    ) -> R<Option<bool>> {
        let not_in_lhs = self.constant_absent(lhs, constant);
        let not_in_rhs = self.constant_absent(rhs, constant);
        match (not_in_lhs, not_in_rhs) {
            (Tri::Unknown, Tri::Unknown) => Ok(Some(false)),
            // One side is determined: if the constant is absent there, it must
            // be absent from the other too.
            (Tri::Unknown, known) | (known, Tri::Unknown) => {
                if known == Tri::True {
                    let side = if not_in_lhs == Tri::Unknown { lhs } else { rhs };
                    match self.force_absent(side, constant) {
                        Some(updated) => Ok(Some(updated)),
                        None => Ok(None),
                    }
                } else {
                    Ok(Some(false))
                }
            }
            (a, b) if a == b => Ok(Some(false)),
            _ => Ok(None),
        }
    }

    /// Whether `constant` is known absent from this effect's members.
    fn constant_absent(&self, members: &[FxId], constant: FxId) -> Tri {
        let Some(cname) = self.p.arena.var(constant).map(|v| v.name) else {
            return Tri::Unknown;
        };
        for m in members {
            let Some(v) = self.p.arena.var(*m) else { return Tri::False };
            if v.is_unification() {
                match v.valuation.iter().find(|(n, _)| *n == cname).map(|(_, t)| *t) {
                    Some(Tri::True) => continue,
                    Some(Tri::False) => return Tri::False,
                    _ => return Tri::Unknown,
                }
            }
            if v.name == cname {
                return Tri::False;
            }
        }
        Tri::True
    }

    /// Record that `constant` is absent from every member. `None` if that is
    /// impossible because the constant is literally one of them.
    fn force_absent(&mut self, members: &[FxId], constant: FxId) -> Option<bool> {
        let cname = self.p.arena.var(constant).map(|v| v.name)?;
        let mut updated = false;
        for m in members {
            let is_unif = self.p.arena.var(*m).is_some_and(|v| v.is_unification());
            if is_unif {
                let data = self.p.arena.var_mut(*m)?;
                if let Some(slot) = data.valuation.iter_mut().find(|(n, _)| *n == cname) {
                    if slot.1 == Tri::Unknown {
                        slot.1 = Tri::True;
                        updated = true;
                    }
                } else {
                    data.valuation.push((cname, Tri::True));
                    updated = true;
                }
                continue;
            }
            if self.p.arena.var(*m).is_some_and(|v| v.name == cname) {
                return None;
            }
        }
        Some(updated)
    }
}
