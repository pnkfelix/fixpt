//! Effect masking — `erase-effect`.
//!
//! The idea that gives FX-87 its point. A computation that allocates a cell,
//! writes it, reads it and throws it away has *no observable effect*, and the
//! type system should say so rather than reporting a write that nobody can see.
//!
//! ```text
//! (let ((x 3 @!)) (set! x 4))   ⇒  unit ! pure
//! ```
//!
//! The rule: a region may be dropped from an effect when it cannot be reached
//! from outside the expression — neither through a free variable's type nor
//! through the expression's own result type. Two refinements from
//! `erase-effect-1` that are easy to miss:
//!
//! * A region reachable through a **free variable** stays. `(lambda ((v (vectorof
//!   int @!))) (vector-set! v 0 1))` keeps its `(write @!)`, because the caller
//!   handed in the vector and can see the change.
//! * A region that survives into the **result type** keeps its `(alloc r)`
//!   specifically — the cell escapes, so its allocation is observable — while
//!   reads and writes of it are still dropped.

use crate::ast::{Arena, Desc, DescId};
use crate::subtype::Rel;
use std::collections::HashSet;

/// Remove from `effect` every region that cannot escape.
///
/// `visible` are the regions reachable through the free variables of the
/// expression; `result` is its type.
pub fn erase_effect(
    arena: &mut Arena,
    rel_immutable: fixpt_read::Sym,
    rel_ref: fixpt_read::Sym,
    effect: DescId,
    result: DescId,
    visible: &[DescId],
) -> DescId {
    let mut in_effect = Vec::new();
    regions_of(arena, effect, &mut HashSet::new(), &mut in_effect);
    if in_effect.is_empty() {
        return effect;
    }
    let mut in_type = Vec::new();
    regions_of(arena, result, &mut HashSet::new(), &mut in_type);

    let mut current = effect;
    for r in in_effect {
        let escapes = {
            let rel = Rel::new(arena, rel_immutable, rel_ref);
            visible.iter().any(|v| rel.region_equal(r, *v, &Default::default(), &Default::default()))
        };
        if escapes {
            continue;
        }
        let in_result = {
            let rel = Rel::new(arena, rel_immutable, rel_ref);
            in_type.iter().any(|t| rel.region_equal(r, *t, &Default::default(), &Default::default()))
        };
        let had_alloc = {
            let rel = Rel::new(arena, rel_immutable, rel_ref);
            let alloc = arena.get(current).clone();
            let _ = alloc;
            has_alloc_of(arena, current, r, &rel)
        };
        let stripped = delete_region(arena, current, r, rel_immutable, rel_ref);
        current = if in_result && had_alloc {
            // The cell escapes in the result, so its allocation stays visible
            // even though reads and writes of it do not.
            let a = arena.desc(Desc::Alloc(r));
            arena.maxeff(vec![a, stripped])
        } else {
            stripped
        };
    }
    current
}

/// Every region mentioned anywhere in `id`.
fn regions_of(arena: &Arena, id: DescId, seen: &mut HashSet<DescId>, out: &mut Vec<DescId>) {
    if !seen.insert(id) {
        return;
    }
    match arena.get(id) {
        Desc::Read(r) | Desc::Write(r) | Desc::Alloc(r) => {
            collect_region(arena, *r, out);
            regions_of(arena, *r, seen, out);
        }
        Desc::MaxEff(parts) | Desc::RUnion(parts) => {
            for p in parts.clone() {
                regions_of(arena, p, seen, out);
            }
        }
        Desc::Con(_, args) => {
            // The last argument of a region-carrying constructor is its region,
            // but rather than special-casing each one, every argument that is
            // *shaped* like a region is collected — a bare name or a union.
            for a in args.clone() {
                collect_region(arena, a, out);
                regions_of(arena, a, seen, out);
            }
        }
        Desc::Subr { effect, args, result } => {
            regions_of(arena, *effect, seen, out);
            for a in args.clone() {
                regions_of(arena, a, seen, out);
            }
            regions_of(arena, *result, seen, out);
        }
        Desc::Vsubr { effect, args, rest, result } => {
            regions_of(arena, *effect, seen, out);
            for a in args.clone() {
                regions_of(arena, a, seen, out);
            }
            regions_of(arena, *rest, seen, out);
            regions_of(arena, *result, seen, out);
        }
        Desc::Poly { body, .. } | Desc::DAbs { body, .. } => regions_of(arena, *body, seen, out),
        Desc::RecordOf { fields, region } | Desc::OneOf { variants: fields, region } => {
            for (_, t) in fields.clone() {
                regions_of(arena, t, seen, out);
            }
            collect_region(arena, *region, out);
        }
        Desc::DApp { fun, args } => {
            regions_of(arena, *fun, seen, out);
            for a in args.clone() {
                regions_of(arena, a, seen, out);
            }
        }
        Desc::Var(_) | Desc::Pure | Desc::Hole => {}
    }
}

/// Region-shaped descriptions: a name beginning `@`, or a variable, or a union
/// of those.
fn collect_region(arena: &Arena, id: DescId, out: &mut Vec<DescId>) {
    match arena.get(id) {
        Desc::RUnion(parts) => {
            for p in parts.clone() {
                collect_region(arena, p, out);
            }
        }
        Desc::Con(_, args) if args.is_empty() => {
            if !out.contains(&id) {
                out.push(id);
            }
        }
        Desc::Var(_) => {
            if !out.contains(&id) {
                out.push(id);
            }
        }
        _ => {}
    }
}

fn has_alloc_of(arena: &Arena, effect: DescId, region: DescId, rel: &Rel<'_>) -> bool {
    match arena.get(effect) {
        Desc::Alloc(r) => rel.region_equal(*r, region, &Default::default(), &Default::default()),
        Desc::MaxEff(parts) => {
            parts.clone().iter().any(|p| has_alloc_of(arena, *p, region, rel))
        }
        _ => false,
    }
}

/// Drop every atom of `effect` whose region is exactly `region`.
fn delete_region(
    arena: &mut Arena,
    effect: DescId,
    region: DescId,
    immutable: fixpt_read::Sym,
    ref_name: fixpt_read::Sym,
) -> DescId {
    let atoms: Vec<DescId> = match arena.get(effect) {
        Desc::MaxEff(parts) => parts.clone(),
        _ => vec![effect],
    };
    let mut kept = Vec::new();
    for atom in atoms {
        let r = match arena.get(atom) {
            Desc::Read(r) | Desc::Write(r) | Desc::Alloc(r) => Some(*r),
            _ => None,
        };
        let drop = match r {
            Some(r) => {
                let rel = Rel::new(arena, immutable, ref_name);
                rel.region_equal(r, region, &Default::default(), &Default::default())
            }
            None => false,
        };
        if !drop {
            kept.push(atom);
        }
    }
    arena.maxeff(kept)
}
