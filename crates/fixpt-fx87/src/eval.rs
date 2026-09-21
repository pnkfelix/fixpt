//! Evaluating descriptions — `eval-texp`, `eval-eexp`, `eval-rexp`.
//!
//! A description as written is not yet the description it means. `(listof int
//! @=)` is a constructor applied to arguments, and the constructor is defined
//! in the standard `d-store` as
//!
//! ```text
//! (dlambda ((t type) (r region)) (dletrec ((list (pairof t list r))) list))
//! ```
//!
//! so the type it denotes is `μX. (pairof int X @=)` — which is why
//! `(list 1 2 3)` prints as a `dletrec` rather than as a `listof`. Evaluation
//! is what turns the first into the second, and nothing can be compared until
//! it has happened: `type-less?` works on evaluated descriptions.
//!
//! # Substituting into a cyclic description
//!
//! The hard part. `listof`'s body contains itself, so a naive substituting copy
//! would not terminate. The copy therefore allocates a [`hole`](Arena::hole)
//! for each node *before* copying its children and remembers it — so a
//! recursive occurrence finds the hole and points at it, and the knot is tied
//! in the copy exactly as it was in the original.
//!
//! This is the same shape as the collector's forwarding pointers, and for the
//! same reason: copying a graph that contains cycles needs somewhere to record
//! "this one is already being copied, here is where it went".

use crate::ast::{Arena, Desc, DescId};
use fixpt_read::Sym;
use std::collections::HashMap;

/// What each description constructor denotes.
pub type DStore = HashMap<Sym, DescId>;

/// Expand `id` until its head is no longer a defined constructor.
///
/// Only the head: the arguments are evaluated as they are substituted, and
/// forcing the whole tree eagerly would not terminate on a recursive type.
pub fn eval(arena: &mut Arena, store: &DStore, id: DescId) -> DescId {
    let mut current = id;
    // A defined constructor could in principle expand to another; bound so a
    // malformed store cannot hang the checker.
    for _ in 0..64 {
        let next = eval_step(arena, store, current);
        if next == current {
            return current;
        }
        current = next;
    }
    current
}

fn eval_step(arena: &mut Arena, store: &DStore, id: DescId) -> DescId {
    match arena.get(id).clone() {
        Desc::Con(name, args) => {
            let Some(definition) = store.get(&name).copied() else { return id };
            // An identity entry — `(int int)` — denotes itself.
            if let Desc::Con(other, inner) = arena.get(definition)
                && *other == name
                && inner.is_empty()
            {
                return id;
            }
            if args.is_empty() {
                return definition;
            }
            apply(arena, definition, &args).unwrap_or(id)
        }
        Desc::DApp { fun, args } => apply(arena, fun, &args).unwrap_or(id),
        _ => id,
    }
}

/// Beta-reduce a `dlambda` applied to arguments.
fn apply(arena: &mut Arena, fun: DescId, args: &[DescId]) -> Option<DescId> {
    let Desc::DAbs { binders, body } = arena.get(fun).clone() else { return None };
    if binders.len() != args.len() {
        return None;
    }
    let map: HashMap<Sym, DescId> =
        binders.iter().map(|b| b.name).zip(args.iter().copied()).collect();
    Some(substitute(arena, body, &map))
}

/// Copy `id`, replacing free description variables according to `map`.
///
/// Cycle-safe: see the module docs.
pub fn substitute(arena: &mut Arena, id: DescId, map: &HashMap<Sym, DescId>) -> DescId {
    if map.is_empty() {
        return id;
    }
    let mut memo = HashMap::new();
    copy(arena, id, map, &mut memo)
}

fn copy(
    arena: &mut Arena,
    id: DescId,
    map: &HashMap<Sym, DescId>,
    memo: &mut HashMap<DescId, DescId>,
) -> DescId {
    if let Some(done) = memo.get(&id) {
        return *done;
    }
    // A substituted variable is answered before a hole is made for it, so the
    // result is the argument itself rather than a copy of it.
    if let Desc::Var(v) = arena.get(id)
        && let Some(replacement) = map.get(v)
    {
        return *replacement;
    }
    // Everything else gets a hole first, so a recursive occurrence inside the
    // children finds it and the copy ends up with the same knot.
    let hole = arena.hole();
    memo.insert(id, hole);
    let rebuilt = match arena.get(id).clone() {
        Desc::Var(v) => Desc::Var(v),
        Desc::Pure => Desc::Pure,
        Desc::Hole => Desc::Hole,
        Desc::Con(name, args) => Desc::Con(name, copy_all(arena, &args, map, memo)),
        Desc::Subr { effect, args, result } => Desc::Subr {
            effect: copy(arena, effect, map, memo),
            args: copy_all(arena, &args, map, memo),
            result: copy(arena, result, map, memo),
        },
        Desc::Vsubr { effect, args, rest, result } => Desc::Vsubr {
            effect: copy(arena, effect, map, memo),
            args: copy_all(arena, &args, map, memo),
            rest: copy(arena, rest, map, memo),
            result: copy(arena, result, map, memo),
        },
        Desc::Poly { binders, body } => {
            // A binder shadows: the substitution does not reach inside.
            let inner = shadowed(map, &binders);
            Desc::Poly { binders, body: copy(arena, body, &inner, memo) }
        }
        Desc::DAbs { binders, body } => {
            let inner = shadowed(map, &binders);
            Desc::DAbs { binders, body: copy(arena, body, &inner, memo) }
        }
        Desc::RecordOf { fields, region } => Desc::RecordOf {
            fields: copy_fields(arena, &fields, map, memo),
            region: copy(arena, region, map, memo),
        },
        Desc::OneOf { variants, region } => Desc::OneOf {
            variants: copy_fields(arena, &variants, map, memo),
            region: copy(arena, region, map, memo),
        },
        Desc::Read(r) => Desc::Read(copy(arena, r, map, memo)),
        Desc::Write(r) => Desc::Write(copy(arena, r, map, memo)),
        Desc::Alloc(r) => Desc::Alloc(copy(arena, r, map, memo)),
        Desc::MaxEff(parts) => Desc::MaxEff(copy_all(arena, &parts, map, memo)),
        Desc::RUnion(parts) => Desc::RUnion(copy_all(arena, &parts, map, memo)),
        Desc::DApp { fun, args } => Desc::DApp {
            fun: copy(arena, fun, map, memo),
            args: copy_all(arena, &args, map, memo),
        },
    };
    arena.fill(hole, rebuilt);
    hole
}

/// A `dlambda` or `poly` binder hides an outer substitution of the same name.
fn shadowed(map: &HashMap<Sym, DescId>, binders: &[crate::ast::Binder]) -> HashMap<Sym, DescId> {
    let mut inner = map.clone();
    for b in binders {
        inner.remove(&b.name);
    }
    inner
}

fn copy_all(
    arena: &mut Arena,
    ids: &[DescId],
    map: &HashMap<Sym, DescId>,
    memo: &mut HashMap<DescId, DescId>,
) -> Vec<DescId> {
    ids.iter().map(|d| copy(arena, *d, map, memo)).collect()
}

fn copy_fields(
    arena: &mut Arena,
    fields: &[(Sym, DescId)],
    map: &HashMap<Sym, DescId>,
    memo: &mut HashMap<DescId, DescId>,
) -> Vec<(Sym, DescId)> {
    fields.iter().map(|(n, d)| (*n, copy(arena, *d, map, memo))).collect()
}
