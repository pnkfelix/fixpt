//! Free variables — `free.scm`.
//!
//! Four computations, because FX-91 has two domains crossing two syntactic
//! categories: the free *description* and free *value* variables of both
//! descriptions and expressions. Generalisation needs all four.
//!
//! One caching subtlety is load-bearing. A free-variable set that mentions a
//! unification variable is **not** cached, because unification can later
//! replace that variable and the answer would change. Sets over identifier
//! variables only are stable and are cached. `free.scm` guards exactly this
//! way, and dropping the guard produces stale sets that make generalisation
//! quietly wrong rather than loudly broken.

use crate::ast::{Arena, Fx, FxId};

/// `(uniq variable=?)`: drop earlier duplicates, keeping the last occurrence.
fn uniq(arena: &Arena, vars: Vec<FxId>) -> Vec<FxId> {
    let mut out: Vec<FxId> = Vec::with_capacity(vars.len());
    for (i, v) in vars.iter().enumerate() {
        if vars[i + 1..].iter().any(|later| arena.same_variable(*v, *later)) {
            continue;
        }
        out.push(*v);
    }
    out
}

fn without(arena: &Arena, vars: Vec<FxId>, bound: &[FxId]) -> Vec<FxId> {
    vars.into_iter()
        .filter(|v| !bound.iter().any(|b| arena.same_variable(*v, *b)))
        .collect()
}

fn all_identifiers(arena: &Arena, vars: &[FxId]) -> bool {
    vars.iter().all(|v| arena.var(*v).is_some_and(|d| !d.is_unification()))
}

// ------------------------------------------- description variables of a dexp

pub fn free_dvars_of_dexp(arena: &mut Arena, id: FxId) -> Vec<FxId> {
    if let Some(cached) = arena.info(id).free_dvars.clone() {
        return cached;
    }
    let raw = free_dvars_of_dexp_1(arena, id);
    let frees = uniq(arena, raw);
    // Only cache what unification cannot invalidate.
    if all_identifiers(arena, &frees) {
        arena.info_mut(id).free_dvars = Some(frees.clone());
    }
    frees
}

fn concat_dexps(arena: &mut Arena, ids: &[FxId]) -> Vec<FxId> {
    let mut out = Vec::new();
    for i in ids {
        out.extend(free_dvars_of_dexp(arena, *i));
    }
    out
}

fn free_dvars_of_dexp_1(arena: &mut Arena, id: FxId) -> Vec<FxId> {
    match arena.get(id).clone() {
        Fx::Variable(_) => vec![arena.find(id)],
        Fx::DLambda { ids, body, .. } => {
            let inner = free_dvars_of_dexp(arena, body);
            without(arena, inner, &ids)
        }
        Fx::Select { module, .. } => free_dvars_of_exp(arena, module),
        Fx::MaxEff(effects) => concat_dexps(arena, &effects),
        // A subr's own identifiers are *value* variables, so nothing is bound
        // here from the description domain's point of view.
        Fx::Subr { effect, types, body, .. } => {
            let mut out = free_dvars_of_dexp(arena, effect);
            out.extend(concat_dexps(arena, &types));
            out.extend(free_dvars_of_dexp(arena, body));
            out
        }
        Fx::Poly { ids, body, .. } | Fx::PolyTilde { ids, body, .. } => {
            let inner = free_dvars_of_dexp(arena, body);
            without(arena, inner, &ids)
        }
        Fx::ModuleOf { abs_ids, val_types, .. } => {
            let inner = concat_dexps(arena, &val_types);
            without(arena, inner, &abs_ids)
        }
        Fx::SumOf { types, .. } | Fx::ProductOf { types, .. } => concat_dexps(arena, &types),
        Fx::DApp { rator, rands } => {
            let mut out = free_dvars_of_dexp(arena, rator);
            out.extend(concat_dexps(arena, &rands));
            out
        }
        _ => Vec::new(),
    }
}

// -------------------------------------------------- value variables of a dexp

pub fn free_vars_of_dexp(arena: &mut Arena, id: FxId) -> Vec<FxId> {
    if let Some(cached) = arena.info(id).free_vars.clone() {
        return cached;
    }
    let raw = free_vars_of_dexp_1(arena, id);
    let frees = uniq(arena, raw);
    arena.info_mut(id).free_vars = Some(frees.clone());
    frees
}

fn concat_vars_of_dexps(arena: &mut Arena, ids: &[FxId]) -> Vec<FxId> {
    let mut out = Vec::new();
    for i in ids {
        out.extend(free_vars_of_dexp(arena, *i));
    }
    out
}

fn free_vars_of_dexp_1(arena: &mut Arena, id: FxId) -> Vec<FxId> {
    match arena.get(id).clone() {
        Fx::Variable(_) | Fx::MaxEff(_) => Vec::new(),
        Fx::DLambda { body, .. } | Fx::Poly { body, .. } | Fx::PolyTilde { body, .. } => {
            free_vars_of_dexp(arena, body)
        }
        Fx::Select { module, .. } => free_vars_of_exp(arena, module),
        // Dependent bindings: a later parameter's type may mention an earlier
        // parameter, so each type's frees are taken against the binders seen
        // so far.
        Fx::Subr { ids, types, body, .. } => {
            let mut bound: Vec<FxId> = Vec::new();
            let mut out = Vec::new();
            for (i, t) in ids.iter().zip(&types) {
                let frees = free_vars_of_dexp(arena, *t);
                out.extend(without(arena, frees, &bound));
                bound.push(*i);
            }
            let body_frees = free_vars_of_dexp(arena, body);
            out.extend(without(arena, body_frees, &bound));
            out
        }
        Fx::ModuleOf { val_types, .. } => concat_vars_of_dexps(arena, &val_types),
        Fx::SumOf { types, .. } | Fx::ProductOf { types, .. } => {
            concat_vars_of_dexps(arena, &types)
        }
        Fx::DApp { rator, rands } => {
            let mut out = free_vars_of_dexp(arena, rator);
            out.extend(concat_vars_of_dexps(arena, &rands));
            out
        }
        _ => Vec::new(),
    }
}

// --------------------------------------------- value variables of expressions

pub fn free_vars_of_exp(arena: &mut Arena, id: FxId) -> Vec<FxId> {
    if let Some(cached) = arena.exp_info(id).exp_free_vars.clone() {
        return cached;
    }
    let raw = free_vars_of_exp_1(arena, id);
    let frees = uniq(arena, raw);
    arena.exp_info_mut(id).exp_free_vars = Some(frees.clone());
    frees
}

fn concat_vars_of_exps(arena: &mut Arena, ids: &[FxId]) -> Vec<FxId> {
    let mut out = Vec::new();
    for i in ids {
        out.extend(free_vars_of_exp(arena, *i));
    }
    out
}

fn free_vars_of_exp_1(arena: &mut Arena, id: FxId) -> Vec<FxId> {
    match arena.get(id).clone() {
        Fx::Variable(_) => vec![arena.find(id)],
        Fx::Lambda { ids, types, body, .. } => {
            let inner = free_vars_of_exp(arena, body);
            let mut out = without(arena, inner, &ids);
            // As in `subr`, parameter types see the parameters before them.
            let mut bound: Vec<FxId> = Vec::new();
            for (i, t) in ids.iter().zip(&types) {
                let frees = free_vars_of_dexp(arena, *t);
                out.extend(without(arena, frees, &bound));
                bound.push(*i);
            }
            out
        }
        Fx::Let { ids, exps, body } => {
            let inner = free_vars_of_exp(arena, body);
            let mut out = without(arena, inner, &ids);
            out.extend(concat_vars_of_exps(arena, &exps));
            out
        }
        Fx::PLambda { body, .. } => free_vars_of_exp(arena, body),
        Fx::Proj { exp, descs } => {
            let mut out = free_vars_of_exp(arena, exp);
            out.extend(concat_vars_of_dexps(arena, &descs));
            out
        }
        Fx::Module {
            up_ids,
            down_ids,
            abs_descs,
            desc_descs,
            define_ids,
            define_exps,
            typed_ids,
            typed_types,
            typed_exps,
            ..
        } => {
            let mut out = concat_vars_of_dexps(arena, &abs_descs);
            out.extend(concat_vars_of_dexps(arena, &desc_descs));
            out.extend(concat_vars_of_dexps(arena, &typed_types));
            let mut bound = up_ids.clone();
            bound.extend(down_ids.iter().copied());
            bound.extend(define_ids.iter().copied());
            bound.extend(typed_ids.iter().copied());
            let mut bodies = define_exps.clone();
            bodies.extend(typed_exps.iter().copied());
            let inner = concat_vars_of_exps(arena, &bodies);
            out.extend(without(arena, inner, &bound));
            out
        }
        // `with` needs the module's *type* to know what its body binds, so it
        // is only meaningful after checking; before then the module's
        // identifiers are unknown and nothing is subtracted.
        Fx::With { module, body, .. } => {
            let mut out = free_vars_of_exp(arena, module);
            let bound = moduleof_identifiers(arena, module);
            let inner = free_vars_of_exp(arena, body);
            out.extend(without(arena, inner, &bound));
            out
        }
        Fx::Extend { module, body, .. } => {
            let mut out = free_vars_of_exp(arena, module);
            out.extend(free_vars_of_exp(arena, body));
            out
        }
        Fx::App { rator, rands } => {
            let mut out = free_vars_of_exp(arena, rator);
            out.extend(concat_vars_of_exps(arena, &rands));
            out
        }
        Fx::If { test, then, els } => {
            // `free.scm` prepends a parsed `#t` here, to stop generalisation
            // over expressions like `(if x x y)`. The marker's identity does
            // not matter, only that the set is non-empty; the test node serves.
            let mut out = vec![arena.find(test)];
            out.extend(free_vars_of_exp(arena, test));
            out.extend(free_vars_of_exp(arena, then));
            out.extend(free_vars_of_exp(arena, els));
            out
        }
        Fx::Open(e) | Fx::Close(e) => free_vars_of_exp(arena, e),
        Fx::Begin(exps) => concat_vars_of_exps(arena, &exps),
        Fx::Load { .. } => Vec::new(),
        Fx::The { ty, exp } | Fx::Does { effect: ty, exp } => {
            let mut out = free_vars_of_dexp(arena, ty);
            out.extend(free_vars_of_exp(arena, exp));
            out
        }
        Fx::Sum { ty, exp, .. } | Fx::Extract { ty, exp, .. } => {
            let mut out = free_vars_of_dexp(arena, ty);
            out.extend(free_vars_of_exp(arena, exp));
            out
        }
        Fx::Product { ty, exps } => {
            let mut out = free_vars_of_dexp(arena, ty);
            out.extend(concat_vars_of_exps(arena, &exps));
            out
        }
        Fx::TagCase { ty, exp, success, failure, .. } => {
            let mut out = free_vars_of_dexp(arena, ty);
            out.extend(free_vars_of_exp(arena, exp));
            out.extend(free_vars_of_exp(arena, success));
            out.extend(free_vars_of_exp(arena, failure));
            out
        }
        _ => Vec::new(),
    }
}

/// Every identifier a checked module type binds: abstractions, descriptions
/// and values together.
pub fn moduleof_identifiers(arena: &Arena, module_exp: FxId) -> Vec<FxId> {
    let Some(ty) = arena.exp_info(module_exp).ty else { return Vec::new() };
    match arena.get(ty) {
        Fx::ModuleOf { abs_ids, desc_ids, val_ids, .. } => {
            let mut out = abs_ids.clone();
            out.extend(desc_ids.iter().copied());
            out.extend(val_ids.iter().copied());
            out
        }
        _ => Vec::new(),
    }
}

// --------------------------------------- description variables of expressions

pub fn free_dvars_of_exp(arena: &mut Arena, id: FxId) -> Vec<FxId> {
    if let Some(cached) = arena.exp_info(id).exp_free_dvars.clone() {
        return cached;
    }
    let raw = free_dvars_of_exp_1(arena, id);
    let frees = uniq(arena, raw);
    if all_identifiers(arena, &frees) {
        arena.exp_info_mut(id).exp_free_dvars = Some(frees.clone());
    }
    frees
}

fn concat_dvars_of_exps(arena: &mut Arena, ids: &[FxId]) -> Vec<FxId> {
    let mut out = Vec::new();
    for i in ids {
        out.extend(free_dvars_of_exp(arena, *i));
    }
    out
}

fn free_dvars_of_exp_1(arena: &mut Arena, id: FxId) -> Vec<FxId> {
    match arena.get(id).clone() {
        // A value variable's description variables are those of its type.
        Fx::Variable(_) => match arena.exp_info(id).ty {
            Some(t) => free_dvars_of_dexp(arena, t),
            None => Vec::new(),
        },
        Fx::Lambda { types, body, .. } => {
            let mut out = concat_dexps(arena, &types);
            out.extend(free_dvars_of_exp(arena, body));
            out
        }
        Fx::Let { exps, body, .. } => {
            let mut out = concat_dvars_of_exps(arena, &exps);
            out.extend(free_dvars_of_exp(arena, body));
            out
        }
        Fx::PLambda { ids, body, .. } => {
            let inner = free_dvars_of_exp(arena, body);
            without(arena, inner, &ids)
        }
        Fx::Proj { exp, descs } => {
            let mut out = free_dvars_of_exp(arena, exp);
            out.extend(concat_dexps(arena, &descs));
            out
        }
        Fx::Module { abs_ids, abs_descs, desc_descs, define_exps, typed_types, typed_exps, .. } => {
            let mut inner = concat_dexps(arena, &abs_descs);
            inner.extend(concat_dexps(arena, &desc_descs));
            inner.extend(concat_dexps(arena, &typed_types));
            inner.extend(concat_dvars_of_exps(arena, &define_exps));
            inner.extend(concat_dvars_of_exps(arena, &typed_exps));
            without(arena, inner, &abs_ids)
        }
        Fx::With { module, body, .. } | Fx::Extend { module, body, .. } => {
            let mut out = free_dvars_of_exp(arena, module);
            let bound = moduleof_identifiers(arena, module);
            let inner = free_dvars_of_exp(arena, body);
            out.extend(without(arena, inner, &bound));
            out
        }
        Fx::App { rator, rands } => {
            let mut out = free_dvars_of_exp(arena, rator);
            out.extend(concat_dvars_of_exps(arena, &rands));
            out
        }
        Fx::If { test, then, els } => {
            let mut out = free_dvars_of_exp(arena, test);
            out.extend(free_dvars_of_exp(arena, then));
            out.extend(free_dvars_of_exp(arena, els));
            out
        }
        Fx::Open(e) | Fx::Close(e) => free_dvars_of_exp(arena, e),
        Fx::Begin(exps) => concat_dvars_of_exps(arena, &exps),
        Fx::Load { .. } => Vec::new(),
        Fx::The { ty, exp } | Fx::Does { effect: ty, exp } => {
            let mut out = free_dvars_of_dexp(arena, ty);
            out.extend(free_dvars_of_exp(arena, exp));
            out
        }
        Fx::Sum { ty, exp, .. } | Fx::Extract { ty, exp, .. } => {
            let mut out = free_dvars_of_dexp(arena, ty);
            out.extend(free_dvars_of_exp(arena, exp));
            out
        }
        Fx::Product { ty, exps } => {
            let mut out = free_dvars_of_dexp(arena, ty);
            out.extend(concat_dvars_of_exps(arena, &exps));
            out
        }
        Fx::TagCase { ty, exp, success, failure, .. } => {
            let mut out = free_dvars_of_dexp(arena, ty);
            out.extend(free_dvars_of_exp(arena, exp));
            out.extend(free_dvars_of_exp(arena, success));
            out.extend(free_dvars_of_exp(arena, failure));
            out
        }
        _ => Vec::new(),
    }
}

/// The description variables of the *types of* an expression's free variables.
/// Generalisation must not quantify over these: they are still live in the
/// environment.
pub fn free_dvars_of_free_vars(arena: &mut Arena, id: FxId) -> Vec<FxId> {
    let frees = free_vars_of_exp(arena, id);
    let mut out = Vec::new();
    for v in frees {
        if let Some(t) = arena.exp_info(v).ty {
            out.extend(free_dvars_of_dexp(arena, t));
        }
    }
    uniq(arena, out)
}
