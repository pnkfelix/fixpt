//! The type/kind environment — `tk-env`.
//!
//! One environment holds two namespaces, because FX-87 has two: value
//! variables have a *type* and a *region*, description variables have a
//! *kind*. The reference keeps both in one structure keyed by a domain tag, and
//! for the same reason FX-91 does — `(lambda ((x t)) t)` is legal, so `x` and
//! `t` can share a name without sharing a binding.
//!
//! # Why a value binding carries a region
//!
//! `desc-of-variable` gives a variable the effect `(read r)` for the region `r`
//! it was bound in. An ordinary immutable binding lives in `@=`, where reading
//! is pure; a mutable one lives somewhere that can be written, and merely
//! *mentioning* it is then an effect. That is how FX-87 makes the cost of
//! mutable state visible in the type of everything that touches it.

use crate::ast::DescId;
use crate::ast::Kind;
use fixpt_read::Sym;

#[derive(Clone, Debug)]
pub struct ValueBinding {
    pub ty: DescId,
    /// Where the binding lives. Reading it costs `(read region)`.
    pub region: DescId,
}

/// A scope, chained rather than copied so that entering one is cheap.
#[derive(Clone, Default)]
pub struct TkEnv {
    values: Vec<(Sym, ValueBinding)>,
    descs: Vec<(Sym, Kind)>,
}

impl TkEnv {
    pub fn new() -> TkEnv {
        TkEnv::default()
    }

    pub fn bind_value(&mut self, name: Sym, binding: ValueBinding) {
        self.values.push((name, binding));
    }

    pub fn bind_desc(&mut self, name: Sym, kind: Kind) {
        self.descs.push((name, kind));
    }

    /// Innermost binding wins, so shadowing works by pushing.
    pub fn value(&self, name: Sym) -> Option<&ValueBinding> {
        self.values.iter().rev().find(|(n, _)| *n == name).map(|(_, b)| b)
    }

    pub fn desc(&self, name: Sym) -> Option<&Kind> {
        self.descs.iter().rev().find(|(n, _)| *n == name).map(|(_, k)| k)
    }

    pub fn value_names(&self) -> impl Iterator<Item = Sym> + '_ {
        self.values.iter().map(|(n, _)| *n)
    }

    /// The names bound as descriptions: types, effects and regions.
    pub fn desc_names(&self) -> impl Iterator<Item = Sym> + '_ {
        self.descs.iter().map(|(n, _)| *n)
    }

    /// A scope entered on top of this one.
    pub fn child(&self) -> TkEnv {
        self.clone()
    }
}
