//! The mutable environments the checker threads through everything.
//!
//! `utils.scm` keys these on a variable's *alpha name* — a dense integer — and
//! stores the domain alongside the value, because alpha-renaming does not
//! separate description variables from value variables. A lookup that ignored
//! the domain would happily return a kind where a type was wanted; the comment
//! there says to think of `(lambda ((x t)) t)`.
//!
//! They are mutable and global rather than threaded, which is safe precisely
//! *because* everything is alpha-renamed: no two binders share a slot.

use crate::ast::{Domain, FxId, Kind, VarData};

/// What the type/kind environment holds. Which case applies is determined by
/// the variable's domain, not by inspection.
#[derive(Clone, Debug)]
pub enum TkEntry {
    /// A description variable's kind.
    Kind(Kind),
    /// A value variable's type.
    Type(FxId),
}

impl TkEntry {
    pub fn as_kind(&self) -> Option<&Kind> {
        match self {
            TkEntry::Kind(k) => Some(k),
            TkEntry::Type(_) => None,
        }
    }
    pub fn as_type(&self) -> Option<FxId> {
        match self {
            TkEntry::Type(t) => Some(*t),
            TkEntry::Kind(_) => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct VarEnv<T> {
    slots: Vec<Option<(T, Domain)>>,
}

impl<T> Default for VarEnv<T> {
    fn default() -> VarEnv<T> {
        VarEnv { slots: Vec::new() }
    }
}

impl<T: Clone> VarEnv<T> {
    pub fn new() -> VarEnv<T> {
        VarEnv::default()
    }

    fn grow(&mut self, index: usize) {
        if index >= self.slots.len() {
            self.slots.resize_with(index + 1, || None);
        }
    }

    /// Look up by variable. Returns `None` when unbound *or* when the stored
    /// entry belongs to the other domain.
    pub fn get(&self, v: &VarData) -> Option<&T> {
        let slot = self.slots.get(v.name as usize)?.as_ref()?;
        if slot.1 == v.domain { Some(&slot.0) } else { None }
    }

    pub fn set(&mut self, v: &VarData, value: T) {
        self.grow(v.name as usize);
        self.slots[v.name as usize] = Some((value, v.domain));
    }

    pub fn remove(&mut self, v: &VarData) {
        if (v.name as usize) < self.slots.len() {
            self.slots[v.name as usize] = None;
        }
    }

    /// `set-variable-env!`: replace the contents wholesale, as the REPL loop
    /// does between top-level forms.
    pub fn restore(&mut self, other: &VarEnv<T>) {
        self.slots.clear();
        self.slots.extend(other.slots.iter().cloned());
    }

    /// `clear-variable-env!`
    pub fn clear(&mut self) {
        for slot in &mut self.slots {
            *slot = None;
        }
    }

    pub fn len(&self) -> usize {
        self.slots.len()
    }
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}
