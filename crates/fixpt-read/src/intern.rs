//! Compile-time symbol interning.
//!
//! Distinct from the heap's symbol table: this one is Rust-side, holds no
//! `Value`s, and so is unaffected by collection. Front ends compare symbols by
//! `Sym` equality, which is a `u32` comparison.

use std::collections::HashMap;

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Sym(pub u32);

#[derive(Default)]
pub struct Interner {
    names: Vec<String>,
    index: HashMap<String, Sym>,
}

impl Interner {
    pub fn new() -> Interner {
        Interner::default()
    }

    pub fn intern(&mut self, name: &str) -> Sym {
        if let Some(&s) = self.index.get(name) {
            return s;
        }
        let s = Sym(self.names.len() as u32);
        self.names.push(name.to_string());
        self.index.insert(name.to_string(), s);
        s
    }

    /// A symbol no source text can produce: it has a name, for printing, but
    /// it is not in the index, so reading that name — even spelled with `|…|`
    /// and escapes — yields a *different* symbol. This is what a hygienic
    /// rename needs, and what a leading space in a gensym only approximates.
    pub fn uninterned(&mut self, name: &str) -> Sym {
        let s = Sym(self.names.len() as u32);
        self.names.push(name.to_string());
        s
    }

    /// Forget every symbol interned since the table had `len` entries.
    ///
    /// For work that must leave no trace — checking a form while it is still
    /// being typed — whose symbols nothing will refer to afterwards. A later
    /// `intern` reuses the slots, so nothing that outlives the work may hold
    /// one of the forgotten symbols.
    pub fn truncate(&mut self, len: usize) {
        if len >= self.names.len() {
            return;
        }
        self.names.truncate(len);
        self.index.retain(|_, s| (s.0 as usize) < len);
    }

    pub fn get(&self, name: &str) -> Option<Sym> {
        self.index.get(name).copied()
    }

    pub fn name(&self, s: Sym) -> &str {
        &self.names[s.0 as usize]
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }
    /// Every name interned so far, in the order they were first seen.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        (0..self.len()).map(|i| self.name(Sym(i as u32)))
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}
