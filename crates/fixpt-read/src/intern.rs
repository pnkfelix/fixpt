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

    pub fn get(&self, name: &str) -> Option<Sym> {
        self.index.get(name).copied()
    }

    pub fn name(&self, s: Sym) -> &str {
        &self.names[s.0 as usize]
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}
