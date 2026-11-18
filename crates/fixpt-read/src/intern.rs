//! Compile-time symbol interning: names as the Rust side holds them
//! (`TODO.md` §292, the user's design, 2026-11-17).
//!
//! An `Interner` holds names of a names space (`fixpt_memmgmt::names`):
//! its heap's, given ([`Interner::of_names`]), so that a name is kept once
//! for the heap and the Rust side alike, and a `Sym` is the name's number
//! there, the heap's own for it; or one of its own, where there is no heap
//! ([`Interner::new`]). What it holds no sweep of the heap frees; what it
//! lets go ([`truncate`](Interner::truncate)) the heap may. A name is read
//! where it is kept, as a `&str` borrowed from the interner. Front ends
//! compare symbols by `Sym` equality, which is a `u32` comparison.
//!
//! An uninterned symbol ([`Interner::uninterned`]) is the interner's own:
//! a name for printing, in no space, so that reading its name gives
//! another symbol.

use fixpt_memmgmt::names::{Holder, Owner};

/// A symbol: a name's number in its interner's space, or, from
/// [`UNINTERNED`] up, an uninterned symbol of its interner's. In a debug
/// build it carries its space's id too, checked where it is read, so that
/// one interner's `Sym` read by an interner of another space is refused,
/// not taken for another name.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Sym {
    n: u32,
    #[cfg(debug_assertions)]
    space: u32,
}

/// The first number of an uninterned symbol.
const UNINTERNED: u32 = 1 << 31;

impl Sym {
    /// Its number: a name's in its space (below `1 << 31`), or an
    /// uninterned symbol's of its interner's.
    #[inline]
    pub fn index(self) -> u32 {
        self.n
    }
}

pub struct Interner {
    names: Holder,
    /// The uninterned symbols' names, in order.
    uninterned: Vec<String>,
    /// Each symbol made, interned or not, in order: what `len` counts and
    /// `truncate` undoes.
    made: Vec<Sym>,
}

impl Default for Interner {
    fn default() -> Interner {
        Interner::new()
    }
}

impl Interner {
    /// An interner of names of its own.
    pub fn new() -> Interner {
        Interner::holding(Holder::new())
    }

    /// An interner of names of `names`, a heap's: its `Sym`s the names'
    /// numbers there.
    pub fn of_names(names: &Owner) -> Interner {
        Interner::holding(names.holder())
    }

    fn holding(names: Holder) -> Interner {
        Interner { names, uninterned: Vec::new(), made: Vec::new() }
    }

    #[inline]
    fn sym(&self, n: u32) -> Sym {
        Sym {
            n,
            #[cfg(debug_assertions)]
            space: self.names.space_id(),
        }
    }

    /// Whether `s` is of this interner's space (always, but in a debug
    /// build, where a `Sym` says).
    #[inline]
    fn mine(&self, s: Sym) {
        #[cfg(debug_assertions)]
        assert_eq!(s.space, self.names.space_id(), "{s:?}: a symbol of another interner's names");
        let _ = s;
    }

    pub fn intern(&mut self, name: &str) -> Sym {
        if let Some(n) = self.names.find(name) {
            return self.sym(n);
        }
        let n = self.names.hold_text(name);
        let s = self.sym(n);
        self.made.push(s);
        s
    }

    /// The symbol of name number `n` of this interner's space (a heap
    /// symbol's, `Heap::symbol_text`), held: none if it is no name there.
    pub fn of_number(&mut self, n: u32) -> Option<Sym> {
        if self.names.holds(n) {
            return Some(self.sym(n));
        }
        if !self.names.hold(n) {
            return None;
        }
        let s = self.sym(n);
        self.made.push(s);
        Some(s)
    }

    /// A symbol no source text can produce: it has a name, for printing, but
    /// it is not in the index, so reading that name — even spelled with `|…|`
    /// and escapes — yields a *different* symbol. This is what a hygienic
    /// rename needs, and what a leading space in a gensym only approximates.
    pub fn uninterned(&mut self, name: &str) -> Sym {
        let i = u32::try_from(self.uninterned.len()).ok().filter(|&i| i < UNINTERNED).expect("too many uninterned symbols");
        self.uninterned.push(name.to_string());
        let s = self.sym(UNINTERNED + i);
        self.made.push(s);
        s
    }

    /// Whether `s` is uninterned ([`uninterned`](Interner::uninterned)).
    pub fn is_uninterned(&self, s: Sym) -> bool {
        s.n >= UNINTERNED
    }

    /// Forget every symbol made since the interner had `len`: their names
    /// let go, for the heap's sweep to free if nothing else holds them.
    ///
    /// For work that must leave no trace — checking a form while it is still
    /// being typed — whose symbols nothing will refer to afterwards. A later
    /// `intern` may make the same numbers again, so nothing that outlives the
    /// work may hold one of the forgotten symbols.
    pub fn truncate(&mut self, len: usize) {
        if len >= self.made.len() {
            return;
        }
        let interned = self.made[..len].iter().filter(|s| !self.is_uninterned(**s)).count();
        let uninterned = len - interned;
        self.made.truncate(len);
        self.names.release_to(interned);
        self.uninterned.truncate(uninterned);
    }

    /// The symbol `name`, if this interner interned it.
    pub fn get(&self, name: &str) -> Option<Sym> {
        self.names.find(name).map(|n| self.sym(n))
    }

    pub fn name(&self, s: Sym) -> &str {
        self.mine(s);
        if s.n >= UNINTERNED {
            return &self.uninterned[(s.n - UNINTERNED) as usize];
        }
        self.names.get(s.n).unwrap_or_else(|| panic!("{s:?}: no symbol this interner holds"))
    }

    /// Whether this interner's names are `names`' (a heap's).
    pub fn is_of(&self, names: &Owner) -> bool {
        self.names.same_space(names)
    }

    pub fn len(&self) -> usize {
        self.made.len()
    }
    /// Every name interned so far, in the order they were first seen.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.made.iter().map(|&s| self.name(s))
    }

    pub fn is_empty(&self) -> bool {
        self.made.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_name_is_one_symbol_and_an_uninterned_one_another() {
        let mut i = Interner::new();
        let x = i.intern("x");
        assert_eq!(i.intern("x"), x);
        let u = i.uninterned("x");
        assert_ne!(u, x);
        assert_eq!((i.name(x), i.name(u)), ("x", "x"));
        assert_eq!(i.get("x"), Some(x));
        assert!(i.is_uninterned(u) && !i.is_uninterned(x));
        assert_eq!(i.names().collect::<Vec<_>>(), ["x", "x"]);
    }

    #[test]
    fn truncate_forgets_what_was_made_since() {
        let mut i = Interner::new();
        let a = i.intern("a");
        let mark = i.len();
        i.intern("b");
        i.uninterned("u");
        i.intern("a");
        i.truncate(mark);
        assert_eq!(i.len(), 1);
        assert_eq!((i.get("a"), i.get("b")), (Some(a), None));
        let c = i.intern("c");
        assert_eq!(i.name(c), "c");
    }

    /// Two interners of one heap's names: a name one symbol for both, its
    /// number the heap's; each reads only what it holds.
    #[test]
    fn interners_of_one_space_share_its_numbers() {
        let o = Owner::new();
        let n = o.intern("shared");
        let (mut a, mut b) = (Interner::of_names(&o), Interner::of_names(&o));
        let (x, y) = (a.intern("shared"), b.intern("shared"));
        assert_eq!((x, y.index()), (y, n));
        assert_eq!(a.of_number(n), Some(x));
        assert!(a.is_of(&o) && !Interner::new().is_of(&o));
        assert_eq!(b.get("other"), None);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "another interner's names")]
    fn another_spaces_symbol_is_refused() {
        let mut a = Interner::new();
        let b = Interner::new();
        let x = a.intern("x");
        b.name(x);
    }
}
