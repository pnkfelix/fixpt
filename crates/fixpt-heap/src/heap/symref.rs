//! The Rust side's hold on an interned symbol (`TODO.md` §292, step 5, the
//! user's design, 2026-11-18): a [`SymbolRef`].
//!
//! An interned symbol's place in the heap's symbols table is its identity
//! and its global's slot (the symbols and the globals tables grow
//! together); an uninterned symbol the Rust side holds is kept in a table
//! of its own, as a root. A place is a number, which the heap cannot see the Rust
//! side keep; so the Rust side keeps no bare number past the call it got it
//! in, but a `SymbolRef`, which pins the place as long as it, or a clone of
//! it, lives: a collection that frees symbols nothing holds frees no pinned
//! one. The place itself is the heap's alone: a ref reads and sets its
//! global through the heap, and code holds the symbol, not its place.
//!
//! Its pins are counts the heap shares with its refs (`Rc`, one thread's,
//! as the heap is), so a ref is dropped, and its pin let go, without the
//! heap at hand.

use std::cell::RefCell;
use std::rc::Rc;

use super::tables::Place;

/// An entry of the heap's table of the uninterned symbols the Rust side
/// holds (`Heap::sym_handles`): the heap's alone.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) struct HandleIx(u32);

impl HandleIx {
    #[inline]
    pub(crate) fn new(j: usize) -> HandleIx {
        HandleIx(u32::try_from(j).expect("fewer than 2^32 symbols held"))
    }
    #[inline]
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

/// What a ref holds: an interned symbol's place, or an uninterned one's
/// entry in the table of those held.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum Held {
    Place(Place),
    Handle(HandleIx),
}

/// How many [`SymbolRef`]s hold each place and each entry.
#[derive(Default)]
pub(crate) struct Pins {
    places: RefCell<Vec<u32>>,
    handles: RefCell<Vec<u32>>,
}

impl Pins {
    /// A ref holding `held`.
    pub(crate) fn pin(self: &Rc<Pins>, held: Held) -> SymbolRef {
        let (counts, i) = self.counts(held);
        let mut c = counts.borrow_mut();
        if c.len() <= i {
            c.resize(i + 1, 0);
        }
        c[i] += 1;
        SymbolRef { held, pins: self.clone() }
    }

    fn counts(&self, held: Held) -> (&RefCell<Vec<u32>>, usize) {
        match held {
            Held::Place(p) => (&self.places, p.index()),
            Held::Handle(j) => (&self.handles, j.index()),
        }
    }

    /// Whether some ref holds `held`.
    pub(crate) fn pinned(&self, held: Held) -> bool {
        let (counts, i) = self.counts(held);
        counts.borrow().get(i).is_some_and(|&n| n > 0)
    }

    /// How many places are pinned.
    pub(crate) fn count(&self) -> usize {
        self.places.borrow().iter().filter(|&&n| n > 0).count()
    }
}

/// A symbol of a heap's, held by the Rust side (`Heap::symbol_ref`): an
/// interned one's place pinned, an uninterned one kept as a root, while
/// this, or a clone, lives. Read through the heap it is of
/// ([`Heap::symbol_of`](crate::heap::Heap::symbol_of),
/// [`global_at`](crate::heap::Heap::global_at)), which refuses another's.
pub struct SymbolRef {
    held: Held,
    pins: Rc<Pins>,
}

impl SymbolRef {
    /// What it holds: the heap's alone, read while this ref lives.
    #[inline]
    pub(crate) fn held(&self) -> Held {
        self.held
    }

    /// Whether it is of the heap whose pins are `pins`.
    #[inline]
    pub(crate) fn of(&self, pins: &Rc<Pins>) -> bool {
        Rc::ptr_eq(&self.pins, pins)
    }
}

impl Clone for SymbolRef {
    fn clone(&self) -> SymbolRef {
        self.pins.pin(self.held)
    }
}

impl Drop for SymbolRef {
    fn drop(&mut self) {
        let (counts, i) = self.pins.counts(self.held);
        counts.borrow_mut()[i] -= 1;
    }
}

impl PartialEq for SymbolRef {
    fn eq(&self, other: &SymbolRef) -> bool {
        self.held == other.held && Rc::ptr_eq(&self.pins, &other.pins)
    }
}
impl Eq for SymbolRef {}

impl std::fmt::Debug for SymbolRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SymbolRef({:?})", self.held)
    }
}
