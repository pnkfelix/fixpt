//! The Rust side's hold on an interned symbol (`TODO.md` §292, step 5, the
//! user's design, 2026-11-18): a [`SymbolRef`].
//!
//! An interned symbol's place in the heap's symbols table is its identity,
//! its global's slot (the symbols and the globals tables grow together),
//! and its handle. A place is a number, which the heap cannot see the Rust
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

/// How many [`SymbolRef`]s pin each place.
#[derive(Default)]
pub(crate) struct Pins {
    counts: RefCell<Vec<u32>>,
}

impl Pins {
    /// A ref pinning `place`.
    pub(crate) fn pin(self: &Rc<Pins>, place: Place) -> SymbolRef {
        let mut c = self.counts.borrow_mut();
        let i = place.index();
        if c.len() <= i {
            c.resize(i + 1, 0);
        }
        c[i] += 1;
        SymbolRef { place, pins: self.clone() }
    }

    /// Whether some ref pins `place`.
    #[allow(dead_code)]
    pub(crate) fn pinned(&self, place: Place) -> bool {
        self.counts.borrow().get(place.index()).is_some_and(|&n| n > 0)
    }

    /// How many places are pinned.
    pub(crate) fn count(&self) -> usize {
        self.counts.borrow().iter().filter(|&&n| n > 0).count()
    }
}

/// An interned symbol of a heap's, held by the Rust side: its place pinned
/// while this, or a clone, lives (`Heap::symbol_ref`). Read through the heap
/// it is of ([`Heap::symbol_of`](crate::heap::Heap::symbol_of),
/// [`global_at`](crate::heap::Heap::global_at)), which refuses another's.
pub struct SymbolRef {
    place: Place,
    pins: Rc<Pins>,
}

impl SymbolRef {
    /// Its place: the heap's alone, read while this ref lives.
    #[inline]
    pub(crate) fn place(&self) -> Place {
        self.place
    }

    /// Whether it is of the heap whose pins are `pins`.
    #[inline]
    pub(crate) fn of(&self, pins: &Rc<Pins>) -> bool {
        Rc::ptr_eq(&self.pins, pins)
    }
}

impl Clone for SymbolRef {
    fn clone(&self) -> SymbolRef {
        self.pins.pin(self.place)
    }
}

impl Drop for SymbolRef {
    fn drop(&mut self) {
        self.pins.counts.borrow_mut()[self.place.index()] -= 1;
    }
}

impl PartialEq for SymbolRef {
    fn eq(&self, other: &SymbolRef) -> bool {
        self.place == other.place && Rc::ptr_eq(&self.pins, &other.pins)
    }
}
impl Eq for SymbolRef {}

impl std::fmt::Debug for SymbolRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SymbolRef({})", self.place.index())
    }
}
