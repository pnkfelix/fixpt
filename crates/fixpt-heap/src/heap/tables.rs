//! The global variables' cells and the interned symbols (`TODO.md` §264):
//! each a table of chunks of [`CHUNK`] slots, a slot's index its chunk and
//! the chunk's field. A slot is written by [`Heap::set_slot`], so the write
//! barrier marks its card as any other field's; no collection looks at
//! every slot (as each did while they were vectors beside the heap, every
//! slot a root).
//!
//! What an image brought is in the tables area, a generation of its own
//! between the old space and the code area (static ≫ code ≫ tables ≫ old ≫
//! nursery): chunks that never move and are never freed, put one after the
//! other, never one between two others, so the area has no hole. A minor
//! collection scans its cards of the first table; one of the old space,
//! its cards of either; a code collection, all of it, as roots, so that it
//! marks the code a global holds. Nothing points to the area's chunks but
//! the tables, so nothing it holds need be remembered elsewhere: what it
//! refers to in the code area is older, and found by the code collection
//! that scans it.
//!
//! What is made at run time is in chunks of the heap's own, objects as any
//! other: made young, promoted and moved by the collections, each chunk the
//! tables hold forwarded as a root. (A major collection might one day move
//! those that survive into the tables area.) Never in a region, which may
//! end.
//!
//! An image carries the tables as lists of values (`image_parts_at`), not
//! their chunks; its reader puts them in its tables area.

use super::{CODE_BASE, Heap, TABLES_BASE, read_head};
use crate::layout;
use crate::value::{Value, make_header};

/// Slots in a chunk: a power of two.
pub(super) const CHUNK: usize = 256;
const CHUNK_SHIFT: u32 = CHUNK.trailing_zeros();

/// One table: its chunks, in order, and how many slots are in use.
#[derive(Default)]
pub(super) struct Table {
    pub(super) chunks: Vec<Value>,
    pub(super) len: usize,
}

/// Which of the heap's two tables.
#[derive(Clone, Copy)]
pub(super) enum Which {
    Globals,
    Symbols,
}

/// The tables area: its walkable end, and where each chunk starts, in
/// order (what `young::scan_code_cards` finds the objects on a card by).
pub(super) struct Area {
    pub(super) top: usize,
    pub(super) starts: Vec<usize>,
}

impl Default for Area {
    fn default() -> Area {
        Area { top: TABLES_BASE, starts: Vec::new() }
    }
}

/// Whether word `i` of the heap's memory is in the tables area.
#[inline(always)]
pub(super) fn in_tables(i: usize) -> bool {
    (TABLES_BASE..CODE_BASE).contains(&i)
}

impl Table {
    /// Where slot `i` is: its chunk, and the chunk's field.
    #[inline(always)]
    fn place(&self, i: usize) -> (Value, usize) {
        debug_assert!(i < self.len, "slot {i} of a table of {}", self.len);
        (self.chunks[i >> CHUNK_SHIFT], (i & (CHUNK - 1)) + 1)
    }
}

impl Heap {
    #[inline(always)]
    fn table(&self, t: Which) -> &Table {
        match t {
            Which::Globals => &self.globals,
            Which::Symbols => &self.symbols,
        }
    }

    #[inline(always)]
    fn table_mut(&mut self, t: Which) -> &mut Table {
        match t {
            Which::Globals => &mut self.globals,
            Which::Symbols => &mut self.symbols,
        }
    }

    /// Slot `i` of table `t`.
    #[inline(always)]
    pub(super) fn table_get(&self, t: Which, i: usize) -> Value {
        let (chunk, k) = self.table(t).place(i);
        self.bloblet_slot(chunk, k)
    }

    /// Slot `i` of table `t` made `v`, through the write barrier.
    #[inline(always)]
    pub(super) fn table_set(&mut self, t: Which, i: usize, v: Value) {
        let (chunk, k) = self.table(t).place(i);
        self.set_bloblet_slot(chunk, k, v);
    }

    /// `v` put at the end of table `t`: its index. A chunk made for it if
    /// the last is full: in the tables area if `image` (what an image
    /// brought), else in the heap.
    pub(super) fn table_push(&mut self, t: Which, v: Value, image: bool) -> usize {
        let i = self.table(t).len;
        if i == self.table(t).chunks.len() * CHUNK {
            let chunk = if image { self.area_chunk() } else { self.heap_chunk() };
            self.table_mut(t).chunks.push(chunk);
        }
        self.table_mut(t).len = i + 1;
        self.table_set(t, i, v);
        i
    }

    /// A chunk in the tables area, past the last: its fields the fixnum 0.
    fn area_chunk(&mut self) -> Value {
        let at = self.tables.top;
        let size = 1 + CHUNK;
        assert!(at + size <= CODE_BASE, "the tables area is full");
        self.tables.top = at + size;
        self.tables.starts.push(at);
        self.set_word(at, make_header(const { layout::kind("bloblet") }, CHUNK, 0));
        for i in 1..size {
            self.set_word(at + i, 0);
        }
        self.blob_v(at + size)
    }

    /// A chunk in the heap, as any object is made there; not in a region,
    /// which may end while the table holds it.
    fn heap_chunk(&mut self) -> Value {
        let region = self.regions.target.take();
        let chunk = self.make_bloblet(const { layout::kind("bloblet") }, CHUNK, 0, false);
        self.regions.target = region;
        chunk
    }

    /// Table `t`'s values, in order.
    pub(super) fn table_values(&self, t: Which) -> Vec<Value> {
        (0..self.table(t).len).map(|i| self.table_get(t, i)).collect()
    }

    /// Every card of the tables area marked in the first table: for a code
    /// collection, which scans all of it.
    pub(super) fn tables_all_dirty(&mut self) {
        let (lo, hi) = (TABLES_BASE, self.tables.top);
        for at in (lo..hi).step_by(1 << super::young::CARD_SHIFT) {
            self.mark_card(at);
        }
    }

    /// Words the tables area holds, and how many chunks: for reports and
    /// tests.
    pub fn tables_area_words(&self) -> (usize, usize) {
        (self.tables.top - TABLES_BASE, self.tables.starts.len())
    }

    /// The tables area checked: each chunk where its start says, one after
    /// the other.
    pub(super) fn verify_tables(&self) -> Result<(), String> {
        let mut at = TABLES_BASE;
        for &s in &self.tables.starts {
            if s != at {
                return Err(format!("a chunk of the tables area at {s}, not {at}"));
            }
            at += read_head(self.mem.words(), s).size();
        }
        if at != self.tables.top {
            return Err(format!("the tables area's chunks end at {at}, its top {}", self.tables.top));
        }
        Ok(())
    }
}
