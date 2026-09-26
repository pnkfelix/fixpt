//! Regions: what a `letrena` allocates in (PLAN.md, "Regions that end").
//! Each region is chunks of its own, from an area of the heap's memory past
//! the two semispaces; nothing in one moves, and the collector traces them
//! all as roots, so what they point to in the heap lives. A region's chunks
//! go back to be reused when it ends, all at once.
//!
//! Chunks, not one stack of words with a mark per region: a region may be
//! allocated in while a newer one is live (a closure over an older region's
//! allocation, called in a newer one's body), and a stack would free that
//! allocation when the newer one ended. Regions themselves do end newest
//! first, since a body ends before the one around it and cannot be resumed
//! once ended (the checker allows no `comefrom` in it); so a handle is a
//! position in a stack of live regions, and ending one ends any newer that
//! an escape left behind.
//!
//! Allocation goes to a region only while a primitive asks for it
//! (`Heap::in_region`); anything too big for a chunk, or once the area is
//! full, goes to the heap as it would have. Either is sound: the heap is
//! only slower to reclaim.

use super::{Heap, ARENA_BASE, ARENA_WORDS};

/// Words in a chunk: 64 KiB.
pub(super) const CHUNK_WORDS: usize = 1 << 13;

#[derive(Default)]
pub(super) struct Regions {
    /// The live regions, the newest last; a handle is a position here.
    live: Vec<Vec<(usize, usize)>>,
    /// Chunks given back, to be reused; and the start of the area not yet
    /// used at all.
    free: Vec<usize>,
    fresh: usize,
    /// The region allocation goes to, while a primitive allocates in one.
    pub(super) target: Option<usize>,
    /// Words allocated in regions, ever.
    pub(super) words: u64,
}

impl Regions {
    pub(super) fn new() -> Regions {
        Regions { fresh: ARENA_BASE, ..Regions::default() }
    }

    /// `n` words in region `h`, or none, if they do not fit a chunk or the
    /// area is used up.
    pub(super) fn bump(&mut self, h: usize, n: usize) -> Option<usize> {
        let chunks = self.live.get_mut(h)?;
        if let Some((start, fill)) = chunks.last_mut()
            && *fill + n <= *start + CHUNK_WORDS
        {
            let at = *fill;
            *fill += n;
            self.words += n as u64;
            return Some(at);
        }
        if n > CHUNK_WORDS {
            return None;
        }
        let chunk = match self.free.pop() {
            Some(c) => c,
            None if self.fresh + CHUNK_WORDS <= ARENA_BASE + ARENA_WORDS => {
                self.fresh += CHUNK_WORDS;
                self.fresh - CHUNK_WORDS
            }
            None => return None,
        };
        chunks.push((chunk, chunk + n));
        self.words += n as u64;
        Some(chunk)
    }

    /// The words in use in every live region, as ranges of the heap's
    /// memory: each a sequence of objects and pairs, as a semispace is.
    pub(super) fn ranges(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.live.iter().flatten().copied()
    }
}

impl Heap {
    /// A new region, the newest; its handle.
    pub fn region_enter(&mut self) -> usize {
        self.regions.live.push(Vec::new());
        self.regions.live.len() - 1
    }

    /// End region `h`, and any newer: their chunks go back to be reused.
    /// Nothing may use what was allocated in them again.
    pub fn region_exit(&mut self, h: usize) {
        let r = &mut self.regions;
        let h = h.min(r.live.len());
        for chunks in r.live.drain(h..) {
            r.free.extend(chunks.iter().map(|(start, _)| *start));
        }
    }

    /// `f`, with what it allocates in region `h`, where that fits: for a
    /// primitive that allocates and calls nothing back, so that only its
    /// own allocation goes there. A region no longer live gives the heap.
    pub fn in_region<T>(&mut self, h: usize, f: impl FnOnce(&mut Heap) -> T) -> T {
        let outer = self.regions.target.replace(h);
        let v = f(self);
        self.regions.target = outer;
        v
    }

    /// How many regions are live.
    pub fn live_regions(&self) -> usize {
        self.regions.live.len()
    }

    /// Words allocated in regions since the heap was made.
    pub fn region_words(&self) -> u64 {
        self.regions.words
    }

    /// Whether word `i` of the heap's memory is in the regions' area.
    pub(super) fn in_region_area(i: usize) -> bool {
        (ARENA_BASE..ARENA_BASE + ARENA_WORDS).contains(&i)
    }
}
