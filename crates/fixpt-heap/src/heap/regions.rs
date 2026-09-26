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

/// The regions whose current chunk machine code can allocate in: those at
/// handles below this. A region at a handle above it (regions nested
/// deeper) allocates in the heap.
pub const REGION_SLOTS: usize = 256;

pub(super) struct Regions {
    /// The live regions, the newest last; a handle is a position here.
    /// Each has the chunks it has filled, and how far.
    live: Vec<Vec<(usize, usize)>>,
    /// For each handle below `REGION_SLOTS`, its current chunk: how far it
    /// is filled, and where it ends; both 0 when it has none. At an
    /// address that never changes, for machine code, which bumps the fill
    /// itself (`Heap::region_table_address`).
    table: Box<[[usize; 2]; REGION_SLOTS]>,
    /// Chunks given back, to be reused; and the start of the area not yet
    /// used at all.
    free: Vec<usize>,
    fresh: usize,
    /// The region allocation goes to, while a primitive allocates in one.
    pub(super) target: Option<usize>,
    /// Words allocated in regions ended, and in chunks filled.
    words: u64,
}

impl Regions {
    pub(super) fn new() -> Regions {
        Regions {
            live: Vec::new(),
            table: Box::new([[0; 2]; REGION_SLOTS]),
            free: Vec::new(),
            fresh: ARENA_BASE,
            target: None,
            words: 0,
        }
    }

    /// `n` words in region `h`, or none, if it has no slot, they do not
    /// fit a chunk, or the area is used up.
    pub(super) fn bump(&mut self, h: usize, n: usize) -> Option<usize> {
        if h >= self.live.len() || h >= REGION_SLOTS {
            return None;
        }
        let [fill, end] = self.table[h];
        if fill + n <= end {
            self.table[h][0] = fill + n;
            return Some(fill);
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
        if end != 0 {
            self.live[h].push((end - CHUNK_WORDS, fill));
            self.words += (fill - (end - CHUNK_WORDS)) as u64;
        }
        self.table[h] = [chunk + n, chunk + CHUNK_WORDS];
        Some(chunk)
    }

    /// Region `h`'s current chunk, as a range in use, if it has one.
    fn current(&self, h: usize) -> Option<(usize, usize)> {
        let [fill, end] = *self.table.get(h)?;
        (end != 0).then(|| (end - CHUNK_WORDS, fill))
    }

    /// The words in use in every live region, as ranges of the heap's
    /// memory: each a sequence of objects and pairs, as a semispace is.
    pub(super) fn ranges(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.live.iter().enumerate().flat_map(|(h, filled)| filled.iter().copied().chain(self.current(h)))
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
        for k in (h..r.live.len()).rev() {
            if let Some((start, fill)) = r.current(k) {
                r.words += (fill - start) as u64;
                r.free.push(start);
                r.table[k] = [0, 0];
            }
            for (start, _) in r.live.pop().expect("live") {
                r.free.push(start);
            }
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
        let r = &self.regions;
        r.words + (0..r.live.len()).filter_map(|h| r.current(h)).map(|(start, fill)| (fill - start) as u64).sum::<u64>()
    }

    /// Where the regions' table of current chunks is, for machine code
    /// (`regions::REGION_SLOTS` of `[fill, end]`, in words from the base):
    /// it may bump a region's fill up to its end, and must call in
    /// otherwise. The address holds for the heap's life.
    pub fn region_table_address(&mut self) -> *mut usize {
        self.regions.table.as_mut_ptr() as *mut usize
    }

    /// Whether word `i` of the heap's memory is in the regions' area.
    pub(super) fn in_region_area(i: usize) -> bool {
        (ARENA_BASE..ARENA_BASE + ARENA_WORDS).contains(&i)
    }
}
