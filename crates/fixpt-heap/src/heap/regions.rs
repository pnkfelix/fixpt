//! Regions: what a `letrena` or `letreap` allocates in (PLAN.md, "Regions
//! that end"). Each region is chunks of its own, past the two semispaces,
//! all given back when it ends. The two kinds differ in what the collector
//! does with them:
//! - an arena's chunks never move, and the collector traces them all as
//!   roots, so what they point to in the heap lives;
//! - a reap's are collected with the heap: what is reachable in it is
//!   copied into new chunks of its own, and the old chunks given back.
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
//! A reference to what a region held may linger after it ends, in a
//! frame's dead slot say, where the collector will find it. It never
//! follows one into an arena, so an arena's chunks are reused as soon as it
//! ends. It would follow one into a reap, so it follows only references into
//! a live reap's own chunks, and an ended reap's chunks are not reused until
//! a collection has found no reference into them: until then they are in
//! quarantine, their pages given back to the system. The reaps' chunks come
//! from an area of their own.
//!
//! Allocation goes to a region only while a primitive asks for it
//! (`Heap::in_region`); anything too big for a chunk, or once its area is
//! full, goes to the heap as it would have. Either is sound: the heap is
//! only slower to reclaim.

use super::{Heap, ARENA_BASE, ARENA_WORDS, REAP_BASE, REAP_WORDS};
use std::collections::{HashMap, HashSet};

/// Words in a chunk: 64 KiB.
pub(super) const CHUNK_WORDS: usize = 1 << 13;

/// The regions whose current chunk machine code can allocate in: those at
/// handles below this. A region at a handle above it (regions nested
/// deeper) allocates in the heap.
pub const REGION_SLOTS: usize = 256;

pub(super) struct Regions {
    /// The live regions, the newest last; a handle is a position here.
    /// Each has the chunks it has filled, and how far.
    pub(super) live: Vec<Vec<(usize, usize)>>,
    /// Whether each live region is a reap.
    pub(super) reap: Vec<bool>,
    /// For each handle below `REGION_SLOTS`, its current chunk: how far it
    /// is filled, and where it ends; both 0 when it has none. At an
    /// address that never changes, for machine code, which bumps the fill
    /// itself (`Heap::region_table_address`).
    pub(super) table: Box<[[usize; 2]; REGION_SLOTS]>,
    /// Arenas' chunks given back, to be reused; and the start of the
    /// arenas' area not yet used at all.
    free: Vec<usize>,
    fresh: usize,
    /// The start of the reaps' area not yet used, and each live reap's
    /// chunks, by where they start, with the reap's handle.
    pub(super) reap_fresh: usize,
    pub(super) owner: HashMap<usize, usize>,
    /// Reaps' chunks free to reuse; and those of reaps ended since, not to
    /// be reused until a collection finds no reference into them.
    pub(super) reap_free: Vec<usize>,
    pub(super) quarantine: HashSet<usize>,
    /// Words of chunks reaps have taken since the last collection: enough
    /// of them, and a safepoint collects.
    pub(super) reap_taken: usize,
    /// The region allocation goes to, while a primitive allocates in one.
    pub(super) target: Option<usize>,
    /// Words allocated in regions ended, and in chunks filled.
    pub(super) words: u64,
}

impl Regions {
    pub(super) fn new() -> Regions {
        Regions {
            live: Vec::new(),
            reap: Vec::new(),
            table: Box::new([[0; 2]; REGION_SLOTS]),
            free: Vec::new(),
            fresh: ARENA_BASE,
            reap_fresh: REAP_BASE,
            owner: HashMap::new(),
            reap_free: Vec::new(),
            quarantine: HashSet::new(),
            reap_taken: 0,
            target: None,
            words: 0,
        }
    }

    /// A chunk for region `h`, or none if its area is used up.
    fn chunk(&mut self, h: usize) -> Option<usize> {
        if self.reap[h] {
            let c = self.reap_chunk()?;
            self.owner.insert(c, h);
            return Some(c);
        }
        match self.free.pop() {
            Some(c) => Some(c),
            None if self.fresh + CHUNK_WORDS <= ARENA_BASE + ARENA_WORDS => {
                self.fresh += CHUNK_WORDS;
                Some(self.fresh - CHUNK_WORDS)
            }
            None => None,
        }
    }

    /// A reap's chunk: one free to reuse, or one never used.
    pub(super) fn reap_chunk(&mut self) -> Option<usize> {
        self.reap_taken += CHUNK_WORDS;
        if let Some(c) = self.reap_free.pop() {
            return Some(c);
        }
        if self.reap_fresh + CHUNK_WORDS > REAP_BASE + REAP_WORDS {
            return None;
        }
        self.reap_fresh += CHUNK_WORDS;
        Some(self.reap_fresh - CHUNK_WORDS)
    }

    /// `n` words in region `h`, or none, if it has no slot, they do not
    /// fit a chunk, or its area is used up.
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
        let chunk = self.chunk(h)?;
        if end != 0 {
            self.live[h].push((end - CHUNK_WORDS, fill));
            self.words += (fill - (end - CHUNK_WORDS)) as u64;
        }
        self.table[h] = [chunk + n, chunk + CHUNK_WORDS];
        Some(chunk)
    }

    /// Region `h`'s current chunk, as a range in use, if it has one.
    pub(super) fn current(&self, h: usize) -> Option<(usize, usize)> {
        let [fill, end] = *self.table.get(h)?;
        (end != 0).then(|| (end - CHUNK_WORDS, fill))
    }

    /// Region `h`'s words in use, chunk by chunk.
    pub(super) fn chunks_of(&self, h: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.live[h].iter().copied().chain(self.current(h))
    }

    /// The words in use in every live region, as ranges of the heap's
    /// memory: each a sequence of objects and pairs, as a semispace is.
    pub(super) fn ranges(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        (0..self.live.len()).flat_map(|h| self.chunks_of(h))
    }

    /// The same, for the arenas alone: what the collector traces as roots.
    pub(super) fn arena_ranges(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        (0..self.live.len()).filter(|h| !self.reap[*h]).flat_map(|h| self.chunks_of(h))
    }
}

impl Heap {
    /// A new arena, the newest region; its handle.
    pub fn region_enter(&mut self) -> usize {
        self.regions.live.push(Vec::new());
        self.regions.reap.push(false);
        self.regions.live.len() - 1
    }

    /// A new reap, the newest region; its handle.
    pub fn reap_enter(&mut self) -> usize {
        self.regions.live.push(Vec::new());
        self.regions.reap.push(true);
        self.regions.live.len() - 1
    }

    /// End region `h`, and any newer: an arena's chunks go back to be
    /// reused, a reap's pages to the system. Nothing may use what was
    /// allocated in them again.
    pub fn region_exit(&mut self, h: usize) {
        let h = h.min(self.regions.live.len());
        for k in (h..self.regions.live.len()).rev() {
            let r = &mut self.regions;
            let mut chunks: Vec<usize> = r.live.pop().expect("live").into_iter().map(|(start, _)| start).collect();
            if let Some((start, fill)) = r.current(k) {
                r.words += (fill - start) as u64;
                chunks.push(start);
                r.table[k] = [0, 0];
            }
            if r.reap.pop().expect("live") {
                for c in chunks {
                    self.regions.owner.remove(&c);
                    self.regions.quarantine.insert(c);
                    self.mem.release(c..c + CHUNK_WORDS);
                }
            } else {
                r.free.extend(chunks);
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

    /// Words region `h` holds now: after a reap is collected, only what
    /// was reachable.
    pub fn region_in_use(&self, h: usize) -> usize {
        self.regions.chunks_of(h).map(|(start, fill)| fill - start).sum()
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

    /// Whether word `i` of the heap's memory is in the regions' areas.
    pub(super) fn in_region_area(i: usize) -> bool {
        (ARENA_BASE..REAP_BASE + REAP_WORDS).contains(&i)
    }
}
