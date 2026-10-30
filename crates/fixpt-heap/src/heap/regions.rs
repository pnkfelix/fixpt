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
//! allocation when the newer one ended. Within one task, regions end newest
//! first, since a body ends before the one around it and cannot be resumed
//! once ended (the checker allows no `comefrom` in it); so each task has a
//! stack of the regions it entered, and ending one ends any newer of its
//! own that an escape left behind.
//!
//! Tasks (FX-26's processes and `par`'s branches; `docs/fx26.md`,
//! "Processes") interleave, so the order holds only within each: task A
//! enters `r1` and waits, B enters `r2`, A leaves `r1`, and `r2` must not
//! end. So a handle is not a position but a slot of its own, numbered from
//! the lowest free, and each task's stack holds the slots it entered. The
//! heap has one task current, 0 until another is made current; entering,
//! leaving and counting regions are the current task's (task Q1 of
//! `docs/research/actors-and-distribution.md`).
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
//! (`Heap::in_region`), and then always there. An object of more words than
//! a chunk is a large object, in a run of chunks of its own, on its
//! region's list of them (`Regions::large`): an arena's never move, as its
//! chunks do not; a reap's are not copied either, but marked where they
//! are when a collection reaches them and scanned there, and those not
//! reached given back. A run given back is kept, whole, for the next large
//! object it fits; a chunk too. A region at a handle with no slot in the
//! table machine code reads (`REGION_SLOTS`) has its current chunk kept
//! where only the Rust side sees it, and machine code calls in for it.
//! An area used up is the heap being full: an error, not a fallback.

use super::{Heap, ARENA_BASE, ARENA_WORDS, REAP_BASE, REAP_WORDS};
use std::collections::{HashMap, HashSet};

/// Words in a chunk: 64 KiB.
pub(super) const CHUNK_WORDS: usize = 1 << 13;

/// The regions whose current chunk machine code can allocate in: those at
/// handles below this. A region at a handle above it (regions nested
/// deeper) is allocated in by calling in (`Regions::spill`).
pub const REGION_SLOTS: usize = 256;

pub(super) struct Regions {
    /// The regions, by handle: each has the chunks it has filled, and how
    /// far; none, if the slot is free.
    pub(super) live: Vec<Vec<(usize, usize)>>,
    /// Each region's large objects, by handle: each of more words than a
    /// chunk, in a run of chunks of its own, as `(start, end)`.
    pub(super) large: Vec<Vec<(usize, usize)>>,
    /// Whether each region is a reap; whether its slot is in use.
    pub(super) reap: Vec<bool>,
    pub(super) alive: Vec<bool>,
    /// Each task's regions, the newest last; none for a task ended (`None`).
    stacks: Vec<Option<Vec<usize>>>,
    /// Each task's state as the scheduler preempts it
    /// (`fixpt_runtime::sched::preempt_due`): how many things that must not
    /// be preempted it is in (its `preempt`, called at a poll, until that
    /// call has returned; its wait, from the capture until resumed), and,
    /// in the top bit, a grace: the next time slice the task's own, whole,
    /// before it is preempted again.
    quiet: Vec<u8>,
    /// The task current.
    task: usize,
    /// For each handle below `REGION_SLOTS`, its current chunk: how far it
    /// is filled, and where it ends; both 0 when it has none. At an
    /// address that never changes, for machine code, which bumps the fill
    /// itself (`Heap::region_table_address`).
    pub(super) table: Box<[[usize; 2]; REGION_SLOTS]>,
    /// The same for each handle from `REGION_SLOTS` on, which machine code
    /// does not see.
    spill: Vec<[usize; 2]>,
    /// Arenas' chunks given back, to be reused, and runs of chunks a large
    /// object held, `(start, chunks)`; and the start of the arenas' area
    /// not yet used at all.
    free: Vec<usize>,
    large_free: Vec<(usize, usize)>,
    fresh: usize,
    /// The start of the reaps' area not yet used, and each live reap's
    /// chunks, by where they start, with the reap's handle.
    pub(super) reap_fresh: usize,
    pub(super) owner: HashMap<usize, usize>,
    /// Each chunk of a live reap's large objects, with where its run
    /// starts.
    pub(super) large_of: HashMap<usize, usize>,
    /// Reaps' chunks free to reuse, and runs of them a large object held;
    /// and those of reaps ended since, not to be reused until a collection
    /// finds no reference into them: each chunk with where its run starts
    /// (itself, for a chunk alone), and each run's length in chunks.
    pub(super) reap_free: Vec<usize>,
    reap_large_free: Vec<(usize, usize)>,
    pub(super) quarantine: HashMap<usize, usize>,
    quarantine_runs: HashMap<usize, usize>,
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
            large: Vec::new(),
            reap: Vec::new(),
            alive: Vec::new(),
            stacks: vec![Some(Vec::new())],
            quiet: vec![0],
            task: 0,
            table: Box::new([[0; 2]; REGION_SLOTS]),
            spill: Vec::new(),
            free: Vec::new(),
            large_free: Vec::new(),
            fresh: ARENA_BASE,
            reap_fresh: REAP_BASE,
            owner: HashMap::new(),
            large_of: HashMap::new(),
            reap_free: Vec::new(),
            reap_large_free: Vec::new(),
            quarantine: HashMap::new(),
            quarantine_runs: HashMap::new(),
            reap_taken: 0,
            target: None,
            words: 0,
        }
    }

    /// Region `h`'s current chunk, how far it is filled and where it ends:
    /// in the table machine code reads, or past it.
    pub(super) fn slot(&self, h: usize) -> [usize; 2] {
        match h.checked_sub(REGION_SLOTS) {
            None => self.table[h],
            Some(k) => self.spill.get(k).copied().unwrap_or([0, 0]),
        }
    }

    pub(super) fn set_slot(&mut self, h: usize, s: [usize; 2]) {
        match h.checked_sub(REGION_SLOTS) {
            None => self.table[h] = s,
            Some(k) => {
                if self.spill.len() <= k {
                    self.spill.resize(k + 1, [0, 0]);
                }
                self.spill[k] = s;
            }
        }
    }

    /// A chunk for region `h`.
    fn chunk(&mut self, h: usize) -> usize {
        if self.reap[h] {
            let c = self.reap_chunk().unwrap_or_else(|| panic!("the reaps' area is full: {REAP_WORDS} words"));
            self.owner.insert(c, h);
            return c;
        }
        match self.free.pop() {
            Some(c) => c,
            None => Self::run_in(&mut self.large_free, &mut self.fresh, ARENA_BASE + ARENA_WORDS, 1)
                .unwrap_or_else(|| panic!("the arenas' area is full: {ARENA_WORDS} words")),
        }
    }

    /// A reap's chunk: one free to reuse, or one never used; none if its
    /// area is used up.
    pub(super) fn reap_chunk(&mut self) -> Option<usize> {
        self.reap_taken += CHUNK_WORDS;
        if let Some(c) = self.reap_free.pop() {
            return Some(c);
        }
        Self::run_in(&mut self.reap_large_free, &mut self.reap_fresh, REAP_BASE + REAP_WORDS, 1)
    }

    /// A run of `k` chunks: the first of `runs` it fits, the rest of that
    /// left there, or from `fresh`, short of `limit`.
    fn run_in(runs: &mut Vec<(usize, usize)>, fresh: &mut usize, limit: usize, k: usize) -> Option<usize> {
        if let Some(i) = runs.iter().position(|&(_, n)| n >= k) {
            let (start, n) = runs[i];
            if n == k {
                runs.swap_remove(i);
            } else {
                runs[i] = (start + k * CHUNK_WORDS, n - k);
            }
            return Some(start);
        }
        if *fresh + k * CHUNK_WORDS > limit {
            return None;
        }
        *fresh += k * CHUNK_WORDS;
        Some(*fresh - k * CHUNK_WORDS)
    }

    /// `n` words in region `h`; none if it is not live (the heap's, then).
    pub(super) fn bump(&mut self, h: usize, n: usize) -> Option<usize> {
        if h >= self.live.len() || !self.alive[h] {
            return None;
        }
        if n > CHUNK_WORDS {
            return Some(self.large_object(h, n));
        }
        let [fill, end] = self.slot(h);
        if fill + n <= end {
            self.set_slot(h, [fill + n, end]);
            return Some(fill);
        }
        let chunk = self.chunk(h);
        if end != 0 {
            self.live[h].push((end - CHUNK_WORDS, fill));
            self.words += (fill - (end - CHUNK_WORDS)) as u64;
        }
        self.set_slot(h, [chunk + n, chunk + CHUNK_WORDS]);
        Some(chunk)
    }

    /// A large object of `n` words in region `h`: a run of chunks of its
    /// own, on the region's list.
    fn large_object(&mut self, h: usize, n: usize) -> usize {
        let k = n.div_ceil(CHUNK_WORDS);
        let start = if self.reap[h] {
            let start = Self::run_in(&mut self.reap_large_free, &mut self.reap_fresh, REAP_BASE + REAP_WORDS, k)
                .unwrap_or_else(|| panic!("the reaps' area is full: {REAP_WORDS} words"));
            self.reap_taken += k * CHUNK_WORDS;
            for i in 0..k {
                self.large_of.insert(start + i * CHUNK_WORDS, start);
            }
            start
        } else {
            Self::run_in(&mut self.large_free, &mut self.fresh, ARENA_BASE + ARENA_WORDS, k)
                .unwrap_or_else(|| panic!("the arenas' area is full: {ARENA_WORDS} words"))
        };
        self.large[h].push((start, start + n));
        self.words += n as u64;
        start
    }

    /// Run `start`, of `k` chunks, a reap's, given back: free to reuse.
    pub(super) fn reap_run_free(&mut self, start: usize, k: usize) {
        if k == 1 {
            self.reap_free.push(start);
        } else {
            self.reap_large_free.push((start, k));
        }
    }

    /// The ended reaps' runs a collection found a reference into
    /// (`marked`, by where they start) kept from reuse; the rest free.
    pub(super) fn quarantine_ends(&mut self, marked: &HashSet<usize>) {
        let runs = std::mem::take(&mut self.quarantine_runs);
        for (start, k) in runs {
            if marked.contains(&start) {
                self.quarantine_runs.insert(start, k);
            } else {
                for i in 0..k {
                    self.quarantine.remove(&(start + i * CHUNK_WORDS));
                }
                self.reap_run_free(start, k);
            }
        }
    }

    /// Region `h`'s current chunk, as a range in use, if it has one.
    pub(super) fn current(&self, h: usize) -> Option<(usize, usize)> {
        let [fill, end] = self.slot(h);
        (end != 0).then(|| (end - CHUNK_WORDS, fill))
    }

    /// Region `h`'s words in use, chunk by chunk; its large objects not.
    pub(super) fn chunks_of(&self, h: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.live[h].iter().copied().chain(self.current(h))
    }

    /// Region `h`'s words in use: its chunks, and its large objects.
    fn held(&self, h: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.chunks_of(h).chain(self.large[h].iter().copied())
    }

    /// The words in use in every live region, as ranges of the heap's
    /// memory: each a sequence of objects and pairs, as a semispace is.
    pub(super) fn ranges(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        (0..self.live.len()).filter(|h| self.alive[*h]).flat_map(|h| self.held(h))
    }

    /// The same, for the arenas alone: what the collector traces as roots.
    pub(super) fn arena_ranges(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        (0..self.live.len()).filter(|h| self.alive[*h] && !self.reap[*h]).flat_map(|h| self.held(h))
    }

    /// A slot for a new region, the lowest free, as a reap or not; on the
    /// current task's stack.
    fn enter(&mut self, reap: bool) -> usize {
        let h = match self.alive.iter().position(|a| !a) {
            Some(h) => h,
            None => {
                self.live.push(Vec::new());
                self.large.push(Vec::new());
                self.reap.push(false);
                self.alive.push(false);
                self.live.len() - 1
            }
        };
        self.alive[h] = true;
        self.reap[h] = reap;
        self.stacks[self.task].as_mut().expect("the current task is live").push(h);
        h
    }

    /// The current task's stack.
    fn stack(&self) -> &Vec<usize> {
        self.stacks[self.task].as_ref().expect("the current task is live")
    }
}

impl Heap {
    /// A new arena, the current task's newest region; its handle.
    pub fn region_enter(&mut self) -> usize {
        self.regions.enter(false)
    }

    /// A new reap, the current task's newest region; its handle.
    pub fn reap_enter(&mut self) -> usize {
        self.regions.enter(true)
    }

    /// End region `h`, and any newer of the current task's: an arena's
    /// chunks go back to be reused, a reap's pages to the system. Nothing
    /// may use what was allocated in them again. A handle not on the
    /// current task's stack (ended already, by an escape) ends nothing.
    pub fn region_exit(&mut self, h: usize) {
        if let Some(depth) = self.regions.stack().iter().position(|&k| k == h) {
            self.regions_exit_to(depth);
        }
    }

    /// End the current task's regions past the first `depth`, newest
    /// first: what an abort to a prompt does, which noted `depth`.
    pub fn regions_exit_to(&mut self, depth: usize) {
        while self.regions.stack().len() > depth {
            let task = self.regions.task;
            let h = self.regions.stacks[task].as_mut().expect("live").pop().expect("deeper");
            self.region_end(h);
        }
    }

    /// Region `h`'s slot given back, and its chunks, and its large
    /// objects' runs.
    fn region_end(&mut self, h: usize) {
        let r = &mut self.regions;
        let mut chunks: Vec<usize> = std::mem::take(&mut r.live[h]).into_iter().map(|(start, _)| start).collect();
        if let Some((start, fill)) = r.current(h) {
            r.words += (fill - start) as u64;
            chunks.push(start);
            r.set_slot(h, [0, 0]);
        }
        let runs: Vec<(usize, usize)> = std::mem::take(&mut r.large[h]).into_iter().map(|(start, end)| (start, (end - start).div_ceil(CHUNK_WORDS))).collect();
        r.alive[h] = false;
        let reap = std::mem::replace(&mut r.reap[h], false);
        // A run's pages go back to the system: there may be many.
        for &(start, k) in &runs {
            self.mem.release(start..start + k * CHUNK_WORDS);
        }
        let r = &mut self.regions;
        if reap {
            for c in chunks {
                r.owner.remove(&c);
                r.quarantine.insert(c, c);
                r.quarantine_runs.insert(c, 1);
                self.mem.release(c..c + CHUNK_WORDS);
            }
            for (start, k) in runs {
                for i in 0..k {
                    r.large_of.remove(&(start + i * CHUNK_WORDS));
                    r.quarantine.insert(start + i * CHUNK_WORDS, start);
                }
                r.quarantine_runs.insert(start, k);
            }
        } else {
            r.free.extend(chunks);
            r.large_free.extend(runs);
        }
    }

    /// A new task, with no region: its number. Not current until made so.
    pub fn task_new(&mut self) -> usize {
        let s = &mut self.regions.stacks;
        let t = match s.iter().position(|t| t.is_none()) {
            Some(t) => {
                s[t] = Some(Vec::new());
                t
            }
            None => {
                s.push(Some(Vec::new()));
                s.len() - 1
            }
        };
        let q = &mut self.regions.quiet;
        q.resize(q.len().max(t + 1), 0);
        q[t] = 0;
        t
    }

    fn quiet_mut(&mut self) -> &mut u8 {
        let t = self.regions.task;
        let q = &mut self.regions.quiet;
        q.resize(q.len().max(t + 1), 0);
        &mut q[t]
    }

    /// Whether the current task is in something that must not be preempted
    /// (`Regions::quiet`).
    pub fn task_quiet(&self) -> bool {
        self.regions.quiet.get(self.regions.task).is_some_and(|q| q & 0x7f != 0)
    }

    /// The current task into something that must not be preempted.
    pub fn quiet_enter(&mut self) {
        let q = self.quiet_mut();
        *q = (*q & 0x80) | ((*q & 0x7f) + 1).min(0x7f);
    }

    /// Out of it; out of the last, a grace begins.
    pub fn quiet_leave(&mut self) {
        let q = self.quiet_mut();
        let d = (*q & 0x7f).saturating_sub(1);
        *q = d | if d == 0 { 0x80 } else { *q & 0x80 };
    }

    /// Whether the current task has a grace, which ends here.
    pub fn take_grace(&mut self) -> bool {
        let q = self.quiet_mut();
        let g = *q & 0x80 != 0;
        *q &= 0x7f;
        g
    }

    /// Make task `t` current; the task that was.
    pub fn task_switch(&mut self, t: usize) -> usize {
        assert!(self.regions.stacks.get(t).is_some_and(|s| s.is_some()), "task {t} is not live");
        std::mem::replace(&mut self.regions.task, t)
    }

    /// Whether task `t` is live.
    pub fn task_live(&self, t: usize) -> bool {
        self.regions.stacks.get(t).is_some_and(|s| s.is_some())
    }

    /// The task current.
    pub fn task_current(&self) -> usize {
        self.regions.task
    }

    /// End task `t`, not the first, and every region it has left. If it is
    /// current, the first task becomes so.
    pub fn task_end(&mut self, t: usize) {
        assert!(t != 0, "the first task never ends");
        if self.regions.stacks.get(t).is_none_or(|s| s.is_none()) {
            return;
        }
        let was = self.task_switch(t);
        self.regions_exit_to(0);
        self.regions.stacks[t] = None;
        self.regions.task = if was == t { 0 } else { was };
    }

    /// Every task but the first ended, and it made current: after a run
    /// that failed, which leaves no task to resume.
    pub fn tasks_reset(&mut self) {
        for t in 1..self.regions.stacks.len() {
            self.task_end(t);
        }
        self.regions.task = 0;
        self.regions.quiet.iter_mut().for_each(|q| *q = 0);
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

    /// How many regions the current task has live.
    pub fn live_regions(&self) -> usize {
        self.regions.stack().len()
    }

    /// How many regions are live, of every task.
    pub fn all_live_regions(&self) -> usize {
        self.regions.alive.iter().filter(|a| **a).count()
    }

    /// Words region `h` holds now, its large objects too: after a reap is
    /// collected, only what was reachable.
    pub fn region_in_use(&self, h: usize) -> usize {
        self.regions.held(h).map(|(start, fill)| fill - start).sum()
    }

    /// Words allocated in regions since the heap was made.
    pub fn region_words(&self) -> u64 {
        let r = &self.regions;
        r.words + (0..r.live.len()).filter(|h| r.alive[*h]).filter_map(|h| r.current(h)).map(|(start, fill)| (fill - start) as u64).sum::<u64>()
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
