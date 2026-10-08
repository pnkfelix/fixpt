//! The nursery, and what lets it be collected alone
//! (`docs/research/generational-gc.md`): the card table, the old space's
//! crossing map, and minor collections.
//!
//! A generational heap allocates everything in the nursery. A minor
//! collection copies what is live there to the end of the old semispace
//! (the active one), Cheney's way, and empties it: everything live is
//! promoted at once. Its roots are the usual ones, what the regions and the
//! code area hold (scanned whole), and the old space's dirty cards: a store
//! that puts a young reference into the old space marks the card of the
//! word written (`Heap::set_slot`, and each machine's own stores).

use super::{Copier, Heap, MAX_SEMI_WORDS, MEM_WORDS, NURSERY_BASE, NURSERY_MAX, read_head};
use crate::layout;
use crate::value::{Value, is_extension, is_header};
use std::collections::{HashMap, HashSet};

/// A card is 64 words, 512 bytes: word `i` of the heap's memory is on card
/// `i >> CARD_SHIFT`.
pub(super) const CARD_SHIFT: usize = 6;
const CARD_WORDS: usize = 1 << CARD_SHIFT;
/// Cards over the whole of the heap's memory (the table's bytes), and over
/// the semispaces (the crossing map's).
pub(super) const CARDS: usize = MEM_WORDS >> CARD_SHIFT;
pub(super) const SEMI_CARDS: usize = (2 * MAX_SEMI_WORDS) >> CARD_SHIFT;

/// Whether word `i` of the heap's memory is the nursery's.
#[inline(always)]
pub(super) fn is_young(i: usize) -> bool {
    (NURSERY_BASE..NURSERY_BASE + NURSERY_MAX).contains(&i)
}

/// Byte `i` of a table kept in words, little-endian, as machine code's
/// `strb` sees it.
#[inline(always)]
fn byte(t: &fixpt_memmgmt::Words, i: usize) -> u8 {
    (t.words()[i >> 3] >> (8 * (i & 7))) as u8
}

#[inline(always)]
fn set_byte(t: &mut fixpt_memmgmt::Words, i: usize, b: u8) {
    let w = &mut t.words_mut()[i >> 3];
    let shift = 8 * (i & 7);
    *w = (*w & !(0xff << shift)) | ((b as u64) << shift);
}

impl Heap {
    /// The card of word `rel` marked: a young reference may be there.
    #[inline(always)]
    pub(super) fn mark_card(&mut self, rel: usize) {
        set_byte(&mut self.cards, rel >> CARD_SHIFT, 1);
    }

    /// Every card from word `lo` to word `hi` clean.
    pub(super) fn clear_cards(&mut self, lo: usize, hi: usize) {
        for c in lo >> CARD_SHIFT..hi.div_ceil(CARD_WORDS) {
            set_byte(&mut self.cards, c, 0);
        }
    }

    /// For machine code that marks cards itself: the card table's address,
    /// biased so that the byte for the word at address `a` is at this plus
    /// `a >> 9` (`mem` starts on a page, so on a card).
    pub fn card_table_address(&self) -> usize {
        let table = self.cards.words().as_ptr() as usize;
        table.wrapping_sub((self.base << 3) >> (CARD_SHIFT + 3))
    }

    /// Whether the heap has a nursery.
    pub fn is_generational(&self) -> bool {
        self.generational
    }

    /// A nursery of `words` words from now on, or none for 0; not while
    /// machine code runs, which reads where allocation goes when it starts.
    /// Turned off, the nursery must be empty (collected).
    pub fn set_nursery(&mut self, words: usize) {
        assert!(words > 0 || self.nursery_top == NURSERY_BASE, "the nursery is collected before it is turned off");
        self.generational = words > 0;
        self.nursery_words = words.max(1024);
    }

    /// Words in the nursery now.
    pub fn nursery_used(&self) -> usize {
        self.nursery_top - NURSERY_BASE
    }

    /// The crossing map for the words from `lo` to `hi`, a sequence of
    /// objects and pairs, walked: for a heap loaded from an image.
    pub(super) fn cross_all(&mut self, lo: usize, hi: usize) {
        let mut last = usize::MAX;
        let mut at = lo;
        while at < hi {
            let w = self.word(at);
            let n = if is_header(w) { read_head(self.mem.words(), at + is_extension(w) as usize).size() } else { 2 };
            cross(&mut self.crossing, &mut last, at, n);
            at += n;
        }
    }

    /// Collect the nursery alone: everything live in it copied to the end
    /// of the old space, which is then scanned; the nursery emptied, and
    /// every card clean. The roots are `extra_roots` and the heap's own, the
    /// regions' and code area's objects, and the old space's dirty cards.
    pub(super) fn collect_minor(&mut self, extra_roots: &mut [&mut [Value]]) {
        let started = std::time::Instant::now();
        let before = self.used();
        self.peak_words = self.peak_words.max(before as u64);
        if self.verify_barrier {
            self.verify_remembered().unwrap_or_else(|e| panic!("the write barrier missed a store: {e}"));
        }
        let young = self.nursery_top - NURSERY_BASE;
        self.words_allocated += young as u64;
        let (lo, old_top) = (self.active, self.top);
        let regions: Vec<(usize, usize)> = self.regions.ranges().collect();
        let code = (super::CODE_BASE, self.code.top);
        // The first object promoted starts the card of the old top's last
        // word only if none starts there already.
        let last_card = match old_top > lo {
            true if (1..=CARD_WORDS).contains(&(byte(&self.crossing, (old_top - 1) >> CARD_SHIFT) as usize)) => (old_top - 1) >> CARD_SHIFT,
            _ => usize::MAX,
        };
        let mem = self.mem.words_mut();
        let mut c = Copier {
            base: self.base,
            from: NURSERY_BASE,
            to: old_top,
            free: 0,
            owner: HashMap::new(),
            new: Vec::new(),
            marked: HashSet::new(),
            code_marks: HashSet::new(),
            code_gray: Vec::new(),
            weak_pairs: Vec::new(),
            regions: &mut self.regions,
            minor: true,
            crossing: &mut self.crossing,
            last_card,
        };
        macro_rules! fwd {
            ($v:expr) => {{
                let v = $v;
                if v.is_ref() { Self::copy_out(mem, &mut c, v) } else { v }
            }};
        }
        for r in self.roots.iter_mut().chain(self.globals.iter_mut()).chain(self.symbols.iter_mut()) {
            *r = fwd!(*r);
        }
        for slice in extra_roots.iter_mut() {
            for v in slice.iter_mut() {
                *v = fwd!(*v);
            }
        }
        // What the regions and the code area hold: scanned whole, since
        // their stores are not remembered.
        for (from, to) in regions.into_iter().chain(std::iter::once(code)) {
            let mut at = from;
            while at < to {
                at += Self::scan_one(mem, at, &mut c);
            }
        }
        // The old space's dirty cards, each cleaned as it is scanned; the
        // table read a word (eight cards) at a time, a clean word skipped
        // whole, so that a large old space with few dirty cards costs little.
        let (first, end) = (lo >> CARD_SHIFT, old_top.div_ceil(CARD_WORDS));
        let mut card = first;
        while card < end {
            if card % 8 == 0 && card + 8 <= end && self.cards.words()[card >> 3] == 0 {
                card += 8;
                continue;
            }
            let this = card;
            card += 1;
            let card = this;
            if byte(&self.cards, card) == 0 {
                continue;
            }
            set_byte(&mut self.cards, card, 0);
            let (clo, chi) = (card << CARD_SHIFT, ((card + 1) << CARD_SHIFT).min(old_top));
            // The object that covers the card's first word: from the last
            // object that starts at or before it, found by the crossing map.
            // (One that starts past the old top was promoted just now.)
            let mut k = card;
            let mut at = loop {
                let b = byte(c.crossing, k) as usize;
                if (1..=CARD_WORDS).contains(&b) && (k << CARD_SHIFT) + b - 1 <= clo {
                    break (k << CARD_SHIFT) + b - 1;
                }
                if k == lo >> CARD_SHIFT {
                    break lo;
                }
                k -= if b > CARD_WORDS { 1 << (b - CARD_WORDS - 1) } else { 1 };
                k = k.max(lo >> CARD_SHIFT);
            };
            while at < chi {
                let w = mem[at];
                let (fields, n) = if is_header(w) {
                    let main = at + is_extension(w) as usize;
                    let head = read_head(mem, main);
                    // A weak pair's car is not traced (`scan_one`).
                    let weak = head.kind == layout::kind("weak-pair");
                    if weak {
                        c.weak_pairs.push(main);
                    }
                    (main + 1 + weak as usize..main + 1 + head.fields, head.size())
                } else {
                    (at..at + 2, 2)
                };
                for f in fields.start.max(clo)..fields.end.min(chi) {
                    let v = Value(mem[f]);
                    if v.is_ref() {
                        mem[f] = Self::copy_out(mem, &mut c, v).raw();
                    }
                }
                at += n;
            }
        }
        // What was promoted, scanned until nothing more is.
        let mut scan = 0;
        while scan < c.free {
            scan += Self::scan_one(mem, old_top + scan, &mut c);
        }
        super::update_weak(mem, self.base, &mut self.weak, NURSERY_BASE, true);
        super::update_weak_pairs(mem, self.base, &c.weak_pairs, NURSERY_BASE, true);
        let free = c.free;
        self.top = old_top + free;
        assert!(self.top - self.active <= MAX_SEMI_WORDS, "the old space is full");
        if self.top - self.active > self.semi {
            self.grow(self.top - self.active);
        }
        self.nursery_top = NURSERY_BASE;
        self.minor_count += 1;
        self.words_copied += free as u64;
        self.minor_words_copied += free as u64;
        self.top_after_gc = self.top;
        let nanos = started.elapsed().as_nanos() as u64;
        self.gc_nanos += nanos;
        self.minor_nanos += nanos;
        self.max_minor_nanos = self.max_minor_nanos.max(nanos);
        self.traced("minor", self.minor_count, nanos, free, before);
    }

    /// That every young reference in the old space is on a dirty card: what
    /// the write barrier promises a minor collection. It walks the whole old
    /// space; for tests.
    pub fn verify_remembered(&self) -> Result<(), String> {
        let mut at = self.active;
        while at < self.top {
            let w = self.word(at);
            let (fields, n) = if is_header(w) {
                let main = at + is_extension(w) as usize;
                let head = read_head(self.mem.words(), main);
                (main + 1..main + 1 + head.fields, head.size())
            } else {
                (at..at + 2, 2)
            };
            for f in fields {
                let v = self.slot(f);
                if v.is_ref() && is_young(self.ix(v)) && byte(&self.cards, f >> CARD_SHIFT) == 0 {
                    return Err(format!("word {f} holds a young {v:?}, and its card is clean"));
                }
            }
            at += n;
        }
        Ok(())
    }
}

impl Copier<'_> {
    /// An object of `n` words copied into the old space at `at`: the
    /// crossing map told.
    #[inline(always)]
    pub(super) fn crossed(&mut self, at: usize, n: usize) {
        cross(self.crossing, &mut self.last_card, at, n);
    }
}

/// The crossing map told of an object of `n` words at `at`, placed after
/// the one that started on card `last`: it starts its card if it is the
/// first there, and no object starts on the cards it covers after it.
///
/// A card's byte: 0, nothing known (before any object is placed there);
/// 1 to 64, where the first object starting on it starts, plus one; past
/// 64, that none does, and the one covering it starts at least
/// `2^(b - 65)` cards back, so that a walk back to it takes a logarithm of
/// the object's length in steps.
#[inline(always)]
fn cross(map: &mut fixpt_memmgmt::Words, last: &mut usize, at: usize, n: usize) {
    if at >= 2 * MAX_SEMI_WORDS {
        return;
    }
    let card = at >> CARD_SHIFT;
    if card != *last {
        set_byte(map, card, (at & (CARD_WORDS - 1)) as u8 + 1);
        *last = card;
    }
    for k in card + 1..=(at + n - 1) >> CARD_SHIFT {
        let back = (k - card).ilog2() as u8;
        set_byte(map, k, CARD_WORDS as u8 + 1 + back);
    }
}
