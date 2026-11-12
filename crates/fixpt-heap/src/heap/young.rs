//! The nursery, and what lets it be collected alone
//! (`docs/research/generational-gc.md`): the card table, the old space's
//! crossing map, and minor collections.
//!
//! A generational heap allocates everything in the nursery. A minor
//! collection copies what is live there to the end of the old semispace
//! (the active one), Cheney's way, and empties it: everything live is
//! promoted at once. Its roots are the usual ones, what the regions hold
//! (scanned whole), and the dirty cards of the old space, the static area
//! and the code area: a store that puts a young reference into any of them
//! marks the card of the word written (`Heap::set_slot`, and each machine's
//! own stores).
//!
//! The areas older than the old space, collected less often than it or
//! never (static ≫ code ≫ old ≫ nursery: the static area's mutable half,
//! never collected, and the code area, collected by a code collection
//! alone), have a second table: a store there of what is in the old space
//! (or, into the static area, of code that may be freed) marks its card in
//! that one, which a minor collection does not read. A card stays marked
//! there while it refers to such: the remembered set by which a major
//! collection scans those areas, not the whole of them (`scan_dirty_cards`,
//! `scan_code_cards`).

use super::{Copier, Heap, MAX_SEMI_WORDS, MEM_WORDS, NURSERY_BASE, NURSERY_MAX, each_field, read_head};
use crate::layout;
use crate::value::{Value, is_extension, is_header};
use std::collections::{HashMap, HashSet};

/// A card is 64 words, 512 bytes: word `i` of the heap's memory is on card
/// `i >> CARD_SHIFT`.
pub(super) const CARD_SHIFT: usize = 6;
const CARD_WORDS: usize = 1 << CARD_SHIFT;
/// Cards over the whole of the heap's memory (the table's bytes, and the
/// crossing map's, which knows the semispaces' and the static area's).
pub(super) const CARDS: usize = MEM_WORDS >> CARD_SHIFT;
/// Cards over the areas older than the old space (`Heap::old_cards`): the
/// static area's mutable half, and after it the code area, to the end.
pub(super) const OLDER_CARDS: usize = (MEM_WORDS - super::STATIC_MUTABLE_BASE) >> CARD_SHIFT;
/// The first of them, in the whole table.
const OLDER_CARD_0: usize = super::STATIC_MUTABLE_BASE >> CARD_SHIFT;
const _: () = assert!(OLDER_CARD_0.is_multiple_of(8), "the two tables' words cover the same cards");
const _: () = assert!(super::STATIC_MUTABLE_BASE + super::STATIC_WORDS / 2 == super::CODE_BASE, "the code area follows the static area's mutable half");

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

/// Whether word `rel`'s card is dirty: for tests.
#[cfg(test)]
pub(super) fn card_marked(h: &Heap, rel: usize) -> bool {
    byte(&h.cards, rel >> CARD_SHIFT) != 0
}

impl Heap {
    /// The card of word `rel` marked: a young reference may be there.
    #[inline(always)]
    pub(super) fn mark_card(&mut self, rel: usize) {
        set_byte(&mut self.cards, rel >> CARD_SHIFT, 1);
    }

    /// The second table's card of word `rel`, of an area older than the old
    /// space, marked: what is in the old space (or, from the static area,
    /// code that may be freed) may be referred to there.
    #[inline(always)]
    pub(super) fn mark_old_card(&mut self, rel: usize) {
        set_byte(&mut self.old_cards, (rel >> CARD_SHIFT) - OLDER_CARD_0, 1);
    }

    /// Word `rel`, of the static area's mutable half, holding code that may
    /// be freed: kept with the others (`Heap::static_code_slots`).
    #[inline(always)]
    pub(super) fn remember_static_code(&mut self, rel: usize) {
        self.static_code_slots.push(rel);
    }

    /// Each of the code area's cards marked in the first table marked in the
    /// second instead: after a code collection, which promotes what they
    /// may refer to, but scans none of them.
    pub(super) fn code_cards_aged(&mut self) {
        for p in &self.code.parts {
            let (lo, hi) = ((p.base >> CARD_SHIFT) >> 3, (p.top.div_ceil(CARD_WORDS)).div_ceil(8));
            for w in lo..hi {
                let a = std::mem::take(&mut self.cards.words_mut()[w]);
                self.old_cards.words_mut()[w - (OLDER_CARD_0 >> 3)] |= a;
            }
        }
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
    /// every card of the first table clean. The roots are `extra_roots` and
    /// the heap's own, the regions' objects, and the dirty cards (of the
    /// first table) of the old space, the static area and the code area.
    pub(super) fn collect_minor(&mut self, extra_roots: &mut [&mut [Value]]) {
        let started = std::time::Instant::now();
        // The mutator's phase paused (`TODO.md` §252).
        let phase = fixpt_memmgmt::phases::collection("gc:minor");
        let before = self.used();
        self.peak_words = self.peak_words.max(before as u64);
        if self.verify_barrier {
            self.verify_remembered().unwrap_or_else(|e| panic!("the write barrier missed a store: {e}"));
        }
        let young = self.nursery_top - NURSERY_BASE;
        self.words_allocated += young as u64;
        let (lo, old_top) = (self.active, self.top);
        let regions: Vec<(usize, usize)> = self.regions.ranges().collect();
        // The first object promoted starts the card of the old top's last
        // word only if none starts there already.
        let last_card = match old_top > lo {
            true if (1..=CARD_WORDS).contains(&(byte(&self.crossing, (old_top - 1) >> CARD_SHIFT) as usize)) => (old_top - 1) >> CARD_SHIFT,
            _ => usize::MAX,
        };
        let remembered = self.remembered();
        let mem = self.mem.words_mut();
        let mut c = Copier {
            base: self.base,
            from: NURSERY_BASE,
            to: old_top,
            free: 0,
            owner: HashMap::new(),
            new: Vec::new(),
            marked: HashSet::new(),
            large_marks: HashSet::new(),
            large_gray: Vec::new(),
            code_marks: HashSet::new(),
            code_gray: Vec::new(),
            weak_pairs: Vec::new(),
            regions: &mut self.regions,
            minor: true,
            trace_code: false,
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
        // What the regions hold: scanned whole, since machine code fills
        // what it allocates there without marking cards.
        for (from, to) in regions {
            let mut at = from;
            while at < to {
                at += Self::scan_one(mem, at, &mut c);
            }
        }
        // The code area's dirty cards, and the old space's, each cleaned as
        // it is scanned; and the static area's mutable half's; what is left
        // referring to the old space marked in the second table.
        for part in &self.code.parts {
            let older = OlderScan { table: &mut self.old_cards, remembered: Remembered::NONE, major: false, slots: None };
            scan_code_cards(&mut self.cards, mem, &mut c, part.base, &part.starts, older);
        }
        scan_dirty_cards(&mut self.cards, mem, &mut c, lo, old_top, None);
        let statics = OlderScan { table: &mut self.old_cards, remembered, major: false, slots: Some(&mut self.static_code_slots) };
        scan_dirty_cards(&mut self.cards, mem, &mut c, super::STATIC_MUTABLE_BASE, self.static_top, Some(statics));
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
        // Past the semispace (one made small): room for the next nursery's
        // promotion too, not just this one's.
        if self.top - self.active > self.semi {
            self.grow(self.top - self.active + self.nursery_words);
        }
        self.nursery_top = NURSERY_BASE;
        self.minor_count += 1;
        self.words_copied += free as u64;
        self.minor_words_copied += free as u64;
        phase.copied(free as u64);
        self.top_after_gc = self.top;
        let nanos = started.elapsed().as_nanos() as u64;
        self.gc_nanos += nanos;
        self.minor_nanos += nanos;
        self.max_minor_nanos = self.max_minor_nanos.max(nanos);
        self.traced("minor", self.minor_count, nanos, free, before);
        self.provenance_swept();
    }

    /// What the static area's remembered set remembers, now.
    pub(super) fn remembered(&self) -> Remembered {
        Remembered { unfixed: self.code.parts.each_ref().map(|p| (p.fixed, p.limit())) }
    }

    /// The cards from word `lo` to `hi` of the static area's mutable half
    /// or the code area marked where they refer to what moves (or, in the
    /// static area, to code that may be freed), each in its table: the
    /// remembered sets, for what was put there with no write barrier (an
    /// image's).
    pub(super) fn remember_moving(&mut self, lo: usize, hi: usize) {
        let r = if super::code::in_code_area(lo) { Remembered::NONE } else { self.remembered() };
        let mut marks = Vec::new();
        each_field(&self.mem.words()[lo..hi], lo, |at, v| {
            if let Some(held) = r.kind(self.base, v) {
                marks.push((at, held, is_young(self.ref_ix(v))));
            }
        });
        for (at, held, young) in marks {
            match held {
                Held::Moves if young => self.mark_card(at),
                Held::Moves => self.mark_old_card(at),
                Held::Code => self.remember_static_code(at),
            }
        }
    }

    /// That every young reference in the old space, the static area's
    /// mutable half and the code area is on a dirty card of the first
    /// table; every other reference to what moves in the latter two, on one
    /// of either; and every reference to code that may be freed in the
    /// static area, on one of either or among its slots: what the write
    /// barrier promises a minor collection, and the remembered sets a major
    /// one. It walks them whole; for tests.
    pub fn verify_remembered(&self) -> Result<(), String> {
        let code = self.code.parts.each_ref().map(|p| (p.base, p.top));
        let young = |v: Value| v.is_ref() && is_young(self.ref_ix(v));
        for (lo, hi) in [(self.active, self.top), (super::STATIC_MUTABLE_BASE, self.static_top), code[0], code[1]] {
            self.verify_remembered_in(lo, hi, |f, v| young(v) && byte(&self.cards, f >> CARD_SHIFT) == 0)?;
        }
        let neither = |f: usize| byte(&self.cards, f >> CARD_SHIFT) == 0 && byte(&self.old_cards, (f >> CARD_SHIFT) - OLDER_CARD_0) == 0;
        for (lo, hi) in [code[0], code[1]] {
            self.verify_remembered_in(lo, hi, |f, v| self.moves(v) && neither(f))?;
        }
        let r = self.remembered();
        let slots: HashSet<usize> = self.static_code_slots.iter().copied().collect();
        self.verify_remembered_in(super::STATIC_MUTABLE_BASE, self.static_top, |f, v| match r.kind(self.base, v) {
            Some(Held::Moves) => neither(f),
            Some(Held::Code) => neither(f) && !slots.contains(&f),
            None => false,
        })?;
        // And what native code stored, marking cards only, in the static
        // area's immutable half: nothing that may move or be freed.
        self.verify_immutable()
    }

    /// That no field from word `lo` to `hi` is `missed` (by where it is and
    /// what it holds): one its cards should remember, and do not.
    fn verify_remembered_in(&self, lo: usize, hi: usize, missed: impl Fn(usize, Value) -> bool) -> Result<(), String> {
        let mut at = lo;
        while at < hi {
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
                if missed(f, v) {
                    return Err(format!("word {f} holds {v:?}, which its card should remember, and its card is clean"));
                }
            }
            at += n;
        }
        Ok(())
    }
}

/// The dirty cards from word `lo` to `hi`, of a space the crossing map
/// knows, each scanned: the fields on it traced by `c`. The table is read a
/// word (eight cards) at a time, a clean word skipped whole, so that a
/// large space with few dirty cards costs little. Each card is cleaned.
///
/// For the static area's mutable half, `older` (`OlderScan`): a major
/// collection scans the cards dirty in either table, and each card left
/// referring to what the second table remembers is marked there, else
/// cleaned there too.
pub(super) fn scan_dirty_cards(cards: &mut fixpt_memmgmt::Words, mem: &mut [u64], c: &mut Copier, lo: usize, hi: usize, mut older: Option<OlderScan>) {
    let (first, end) = (lo >> CARD_SHIFT, hi.div_ceil(CARD_WORDS));
    let mut card = first;
    while card < end {
        if card % 8 == 0 && card + 8 <= end && cards.words()[card >> 3] == 0 && !older.as_ref().is_some_and(|o| o.dirty(true, card)) {
            card += 8;
            continue;
        }
        let this = card;
        card += 1;
        let card = this;
        if byte(cards, card) == 0 && !older.as_ref().is_some_and(|o| o.dirty(false, card)) {
            continue;
        }
        let mut kept = false;
        let (clo, chi) = (card << CARD_SHIFT, ((card + 1) << CARD_SHIFT).min(hi));
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
                // A weak pair's car is not traced (`scan_one`), but is moved
                // on or cleared after: remembered as it is.
                let weak = head.kind == const { layout::kind("weak-pair") };
                if weak {
                    c.weak_pairs.push(main);
                    if (clo..chi).contains(&(main + 1))
                        && let Some(o) = &mut older
                    {
                        kept |= o.keeps(c.base, main + 1, Value(mem[main + 1]));
                    }
                }
                (main + 1 + weak as usize..main + 1 + head.fields, head.size())
            } else {
                (at..at + 2, 2)
            };
            for f in fields.start.max(clo)..fields.end.min(chi) {
                let v = Value(mem[f]);
                // Written only if moved (`scan_one`).
                if v.is_ref() {
                    let to = Heap::copy_out(mem, c, v);
                    if to.raw() != v.raw() {
                        mem[f] = to.raw();
                    }
                    if let Some(o) = &mut older {
                        kept |= o.keeps(c.base, f, to);
                    }
                }
            }
            at += n;
        }
        set_byte(cards, card, 0);
        if let Some(o) = &mut older {
            o.set(card, kept);
        }
    }
}

/// What the remembered sets of the areas older than the old space
/// remember: a reference to what a collection may move; and, from the
/// static area, to the code area's objects but what an image brought
/// (`code::Part::fixed`), which a code collection may free: in each part,
/// the words from the first of `unfixed` to the second.
#[derive(Clone, Copy)]
pub(super) struct Remembered {
    pub(super) unfixed: [(usize, usize); 2],
}

impl Remembered {
    /// What the code area's remembers: only what moves, since its objects
    /// are collected with the code they refer to.
    pub(super) const NONE: Remembered = Remembered { unfixed: [(0, 0); 2] };

    /// Whether `v`, in a heap whose memory starts at word `base`, is one.
    #[inline(always)]
    pub(super) fn holds(&self, base: usize, v: Value) -> bool {
        self.kind(base, v).is_some()
    }

    /// Which `v` is, if it is one: what moves, or code that may be freed.
    #[inline(always)]
    pub(super) fn kind(&self, base: usize, v: Value) -> Option<Held> {
        if !v.is_ref() {
            return None;
        }
        let i = if v.is_suffix_ref() { v.owner() } else { v.index() - base };
        let g = super::gen_of(i) & super::GEN_MASK;
        if g <= super::GEN_OLD {
            Some(Held::Moves)
        } else if g == super::GEN_CODE && self.unfixed.iter().any(|&(lo, hi)| (lo..hi).contains(&i)) {
            Some(Held::Code)
        } else {
            None
        }
    }
}

/// What a remembered set remembers a reference to.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Held {
    Moves,
    Code,
}

/// What a scan of the cards of an area older than the old space keeps up
/// (`scan_dirty_cards`, `scan_code_cards`).
pub(super) struct OlderScan<'a> {
    /// The second table (`Heap::old_cards`, cards from `OLDER_CARD_0`).
    pub(super) table: &'a mut fixpt_memmgmt::Words,
    pub(super) remembered: Remembered,
    /// Whether the collection is a major one, which scans the cards dirty
    /// in either table, not only the first's.
    pub(super) major: bool,
    /// For the static area: where each field found holding code that may be
    /// freed goes (`Heap::static_code_slots`), not by its card.
    pub(super) slots: Option<&'a mut Vec<usize>>,
}

impl OlderScan<'_> {
    /// Whether a major collection scans `card` (the eight from it, if
    /// `word`) for the second table's mark.
    #[inline(always)]
    fn dirty(&self, word: bool, card: usize) -> bool {
        let i = card - OLDER_CARD_0;
        self.major && if word { self.table.words()[i >> 3] != 0 } else { byte(self.table, i) != 0 }
    }

    /// Whether field `f`, holding `v` once the collection has moved it on,
    /// keeps its card marked in the second table; code it holds is kept by
    /// the field itself, among the slots.
    #[inline(always)]
    fn keeps(&mut self, base: usize, f: usize, v: Value) -> bool {
        match self.remembered.kind(base, v) {
            Some(Held::Code) => {
                self.slots.as_mut().expect("code remembered only from the static area").push(f);
                false
            }
            held => held.is_some(),
        }
    }

    /// `card`, just scanned, marked in the second table if `kept`, else
    /// cleaned there.
    #[inline(always)]
    fn set(&mut self, card: usize, kept: bool) {
        set_byte(self.table, card - OLDER_CARD_0, kept as u8);
    }
}

/// A part of the code area's dirty cards, from `base`, each scanned as
/// [`scan_dirty_cards`] scans the static area's (`older`), the fields on it
/// of the objects `starts` (the part's, in address order) finds there.
/// Only ordinary headers, and no weak pair: the area holds only bloblets
/// (`Heap::make_code_bloblet`).
pub(super) fn scan_code_cards(cards: &mut fixpt_memmgmt::Words, mem: &mut [u64], c: &mut Copier, base: usize, starts: &[usize], mut older: OlderScan) {
    let Some(&last) = starts.last() else { return };
    let (first, end) = (base >> CARD_SHIFT, (last + read_head(mem, last).size()).div_ceil(CARD_WORDS));
    let mut card = first;
    while card < end {
        if card % 8 == 0 && card + 8 <= end && cards.words()[card >> 3] == 0 && !older.dirty(true, card) {
            card += 8;
            continue;
        }
        let this = card;
        card += 1;
        if byte(cards, this) == 0 && !older.dirty(false, this) {
            continue;
        }
        let mut kept = false;
        let (clo, chi) = (this << CARD_SHIFT, (this + 1) << CARD_SHIFT);
        // From the last object that starts at or before the card.
        let mut k = starts.partition_point(|&s| s <= clo).saturating_sub(1);
        while k < starts.len() && starts[k] < chi {
            let at = starts[k];
            let fields = at + 1..at + 1 + read_head(mem, at).fields;
            for f in fields.start.max(clo)..fields.end.min(chi) {
                let v = Value(mem[f]);
                if v.is_ref() {
                    let to = Heap::copy_out(mem, c, v);
                    if to.raw() != v.raw() {
                        mem[f] = to.raw();
                    }
                    kept |= older.keeps(c.base, f, to);
                }
            }
            k += 1;
        }
        set_byte(cards, this, 0);
        older.set(this, kept);
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
    if at >= 2 * MAX_SEMI_WORDS && !super::in_static(at) {
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
