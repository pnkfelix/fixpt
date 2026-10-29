//! An image put into a heap that holds something already, beside it: its
//! live region past the old space's top, each part of its code area past
//! that part's, and every reference in them moved by one walk over them.
//! What [`Heap::copy_graph_with`] does from a heap loaded from the image,
//! without the heap, the graph's table or the copy.
//!
//! In place (`TODO.md` §160), where this heap is where the image's was and
//! holds nothing yet in its old space or its code area: the image's words
//! go where they were, and only the words its fixups name are written.
//! Given the file the image is in ([`Heap::splice_image_from`]), its static
//! area is mapped from it there rather than copied (`TODO.md` §160 item 4):
//! privately, so that what a collection writes into its mutable half is
//! the process's own copy of that page; its immutable half read-only, once
//! the splice is done, where it ends on a page (`image::dump_static`).
//!
//! As that copy does, an interned symbol of the image is this heap's of the
//! same name, where there is one, and the image's shared stub is this
//! heap's, where it has one (else the image's is); each object `given`
//! names is this heap's object instead. The image's objects otherwise all
//! come in, reached or not: an image is made of one graph
//! (`save_native_front_end`).

use super::code::{PART_BASES, in_code_area};
use super::young::is_young;
use super::{Heap, read_head, relocating};
use crate::image::Parts;
use crate::layout;
use crate::value::{Value, is_extension, is_header, make_header};
use std::collections::HashMap;

/// A symbol's name and global slot: fields 0 and 2 of 3, before its
/// trailer and the (empty) suffix it is pointed at (`Heap::alloc`).
const SYMBOL_NAME: usize = 4;
const SYMBOL_SLOT: usize = 2;

/// Where the image's words go: each of its regions (the live region, the
/// static area's two halves, the code area's two parts), from where in the
/// image to where in this heap, and how many words.
struct Moves {
    regions: [(usize, usize, usize); 5],
}

impl Moves {
    /// Where image word `i` goes; none if it is in no region. A region's
    /// end too: a bloblet of no suffix is pointed at one past its fields,
    /// which for its region's last object is the region's end. Regions are
    /// far apart, so no end is another's start.
    #[inline]
    fn index(&self, i: usize) -> Option<usize> {
        self.regions.iter().find(|&&(from, _, n)| n > 0 && (from..=from + n).contains(&i)).map(|&(from, to, _)| i - from + to)
    }
}

impl Heap {
    /// The image whose parts are `img` put into this heap ([the module's
    /// doc](self)); its roots, as this heap's. Each pair of `given` is an
    /// object of the image's (by its value there) and this heap's object
    /// that stands for it. Nothing collects meanwhile.
    pub fn splice_image(&mut self, img: &Parts, given: &[(Value, Value)]) -> Result<Vec<Value>, String> {
        self.splice_image_from(img, given, None)
    }

    /// [`splice_image`](Heap::splice_image) of an image whose bytes are
    /// `file`'s: its static area mapped from it where the splice is in
    /// place (the module's doc).
    pub fn splice_image_from(&mut self, img: &Parts, given: &[(Value, Value)], file: Option<&crate::Mapped>) -> Result<Vec<Value>, String> {
        let (n, ib) = (img.n_words(), img.base);
        // In place where nothing is in the old space, and each code part
        // holds nothing or what the image's starts with alike (the shared
        // stub, made first in both).
        let as_image = |k: usize| {
            let (p, w) = (&self.code.parts[k], img.code[k].0);
            let used = p.top - p.base;
            w.len() >= used * 8 && (0..used).all(|i| self.mem.words()[p.base + i] == u64::from_le_bytes(w[i * 8..i * 8 + 8].try_into().unwrap()))
        };
        let same_code = as_image(0) && as_image(1);
        let [(immutable_at, half), (static_at, _)] = super::static_area();
        let empty = self.immutable_top == immutable_at && self.static_top == static_at;
        // The image's immutable half where its symbols are this heap's (no
        // symbol here may move: none here yet, as when the image is read
        // before anything else); else its mutable half, scanned, since this
        // heap's symbols, which move, may stand for the image's.
        let immutable_ok = !self.symbols.iter().any(|&s| self.moves(s));
        // In place only where every part lands where it was made for: not
        // where the immutable half goes to the mutable half, whose words
        // the fixups alone would not reach (a front end read after the
        // runtime's symbols are made, the old space still empty).
        let in_place = self.base == ib && !relocating() && self.top == 0 && self.active == 0 && empty && same_code && immutable_ok;
        // Each from a card's start, so that the crossing map of the cards
        // before stays as it is.
        let card = 1 << super::young::CARD_SHIFT;
        let (old_top, old_immutable_top, old_static_top) = (self.top, self.immutable_top, self.static_top);
        // Under `FIXPT_IMAGE_RELOCATE`, a card more before each, so that
        // the image's words do not land where they were made for, and every
        // reference to them is moved (a heap read into first would not
        // move them otherwise: its static area empty, at the image's base).
        let shift = if relocating() { card } else { 0 };
        for top in [&mut self.top, &mut self.immutable_top, &mut self.static_top] {
            let gap = (card - *top % card) % card + shift;
            if gap > 0 {
                self.mem.words_mut()[*top] = make_header(const { layout::kind("bloblet") }, 0, (gap - 1) * 8);
                *top += gap;
            }
        }
        let (ni, ns) = (img.immutable.len() / 8, img.statics.len() / 8);
        let at = self.top;
        let (iat, sat) = if immutable_ok { (self.immutable_top, self.static_top) } else { (self.static_top, self.static_top + ni) };
        if at + n > self.active + self.semi {
            self.grow(at + n - self.active);
        }
        let room = if immutable_ok { iat + ni <= immutable_at + half && sat + ns <= static_at + half } else { sat + ns <= static_at + half };
        if !room {
            return Err(format!("the static area has no room for {} words", ni + ns));
        }
        let mut regions = [(0, at, n), (immutable_at, iat, ni), (static_at, sat, ns), (0, 0, 0), (0, 0, 0)];
        for (k, (words, _)) in img.code.iter().enumerate() {
            let p = &self.code.parts[k];
            let len = words.len() / 8;
            if !in_place && p.top + len > p.limit() {
                return Err(format!("the code area's part {k} has no room for {len} words"));
            }
            regions[k + 3] = (PART_BASES[k], if in_place { p.base } else { p.top }, len);
        }
        if img.code.iter().any(|(w, _)| !w.is_empty()) {
            self.start_code_area();
        }
        let moves = Moves { regions };
        let sources = [img.words, img.immutable, img.statics, img.code[0].0, img.code[1].0];
        // The static area mapped, in place, rather than copied: the
        // immutable half writable until the splice is done (a symbol's slot
        // may be written), then read-only if it ends on a page.
        let mut mapped = [false; 5];
        if in_place && let Some(f) = file {
            for k in [1, 2] {
                let (_, to, len) = moves.regions[k];
                mapped[k] = len > 0 && self.mem.map_from(to, f, sources[k], true);
            }
        }
        for (k, (&(_, to, len), from)) in moves.regions.iter().zip(sources).enumerate() {
            if mapped[k] {
                continue;
            }
            let mem = &mut self.mem.words_mut()[to..to + len];
            for (w, b) in mem.iter_mut().zip(from.chunks_exact(8)) {
                *w = u64::from_le_bytes(b.try_into().unwrap());
            }
        }
        let base = self.base;
        // An image reference moved, given nothing for it. A suffix ref's
        // owner is a place in the heap's memory already.
        let moved = |v: Value| -> Option<Value> {
            if v.is_suffix_ref() {
                return Value::suffix_ref(moves.index(v.owner())?, v.offset());
            }
            let i = moves.index(v.index().checked_sub(ib)?)?;
            Some(Value(v.raw() - ((v.index() as u64) << 3) + (((base + i) as u64) << 3)))
        };

        // What stands for objects of the image's, by where they are in it.
        let (symbols, globals, mut added) = (self.symbols.len(), self.globals.len(), Vec::new());
        let mut instead: HashMap<usize, Value> = given.iter().map(|&(v, to)| (v.index() - ib, to)).collect();
        let mut stub = None;
        for &s in &img.symbols {
            let at_s = moves.index(s.index() - ib).ok_or("a symbol outside the image")?;
            let name = moved(Value(self.mem.words()[at_s - SYMBOL_NAME])).ok_or("a symbol's name outside the image")?;
            let name = self.string_to_rust(name);
            if name == "%fx26-foreign-stub" {
                let slot = Value(img.word(s.index() - ib - SYMBOL_SLOT)).as_fixnum() as usize;
                if let Some(old) = img.globals.get(slot).filter(|w| w.is_ref() && in_code_area(w.index() - ib)) {
                    // This heap's stub stands for the image's; else the
                    // image's is this heap's.
                    match self.code.stub {
                        Value::FALSE => stub = Some(*old),
                        mine => {
                            instead.insert(old.index() - ib, mine);
                        }
                    }
                }
            }
            if let Some(&i) = self.symbol_index.get(&name) {
                instead.insert(s.index() - ib, self.symbols[i as usize]);
                continue;
            }
            // The image's symbol is this heap's, at a global slot of its own.
            let slot = self.globals.len();
            self.globals.push(Value::UNBOUND);
            // Written only if it is another slot than the image's: in a heap
            // that holds no symbol yet, it is the same.
            let w = Value::fixnum(slot as i64).raw();
            if self.mem.words()[at_s - SYMBOL_SLOT] != w {
                self.mem.words_mut()[at_s - SYMBOL_SLOT] = w;
            }
            self.symbol_index.insert(name.clone(), self.symbols.len() as u32);
            added.push(name);
            self.symbols.push(moved(s).expect("moved above"));
        }

        let unknown = std::cell::Cell::new(None);
        let map = |v: Value| -> Value {
            if !v.is_ref() {
                return v;
            }
            if v.is_suffix_ref() {
                if let Some(&to) = instead.get(&v.owner()) {
                    return Value::suffix_ref(to.index() - base, v.offset()).expect("an owner within the heap");
                }
            } else if let Some(&to) = v.index().checked_sub(ib).and_then(|i| instead.get(&i)) {
                return to;
            }
            moved(v).unwrap_or_else(|| {
                unknown.set(Some(format!("a reference {v:?} outside it")));
                v
            })
        };
        // Each field mapped (in place, each its fixups name); its card
        // marked if it is young now.
        let mut young = Vec::new();
        let mut field = |mem: &mut [u64], f: usize| {
            let v = map(Value(mem[f]));
            // Written only if changed, so that a page none changes is not.
            if mem[f] != v.raw() {
                mem[f] = v.raw();
            }
            let i = if v.is_suffix_ref() { v.owner() } else if v.is_ref() { v.index() - base } else { return };
            if is_young(i) {
                young.push(f);
            }
        };
        if in_place {
            let mem = self.mem.words_mut();
            for &f in &img.fixups {
                field(mem, f);
            }
        } else {
            for &(_, to, len) in &moves.regions {
                let mem = self.mem.words_mut();
                let mut scan = to;
                while scan < to + len {
                    let w = mem[scan];
                    let (first, count, size) = if is_header(w) {
                        let main = scan + is_extension(w) as usize;
                        let head = read_head(mem, main);
                        (main + 1, head.fields, head.size())
                    } else {
                        (scan, 2, 2)
                    };
                    for f in first..first + count {
                        field(mem, f);
                    }
                    scan += size;
                }
            }
        }
        if let Some(why) = unknown.take() {
            // Undone: nothing refers to the words past the top.
            for name in added {
                self.symbol_index.remove(&name);
            }
            self.symbols.truncate(symbols);
            self.globals.truncate(globals);
            (self.top, self.immutable_top, self.static_top) = (old_top, old_immutable_top, old_static_top);
            return Err(why);
        }
        for f in young {
            self.mark_card(f);
        }
        if let Some(old) = stub.and_then(moved) {
            let sym = self.intern("%fx26-foreign-stub");
            let slot = self.symbol_global_slot(sym);
            self.globals[slot] = old;
            self.code.stub = old;
        }

        self.cross_all(at, at + n);
        self.cross_all(iat, iat + ni);
        self.cross_all(sat, sat + ns);
        self.top = at + n;
        if immutable_ok {
            self.immutable_top = iat + ni;
        }
        self.static_top = sat + ns;
        self.budget_from(self.top - self.active);
        for (k, (words, free)) in img.code.iter().enumerate() {
            let (len, to) = (words.len() / 8, moves.regions[k + 3].1);
            let free: Vec<(usize, usize)> = free.iter().map(|&(s, n)| (to + s, n)).collect();
            let (mut at, mut starts, mut f) = (to, Vec::new(), free.iter().peekable());
            while at < to + len {
                if f.peek().is_some_and(|&&(s, _)| s == at) {
                    at += f.next().expect("peeked").1;
                    continue;
                }
                let w = self.word(at);
                starts.push(at);
                at += read_head(self.mem.words(), at + is_extension(w) as usize).size();
            }
            let p = &mut self.code.parts[k];
            // In place, what the part held is the image's start, walked again.
            if in_place {
                (p.used, p.free, p.starts) = (0, Vec::new(), Vec::new());
            }
            p.used += len - free.iter().map(|&(_, n)| n).sum::<usize>();
            p.top = to + len;
            p.free.extend(free);
            p.starts.extend(starts);
            if len > 0
                && let Ok(view) = &self.code_exec
            {
                view.flush((self.base + to) * 8, len * 8);
            }
        }
        // What the image's immutable half refers to of its code is never
        // swept: no collection scans that half to find it.
        if immutable_ok && ni > 0 {
            self.fix_code();
        }
        // Read-only: nothing may write there (`set_slot` refuses what
        // would), and a page past it the heap writes next is not one of it.
        if mapped[1] && (ni * 8).is_multiple_of(fixpt_memmgmt::reserve::probe::page()) {
            self.mem.set_writable(iat..iat + ni, false);
        }
        Ok(img.roots.iter().map(|&r| map(r)).collect())
    }
}
