//! A heap's names (`TODO.md` §292, the user's, 2026-11-17): the UTF-8 text
//! of its interned symbols' names, each once, numbered, in memory of this
//! module's own that never moves. The heap owns them ([`Owner`]) and frees a
//! name by a sweep, as it frees an object, once nothing holds it; the Rust
//! side reads a name as a `&str` where it is kept, nothing copied, through
//! the heap or through a [`Holder`] it was given (an `Interner`'s).
//!
//! What makes a name's `&str` sound is here alone:
//! - a name's bytes are copied from a `&str`, so are UTF-8, and are written
//!   only where no readable name is: past every byte used, or where a name
//!   freed was;
//! - a name is freed only by [`Owner::sweep`], which takes the owner `&mut`
//!   (so no `&str` borrowed from it lives), and frees no name a holder
//!   holds;
//! - a holder reads only a name it holds ([`Holder::get`]), and lets one go
//!   only `&mut` (so no `&str` borrowed from it lives) or by being dropped.
//!
//! So a `&str` borrowed from the owner or a holder is of a name that stays
//! as it is until the borrow ends. The memory itself lives as long as the
//! owner or a holder does. A name's number ([`NameId`]) is reused once it is
//! freed: it is no name's for good, only while something holds it, so it is
//! kept by what holds the name (a holder, or the owner's heap, in a word of
//! its own), never apart from it.
//!
//! One thread's: an owner and its holders are not `Send`, so nothing here is
//! read on one thread while another writes it.

use std::cell::RefCell;
use std::rc::Rc;

use fixpt_hash::HashMap;

/// The most names a space may hold.
const COUNT_MAX: usize = 1 << 30;
/// A space's first chunk of bytes; each next one twice the last, to
/// `CHUNK_MAX`, and a name longer than a chunk in one of its own.
const CHUNK_MIN: usize = 1 << 12;
const CHUNK_MAX: usize = 1 << 20;

/// Where name `n` is: its chunk, its first byte there, and how many.
#[derive(Clone, Copy, Default)]
struct Place {
    chunk: u32,
    start: u32,
    len: u32,
}

/// A name of a space: its number there, for its holder or owner (its heap,
/// in a word of its own: [`bits`](NameId::bits), [`Owner::name`]) to read
/// it by, while it holds it.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct NameId(u32);

impl NameId {
    /// Its number, for the owner's heap to keep in a word of its own (a
    /// symbol's name), read back by [`Owner::name`]. Below `1 << 30`.
    #[inline]
    pub fn bits(self) -> u32 {
        self.0
    }
}

/// Which space names are of, among those the process made: never another's.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct SpaceId(u32);

/// The next space's [`Owner::id`].
static NEXT_ID: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(1);

struct Space {
    /// Which space this is, among those the process made.
    id: SpaceId,
    state: RefCell<State>,
}

#[derive(Default)]
struct State {
    /// The numbers made so far: each below it is a name, or free.
    count: u32,
    /// Each number's place.
    places: Vec<Place>,
    /// The names' bytes: chunks allocated once each, never moved nor
    /// freed before the space (each a `Box<[u8]>`, kept as its raw parts
    /// so that writing past a name read borrows nothing of it); and how
    /// much of the last is used.
    chunks: Vec<(*mut u8, usize)>,
    fill: usize,
    /// Each number's: whether it is a name now (not free), and how many
    /// holders hold it.
    live: Vec<bool>,
    held: Vec<u32>,
    /// Each name by its text's hash.
    index: ByHash<Hashed>,
    /// Numbers freed, to be made again; and the places of names freed, by
    /// length, to be written again by a name as long.
    free_numbers: Vec<u32>,
    free_bytes: HashMap<u32, Vec<(u32, u32)>>,
}

/// A map keyed by a name's hash, which is its own hash: not hashed again
/// (by `fixpt_hash`'s SipHash, which a profile of loading the front end's
/// names found at 1.3% of a run).
type ByHash<V> = std::collections::HashMap<u64, V, std::hash::BuildHasherDefault<AsIs>>;

/// The hasher of [`ByHash`]: the key, as it is.
#[derive(Default)]
struct AsIs(u64);

impl std::hash::Hasher for AsIs {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0 << 8) | b as u64;
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = x;
    }
}

/// The names of one hash: one, as nearly always, or several.
enum Hashed {
    One(u32),
    Many(Vec<u32>),
}

impl State {
    /// The numbers of the names of hash `h`.
    fn hashed(&self, h: u64) -> &[u32] {
        match self.index.get(&h) {
            None => &[],
            Some(Hashed::One(n)) => std::slice::from_ref(n),
            Some(Hashed::Many(ns)) => ns,
        }
    }

    /// The numbers of hash `h` made `ns`.
    fn set_hashed(&mut self, h: u64, ns: Vec<u32>) {
        match ns.as_slice() {
            [] => {
                self.index.remove(&h);
            }
            [n] => {
                self.index.insert(h, Hashed::One(*n));
            }
            _ => {
                self.index.insert(h, Hashed::Many(ns));
            }
        }
    }
}

impl Drop for Space {
    fn drop(&mut self) {
        for &(p, len) in &self.state.get_mut().chunks {
            // SAFETY: each chunk is a `Box<[u8]>` of `len` bytes made into
            // its raw parts (`Space::room`); nothing borrows from it, as its
            // space is being dropped.
            drop(unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(p, len)) });
        }
    }
}

/// A name's hash, for the index: FNV-1a.
fn hash(text: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in text.as_bytes() {
        h = (h ^ b as u64).wrapping_mul(0x100_0000_01b3);
    }
    h
}

impl Space {
    fn new() -> Space {
        Space { id: SpaceId(NEXT_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed)), state: RefCell::default() }
    }

    /// Where `len` bytes more go: a chunk and a place in it, past every
    /// byte used there, a chunk made if the last has no room.
    fn room(st: &mut State, len: usize) -> (u32, u32) {
        let last = st.chunks.last().map_or(0, |&(_, n)| n);
        if st.chunks.is_empty() || st.fill + len > last {
            let n = if st.chunks.is_empty() { CHUNK_MIN } else { (last * 2).min(CHUNK_MAX) }.max(len);
            let chunk = Box::into_raw(vec![0u8; n].into_boxed_slice());
            st.chunks.push((chunk as *mut u8, n));
            st.fill = 0;
        }
        let at = st.fill;
        st.fill += len;
        ((st.chunks.len() - 1) as u32, at as u32)
    }

    /// The bytes at place `p`, as a `str`. The caller knows they are a
    /// live name's, so are UTF-8 and stay as they are while it borrows
    /// them (the module's doc).
    fn at(st: &State, p: Place) -> &str {
        let (chunk, _) = st.chunks[p.chunk as usize];
        // SAFETY: the place is within its chunk, which lives as long as the
        // space and never moves; its bytes a name's, copied from a `str`,
        // not written while the name is live.
        unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(chunk.add(p.start as usize), p.len as usize)) }
    }

    /// Name `n`'s text, if it is a name now. The `&str` is the caller's to
    /// keep only while `n` is not freed: [`Owner::get`] and
    /// [`Holder::get`] bound it so.
    fn text(&self, n: u32) -> Option<&str> {
        let st = self.state.borrow();
        if !st.live.get(n as usize).copied().unwrap_or(false) {
            return None;
        }
        let text = Self::at(&st, st.places[n as usize]);
        // SAFETY: the chunk's bytes live as long as the space, which `self`
        // borrows, not the state's borrow: no longer than that, and while
        // the name is live (the caller's bound, the module's doc).
        Some(unsafe { &*(text as *const str) })
    }

    /// The number of the name `text`, if it is one.
    fn find(&self, text: &str) -> Option<u32> {
        self.find_hashed(text, hash(text))
    }

    /// [`find`](Space::find), its hash `h` given.
    fn find_hashed(&self, text: &str, h: u64) -> Option<u32> {
        let st = self.state.borrow();
        st.hashed(h).iter().copied().find(|&n| Self::at(&st, st.places[n as usize]) == text)
    }

    /// The number of the name `text`: its own, made now if it had none.
    fn intern(&self, text: &str) -> u32 {
        let h = hash(text);
        if let Some(n) = self.find_hashed(text, h) {
            return n;
        }
        let mut st = self.state.borrow_mut();
        let len = u32::try_from(text.len()).expect("a name of fewer than 4 GiB");
        // Where its bytes go: a freed name's as long, or past every byte.
        let (chunk, start) = match st.free_bytes.get_mut(&len).and_then(|v| v.pop()) {
            Some(at) => at,
            None => Self::room(&mut st, text.len()),
        };
        let n = match st.free_numbers.pop() {
            Some(n) => n,
            None => {
                let n = st.count;
                assert!((n as usize) < COUNT_MAX, "a heap's names are full ({n} names)");
                st.count += 1;
                st.live.push(false);
                st.held.push(0);
                st.places.push(Place::default());
                n
            }
        };
        // SAFETY: `start..start + len` of the chunk is no live name's (past
        // every byte used there, or a freed name's), within the chunk; it
        // is written through the chunk's raw pointer, borrowing nothing of
        // what is read elsewhere in it.
        unsafe { std::ptr::copy_nonoverlapping(text.as_ptr(), st.chunks[chunk as usize].0.add(start as usize), text.len()) };
        st.places[n as usize] = Place { chunk, start, len };
        st.live[n as usize] = true;
        if !st.index.contains_key(&h) {
            st.index.insert(h, Hashed::One(n));
        } else {
            let ns = st.hashed(h).iter().copied().chain([n]).collect();
            st.set_hashed(h, ns);
        }
        n
    }

    /// Room made for `more` names more: an image's, about to be interned.
    fn reserve(&self, more: usize) {
        let mut st = self.state.borrow_mut();
        st.index.reserve(more);
        st.live.reserve(more);
        st.held.reserve(more);
        st.places.reserve(more);
    }

    /// Name `n` freed, its number and its bytes to be made again.
    fn free(st: &mut State, n: u32) {
        let p = st.places[n as usize];
        let h = hash(Self::at(st, p));
        let rest = st.hashed(h).iter().copied().filter(|&m| m != n).collect();
        st.set_hashed(h, rest);
        st.live[n as usize] = false;
        st.free_numbers.push(n);
        st.free_bytes.entry(p.len).or_default().push((p.chunk, p.start));
    }
}

/// A heap's names: what the heap holds, and frees by [`sweep`](Owner::sweep).
pub struct Owner(Rc<Space>);

impl Default for Owner {
    fn default() -> Owner {
        Owner::new()
    }
}

impl Owner {
    pub fn new() -> Owner {
        Owner(Rc::new(Space::new()))
    }

    /// The name `text`: its own, made now if it had none. It lives until a
    /// sweep frees it.
    pub fn intern(&self, text: &str) -> NameId {
        NameId(self.0.intern(text))
    }

    /// The name `text`, if it is one; making none.
    pub fn find(&self, text: &str) -> Option<NameId> {
        self.0.find(text).map(NameId)
    }

    /// [`intern`](Owner::intern) of each of `texts`, room made for them
    /// first: an image's, as it is read.
    pub fn intern_all<'t>(&self, texts: impl ExactSizeIterator<Item = &'t str>) -> Vec<NameId> {
        self.0.reserve(texts.len());
        texts.map(|t| NameId(self.0.intern(t))).collect()
    }

    /// Name `n`'s text, if it is a name: as long as the owner is borrowed,
    /// no sweep frees it.
    pub fn get(&self, n: NameId) -> Option<&str> {
        self.0.text(n.0)
    }

    /// The name whose [`bits`](NameId::bits) are `bits`, if it is one now:
    /// what the owner's heap kept in a word of its own.
    #[inline]
    pub fn name(&self, bits: u32) -> Option<NameId> {
        self.0.state.borrow().live.get(bits as usize).copied().unwrap_or(false).then_some(NameId(bits))
    }

    /// Which space this is, among those the process made.
    pub fn id(&self) -> SpaceId {
        self.0.id
    }

    /// How many numbers have been made: each name's is below it.
    pub fn count(&self) -> u32 {
        self.0.state.borrow().count
    }

    /// Every name not kept by `keep` and held by no holder, freed: how
    /// many.
    pub fn sweep(&mut self, mut keep: impl FnMut(NameId) -> bool) -> usize {
        let mut st = self.0.state.borrow_mut();
        let mut freed = 0;
        for n in 0..st.count {
            if st.live[n as usize] && st.held[n as usize] == 0 && !keep(NameId(n)) {
                Space::free(&mut st, n);
                freed += 1;
            }
        }
        freed
    }

    /// A holder of these names, holding none yet.
    pub fn holder(&self) -> Holder {
        Holder { space: self.0.clone(), mine: Vec::new(), order: Vec::new() }
    }
}

/// Names held, of a heap's (or of its own, made by [`Holder::new`]): read
/// through it, and kept from every sweep until it lets them go.
pub struct Holder {
    space: Rc<Space>,
    /// Whether it holds each number, by number; and the names it holds, in
    /// the order it took them.
    mine: Vec<bool>,
    order: Vec<NameId>,
}

impl Holder {
    /// A holder of names of its own, which no heap owns: freed with it.
    pub fn new() -> Holder {
        Owner::new().holder()
    }

    /// The name `text`, made if it had none, held.
    pub fn hold_text(&mut self, text: &str) -> NameId {
        self.hold_text_new(text).0
    }

    /// [`hold_text`](Holder::hold_text), and whether this took it now (it
    /// held it not before).
    pub fn hold_text_new(&mut self, text: &str) -> (NameId, bool) {
        let n = NameId(self.space.intern(text));
        let new = !self.holds(n);
        self.take(n);
        (n, new)
    }

    /// The name `text`, if it is one this holds.
    pub fn find(&self, text: &str) -> Option<NameId> {
        self.space.find(text).map(NameId).filter(|&n| self.holds(n))
    }

    /// Name `n` held, if it is a name: whether it is.
    pub fn hold(&mut self, n: NameId) -> bool {
        if self.space.text(n.0).is_none() {
            return false;
        }
        self.take(n);
        true
    }

    /// The name whose [`bits`](NameId::bits) are `bits`, if this holds it.
    #[inline]
    pub fn held_name(&self, bits: u32) -> Option<NameId> {
        let n = NameId(bits);
        self.holds(n).then_some(n)
    }

    fn take(&mut self, n: NameId) {
        if self.holds(n) {
            return;
        }
        let i = n.0 as usize;
        if self.mine.len() <= i {
            self.mine.resize(i + 1, false);
        }
        self.mine[i] = true;
        self.order.push(n);
        self.space.state.borrow_mut().held[i] += 1;
    }

    /// Whether this holds name `n`.
    #[inline]
    pub fn holds(&self, n: NameId) -> bool {
        self.mine.get(n.0 as usize).copied().unwrap_or(false)
    }

    /// Name `n`'s text, if this holds it: as long as this is borrowed, it
    /// holds it still, so no sweep frees it.
    #[inline]
    pub fn get(&self, n: NameId) -> Option<&str> {
        if !self.holds(n) {
            return None;
        }
        self.space.text(n.0)
    }

    /// How many names this holds: what [`release_to`](Holder::release_to)
    /// releases back to.
    pub fn len(&self) -> usize {
        self.order.len()
    }

    pub fn is_empty(&self) -> bool {
        self.order.is_empty()
    }

    /// The names held, in the order this took them.
    pub fn held(&self) -> &[NameId] {
        &self.order
    }

    /// Every name this took after it held `len` let go, for a sweep to
    /// free if nothing else holds it.
    pub fn release_to(&mut self, len: usize) {
        if len >= self.order.len() {
            return;
        }
        let mut st = self.space.state.borrow_mut();
        for n in self.order.drain(len..) {
            self.mine[n.0 as usize] = false;
            st.held[n.0 as usize] -= 1;
        }
    }

    /// Which space its names are of ([`Owner::id`]).
    pub fn space_id(&self) -> SpaceId {
        self.space.id
    }

    /// Whether `other` holds names of the same space as this.
    pub fn same_space(&self, other: &Owner) -> bool {
        Rc::ptr_eq(&self.space, &other.0)
    }
}

impl Default for Holder {
    fn default() -> Holder {
        Holder::new()
    }
}

impl Drop for Holder {
    fn drop(&mut self) {
        self.release_to(0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_name_is_kept_once_and_read_where_it_is() {
        let o = Owner::new();
        let a = o.intern("car");
        let b = o.intern("λx");
        assert_ne!(a, b);
        assert_eq!(o.intern("car"), a);
        assert_eq!((o.get(a), o.get(b)), (Some("car"), Some("λx")));
        assert_eq!((o.find("λx"), o.find("none")), (Some(b), None));
        assert_eq!(o.get(o.intern("")), Some(""));
        assert!(std::ptr::eq(o.get(a).unwrap(), o.get(a).unwrap()), "kept, not copied");
        assert_eq!(o.name(o.count()), None);
    }

    #[test]
    fn a_sweep_frees_what_nothing_holds_or_keeps() {
        let mut o = Owner::new();
        let (a, b, c) = (o.intern("a"), o.intern("b"), o.intern("c"));
        let mut h = o.holder();
        assert!(h.hold(b));
        assert_eq!(h.get(a), None, "a holder reads only what it holds");
        assert_eq!(o.sweep(|n| n == c), 1, "`a` alone");
        assert_eq!((o.get(a), o.get(b), o.get(c)), (None, Some("b"), Some("c")));
        assert_eq!(o.find("a"), None);
        // Its number and bytes made again, by a name as long.
        let d = o.intern("d");
        assert_eq!(d, a);
        assert_eq!(o.get(d), Some("d"));
        // Let go, then freed.
        h.release_to(0);
        assert_eq!(o.sweep(|_| false), 3);
        assert_eq!(o.count(), 3, "no number made since");
    }

    #[test]
    fn a_holder_keeps_its_names_past_the_owner() {
        let o = Owner::new();
        let mut h = o.holder();
        let n = h.hold_text("kept");
        drop(o);
        assert_eq!(h.get(n), Some("kept"));
        assert_eq!(h.find("kept"), Some(n));
    }

    #[test]
    fn a_holder_lets_go_back_to_a_mark() {
        let mut o = Owner::new();
        let mut h = o.holder();
        let a = h.hold_text("a");
        let mark = h.len();
        let b = h.hold_text("b");
        assert_eq!(h.hold_text("a"), a, "held once");
        assert_eq!(h.held(), &[a, b]);
        h.release_to(mark);
        assert_eq!((h.get(a), h.get(b)), (Some("a"), None));
        assert_eq!(o.sweep(|_| false), 1);
        assert_eq!(o.get(b), None);
        // Two holders of one name: freed only when both let go.
        let mut g = o.holder();
        assert!(g.hold(a));
        drop(h);
        assert_eq!(o.sweep(|_| false), 0);
        drop(g);
        assert_eq!(o.sweep(|_| false), 1);
    }

    #[test]
    fn a_holder_of_its_own() {
        let mut h = Holder::new();
        let n = h.hold_text("alone");
        assert_eq!(h.get(n), Some("alone"));
    }
}

#[cfg(test)]
mod collisions {
    use super::*;

    /// Two names of one hash, as the index keeps them: each found, and
    /// either freed, the other kept.
    #[test]
    fn names_of_one_hash() {
        let mut o = Owner::new();
        let (a, b) = (o.intern("a"), o.intern("b"));
        {
            // Made to share a hash, as two names may.
            let mut st = o.0.state.borrow_mut();
            let (ha, hb) = (hash("a"), hash("b"));
            st.index.remove(&hb);
            st.set_hashed(ha, vec![a.0, b.0]);
        }
        assert_eq!(o.0.state.borrow().hashed(hash("a")), &[a.0, b.0]);
        assert_eq!(o.find("a"), Some(a));
        let mut h = o.holder();
        h.hold(b);
        o.sweep(|_| false);
        assert_eq!(o.0.state.borrow().hashed(hash("a")), &[b.0]);
        assert_eq!(o.get(b), Some("b"));
    }
}
