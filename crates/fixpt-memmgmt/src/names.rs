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
//! owner or a holder does. A name's number is reused once it is freed: a
//! number is no name's for good, only while something holds it.
//!
//! One thread's: an owner and its holders are not `Send`, so nothing here is
//! read on one thread while another writes it.

use std::cell::RefCell;
use std::rc::Rc;

use fixpt_hash::HashMap;

/// The most bytes of names, and the most names, a space may hold: address
/// space reserved once, pages committed by the system as first written.
const BYTES_MAX: usize = 1 << 32;
const COUNT_MAX: usize = 1 << 28;

/// Where name `n` is: its first byte, and how many.
#[derive(Clone, Copy, Default)]
struct Place {
    start: u64,
    len: u64,
}

struct Space {
    /// The names' bytes.
    bytes: *mut u8,
    /// Each number's place, `COUNT_MAX` of them reserved.
    places: *mut Place,
    state: RefCell<State>,
}

#[derive(Default)]
struct State {
    /// The numbers made so far: each below it is a name, or free.
    count: u32,
    /// Bytes used, from the start.
    used: usize,
    /// Each number's: whether it is a name now (not free), and how many
    /// holders hold it.
    live: Vec<bool>,
    held: Vec<u32>,
    /// Each name by its text's hash: the number of that hash, or [`MANY`]
    /// where two names have one, their numbers then in `many`.
    index: ByHash<u32>,
    many: ByHash<Vec<u32>>,
    /// Numbers freed, to be made again; and the places of names freed, by
    /// length, to be written again by a name as long.
    free_numbers: Vec<u32>,
    free_bytes: HashMap<u64, Vec<u64>>,
}

/// A map keyed by a name's hash, which is its own hash: not hashed again
/// (by `fixpt_hash`'s SipHash, which a profile of loading the front end's
/// names found at 1.3% of a run).
type ByHash<V> = std::collections::HashMap<u64, V, std::hash::BuildHasherDefault<Hashed>>;

/// The hasher of [`ByHash`]: the key, as it is.
#[derive(Default)]
struct Hashed(u64);

impl std::hash::Hasher for Hashed {
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

/// In the index, where names of one hash are several (`State::many`).
const MANY: u32 = u32::MAX;

impl State {
    /// The numbers of the names of hash `h`.
    fn hashed(&self, h: u64) -> &[u32] {
        match self.index.get(&h) {
            None => &[],
            Some(&MANY) => &self.many[&h],
            Some(n) => std::slice::from_ref(n),
        }
    }

    /// The numbers of hash `h` made `ns`.
    fn set_hashed(&mut self, h: u64, ns: Vec<u32>) {
        self.many.remove(&h);
        match ns.as_slice() {
            [] => {
                self.index.remove(&h);
            }
            [n] => {
                self.index.insert(h, *n);
            }
            _ => {
                self.index.insert(h, MANY);
                self.many.insert(h, ns);
            }
        }
    }
}

/// `len` bytes of address space, readable and writable, zero; the process
/// stops if the system refuses them.
fn map(len: usize) -> *mut u8 {
    #[cfg(target_os = "linux")]
    let flags = libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_NORESERVE;
    #[cfg(not(target_os = "linux"))]
    let flags = libc::MAP_PRIVATE | libc::MAP_ANON;
    // SAFETY: an anonymous mapping, used only through its space.
    let p = unsafe { libc::mmap(std::ptr::null_mut(), len, libc::PROT_READ | libc::PROT_WRITE, flags, -1, 0) };
    assert!(p != libc::MAP_FAILED, "no address space for a heap's names ({len} bytes)");
    p as *mut u8
}

impl Drop for Space {
    fn drop(&mut self) {
        // SAFETY: the two mappings `map` made, of these lengths; nothing
        // borrows from them, as their space is being dropped.
        unsafe {
            libc::munmap(self.bytes as *mut libc::c_void, BYTES_MAX);
            libc::munmap(self.places as *mut libc::c_void, COUNT_MAX * std::mem::size_of::<Place>());
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
        Space { bytes: map(BYTES_MAX), places: map(COUNT_MAX * std::mem::size_of::<Place>()) as *mut Place, state: RefCell::default() }
    }

    /// Name `n`'s text, if it is a name now. The `&str` is the caller's to
    /// keep only while `n` is not freed: [`Owner::get`] and
    /// [`Holder::get`] bound it so.
    fn text(&self, n: u32) -> Option<&str> {
        let st = self.state.borrow();
        if !st.live.get(n as usize).copied().unwrap_or(false) {
            return None;
        }
        // SAFETY: `n` is below the count (it is live), so its place was
        // written when it was made and is not written while it is live.
        let p = unsafe { *self.places.add(n as usize) };
        // SAFETY: those bytes are the name's, copied from a `str`, within
        // `bytes`, and not written while the name is live: the module's
        // doc.
        Some(unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(self.bytes.add(p.start as usize), p.len as usize)) })
    }

    /// The number of the name `text`, if it is one.
    fn find(&self, text: &str) -> Option<u32> {
        let st = self.state.borrow();
        st.hashed(hash(text)).iter().copied().find(|&n| self.text_unchecked(n) == text)
    }

    /// Name `n`'s text, `n` live, the state borrowed by the caller.
    fn text_unchecked(&self, n: u32) -> &str {
        // SAFETY: as `text`'s; the caller knows `n` is live.
        unsafe {
            let p = *self.places.add(n as usize);
            std::str::from_utf8_unchecked(std::slice::from_raw_parts(self.bytes.add(p.start as usize), p.len as usize))
        }
    }

    /// The number of the name `text`: its own, made now if it had none.
    fn intern(&self, text: &str) -> u32 {
        if let Some(n) = self.find(text) {
            return n;
        }
        let mut st = self.state.borrow_mut();
        let len = text.len() as u64;
        // Where its bytes go: a freed name's as long, or past every byte.
        let start = match st.free_bytes.get_mut(&len).and_then(|v| v.pop()) {
            Some(s) => s,
            None => {
                let s = st.used as u64;
                assert!(st.used + text.len() <= BYTES_MAX, "a heap's names are full ({} bytes)", st.used);
                st.used += text.len();
                s
            }
        };
        let n = match st.free_numbers.pop() {
            Some(n) => n,
            None => {
                let n = st.count;
                assert!((n as usize) < COUNT_MAX, "a heap's names are full ({n} names)");
                st.count += 1;
                st.live.push(false);
                st.held.push(0);
                n
            }
        };
        // SAFETY: `start..start + len` is no live name's (past every byte
        // used, or a freed name's), and `n`'s place no live name's; both
        // within their mappings.
        unsafe {
            std::ptr::copy_nonoverlapping(text.as_ptr(), self.bytes.add(start as usize), text.len());
            *self.places.add(n as usize) = Place { start, len };
        }
        st.live[n as usize] = true;
        let h = hash(text);
        if !st.index.contains_key(&h) {
            st.index.insert(h, n);
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
    }

    /// Name `n` freed, its number and its bytes to be made again.
    fn free(&self, st: &mut State, n: u32) {
        let text = self.text_unchecked(n);
        let h = hash(text);
        let rest = st.hashed(h).iter().copied().filter(|&m| m != n).collect();
        st.set_hashed(h, rest);
        // SAFETY: `n` is live until now: its place as written.
        let p = unsafe { *self.places.add(n as usize) };
        st.live[n as usize] = false;
        st.free_numbers.push(n);
        st.free_bytes.entry(p.len).or_default().push(p.start);
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

    /// The number of the name `text`: its own, made now if it had none. It
    /// lives until a sweep frees it.
    pub fn intern(&self, text: &str) -> u32 {
        self.0.intern(text)
    }

    /// The number of the name `text`, if it is one; making none.
    pub fn find(&self, text: &str) -> Option<u32> {
        self.0.find(text)
    }

    /// [`intern`](Owner::intern) of each of `texts`, room made for them
    /// first: an image's, as it is read.
    pub fn intern_all<'t>(&self, texts: impl ExactSizeIterator<Item = &'t str>) -> Vec<u32> {
        self.0.reserve(texts.len());
        texts.map(|t| self.0.intern(t)).collect()
    }

    /// Name `n`, if it is one: as long as the owner is borrowed, no sweep
    /// frees it.
    pub fn get(&self, n: u32) -> Option<&str> {
        self.0.text(n)
    }

    /// How many numbers have been made: each name's is below it.
    pub fn count(&self) -> u32 {
        self.0.state.borrow().count
    }

    /// Every name not kept by `keep` and held by no holder, freed: how
    /// many.
    pub fn sweep(&mut self, mut keep: impl FnMut(u32) -> bool) -> usize {
        let mut st = self.0.state.borrow_mut();
        let mut freed = 0;
        for n in 0..st.count {
            if st.live[n as usize] && st.held[n as usize] == 0 && !keep(n) {
                self.0.free(&mut st, n);
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
    /// Whether it holds each number, by number; and the numbers it holds,
    /// in the order it took them.
    mine: Vec<bool>,
    order: Vec<u32>,
}

impl Holder {
    /// A holder of names of its own, which no heap owns: freed with it.
    pub fn new() -> Holder {
        Owner::new().holder()
    }

    /// The number of the name `text`, made if it had none, held.
    pub fn hold_text(&mut self, text: &str) -> u32 {
        let n = self.space.intern(text);
        self.take(n);
        n
    }

    /// The number of the name `text`, if it is one this holds.
    pub fn find(&self, text: &str) -> Option<u32> {
        self.space.find(text).filter(|&n| self.holds(n))
    }

    /// Name `n` held, if it is a name: whether it is.
    pub fn hold(&mut self, n: u32) -> bool {
        if self.space.text(n).is_none() {
            return false;
        }
        self.take(n);
        true
    }

    fn take(&mut self, n: u32) {
        if self.holds(n) {
            return;
        }
        let i = n as usize;
        if self.mine.len() <= i {
            self.mine.resize(i + 1, false);
        }
        self.mine[i] = true;
        self.order.push(n);
        self.space.state.borrow_mut().held[i] += 1;
    }

    /// Whether this holds name `n`.
    #[inline]
    pub fn holds(&self, n: u32) -> bool {
        self.mine.get(n as usize).copied().unwrap_or(false)
    }

    /// Name `n`, if this holds it: as long as this is borrowed, it holds
    /// it still, so no sweep frees it.
    #[inline]
    pub fn get(&self, n: u32) -> Option<&str> {
        if !self.holds(n) {
            return None;
        }
        self.space.text(n)
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
    pub fn held(&self) -> &[u32] {
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
            self.mine[n as usize] = false;
            st.held[n as usize] -= 1;
        }
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
        assert_eq!(o.get(o.count()), None);
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
            st.set_hashed(ha, vec![a, b]);
            st.index.remove(&hb);
        }
        assert_eq!(o.0.state.borrow().hashed(hash("a")), &[a, b]);
        assert_eq!(o.0.find("a"), Some(a));
        let mut h = o.holder();
        h.hold(b);
        o.sweep(|_| false);
        assert_eq!(o.0.state.borrow().hashed(hash("a")), &[b]);
        assert_eq!(o.get(b), Some("b"));
    }
}
