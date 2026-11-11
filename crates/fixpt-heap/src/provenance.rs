//! Where code a macro made comes from, one place for both front ends
//! (`docs/research/macro-provenance.md`, `TODO.md` §249): a *provenance*,
//! a chain of places, innermost first (the part's place in the macro's
//! template, then the use site of the expansion that made it, and out, to
//! a place in a text as written), each a place as both compilers write one
//! (`place_of`: a character, past its file's base, a billion times the
//! file's number in load order). A register word records, for such code,
//! the chain's *id*: an integer made from the chain's contents, so that
//! the two front ends, given the same chain, record the same integer, and
//! one id means the same chain in every process. A place written in a text
//! is not one: it stays as it is.
//!
//! Each heap keeps the chains of the ids its words hold ([`Provenance`]),
//! and each word that holds any by a weak reference: once every word that
//! held an id is found dead by a collection, its entry is let go; but an
//! immortal one (code that is never collected: in the static area, an
//! image's).

use std::collections::HashMap;

/// Where provenance ids start: past every file's places, and past the keys
/// the expander written in FX-26 gives the parts its templates make
/// ([`SOURCE_KEYS`]), within a fixnum.
pub const PROVENANCE_BASE: i64 = 1 << 52;
/// How many ids there are, from [`PROVENANCE_BASE`].
const ID_BITS: u32 = 50;
/// The keys the FX-26 expander gives a template's parts (`macros-procedural.fx`'s
/// `source-base`), which no compiler records once it has made them ids.
pub const SOURCE_KEYS: i64 = 1 << 50;

/// Whether place `p` is a provenance's id.
pub fn is_provenance(p: i64) -> bool {
    (PROVENANCE_BASE..PROVENANCE_BASE + (1 << ID_BITS)).contains(&p)
}

/// A provenance's id: FNV-1a of its places, each its eight bytes, in
/// [`ID_BITS`] bits, past [`PROVENANCE_BASE`]. The same in every process
/// and every build.
pub fn id_of(chain: &[i64]) -> i64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for p in chain {
        for b in p.to_le_bytes() {
            h ^= b as u64;
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    PROVENANCE_BASE + (h & ((1 << ID_BITS) - 1)) as i64
}

/// A heap's provenances: each id its words may hold, with its chain, and
/// whether it is immortal.
#[derive(Default, Clone, Debug)]
pub struct Provenance {
    /// Each id's chain, how many live words hold it, and whether it is
    /// immortal. One no word has held yet is kept (a compiler asked for it,
    /// its word not made yet).
    chains: HashMap<i64, Entry>,
    /// Each word holding ids, by its weak reference (`Heap::weak_add`), and
    /// the ids.
    holders: Vec<(usize, Vec<i64>)>,
}

#[derive(Clone, Debug)]
struct Entry {
    chain: Vec<i64>,
    held: usize,
    ever_held: bool,
    immortal: bool,
}

impl Entry {
    fn new(chain: &[i64], immortal: bool) -> Entry {
        Entry { chain: chain.to_vec(), held: 0, ever_held: false, immortal }
    }
}

impl Provenance {
    /// Chain `chain`'s id, the chain kept for it. Two chains of one id (not
    /// expected, at 50 bits) is said, in a debug build by failing: the
    /// first kept, never one taken silently for the other.
    pub fn id(&mut self, chain: &[i64]) -> i64 {
        let id = id_of(chain);
        match self.chains.get(&id) {
            Some(e) if e.chain != chain => {
                debug_assert!(false, "two provenances of id {id}: {:?} and {chain:?}", e.chain);
                eprintln!("fixpt: two provenances of id {id}: {:?} and {chain:?}; the first kept", e.chain);
            }
            Some(_) => {}
            None => {
                self.chains.insert(id, Entry::new(chain, false));
            }
        }
        id
    }

    /// The chain of id `id`, if this heap keeps it.
    pub fn chain(&self, id: i64) -> Option<&[i64]> {
        self.chains.get(&id).map(|e| e.chain.as_slice())
    }

    /// The written place `p` stands for: itself if it is no provenance, else
    /// its chain's last, the use in a text as written; none if its chain is
    /// not kept.
    pub fn written(&self, p: i64) -> Option<i64> {
        if !is_provenance(p) {
            return Some(p);
        }
        self.chain(p).and_then(|c| c.last().copied())
    }

    /// Id `id` with chain `chain`, as another heap kept it (a word copied
    /// from it): kept here too, immortal if `immortal`.
    pub fn keep(&mut self, id: i64, chain: &[i64], immortal: bool) {
        let e = self.chains.entry(id).or_insert_with(|| Entry::new(chain, immortal));
        e.immortal |= immortal;
    }

    /// The word of weak reference `weak` holds ids `ids` (each one kept
    /// here): counted, until a collection finds it dead ([`swept`]).
    pub fn hold(&mut self, weak: usize, ids: Vec<i64>) {
        for id in &ids {
            if let Some(e) = self.chains.get_mut(id) {
                e.held += 1;
                e.ever_held = true;
            }
        }
        self.holders.push((weak, ids));
    }

    /// After a collection, `alive` saying of each weak reference whether
    /// its word lives: the dead words' ids no longer held by them, and each
    /// id no word holds now, that one had held, let go, unless immortal.
    /// The dead words' weak references, to be released.
    pub fn swept(&mut self, alive: impl Fn(usize) -> bool) -> Vec<usize> {
        let mut released = Vec::new();
        let chains = &mut self.chains;
        self.holders.retain(|(weak, ids)| {
            if alive(*weak) {
                return true;
            }
            for id in ids {
                if let Some(e) = chains.get_mut(id) {
                    e.held = e.held.saturating_sub(1);
                }
            }
            released.push(*weak);
            false
        });
        if !released.is_empty() {
            chains.retain(|_, e| e.immortal || e.held > 0 || !e.ever_held);
        }
        released
    }

    /// Whether any is kept.
    pub fn is_empty(&self) -> bool {
        self.chains.is_empty()
    }

    /// How many are kept.
    pub fn len(&self) -> usize {
        self.chains.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_id_is_its_chain_s_and_kept() {
        let mut p = Provenance::default();
        let a = p.id(&[8_000_002_010, 42]);
        assert!(is_provenance(a));
        assert_eq!(a, id_of(&[8_000_002_010, 42]));
        assert_eq!(p.id(&[8_000_002_010, 42]), a);
        assert_ne!(p.id(&[42, 8_000_002_010]), a, "the order is the chain's");
        assert_eq!(p.chain(a), Some(&[8_000_002_010, 42][..]));
        assert_eq!(p.written(a), Some(42));
        assert_eq!(p.written(17), Some(17));
        assert!(!is_provenance(SOURCE_KEYS + 5) && !is_provenance(1_000_000_123));
    }

    #[test]
    fn a_collection_lets_go_what_no_word_holds_but_the_immortal() {
        let mut p = Provenance::default();
        let (a, b, d) = (p.id(&[1, 2]), p.id(&[3, 4]), p.id(&[7, 8]));
        let c = id_of(&[5, 6]);
        p.keep(c, &[5, 6], true);
        // Words 0 (holding a and b), 1 (b), 2 (c); d asked for, no word yet.
        p.hold(0, vec![a, b]);
        p.hold(1, vec![b]);
        p.hold(2, vec![c]);
        assert_eq!(p.swept(|w| w != 0), vec![0]);
        assert!(p.chain(a).is_none(), "held by the dead word alone");
        assert!(p.chain(b).is_some(), "still held by word 1");
        assert!(p.chain(d).is_some(), "never held: its word is to come");
        assert_eq!(p.swept(|w| w == 1), vec![2]);
        assert!(p.chain(c).is_some(), "immortal");
        assert_eq!(p.swept(|_| false), vec![1]);
        assert!(p.chain(b).is_none());
    }
}
