//! The workspace's hash maps and sets: the standard ones, hashed by SipHash
//! as they are by default, but with no seed of each process's own. What
//! iterates one does it in the same order in every run, so what it makes
//! of that order (an image's lists, the order code is compiled in, and so
//! where it lands) is the same in every run, and in a debug and a release
//! build alike: the caches `fixpt prewarm` makes are the same bytes but for
//! their keys. The keys hashed are the heap's addresses and the program's
//! names, none an adversary's, so the seed bought nothing here.
//!
//! A map whose hasher was chosen for speed (a multiply a word, as
//! `fixpt-heap`'s `WordHasher`, `fixpt-fx26`'s `IdHasher`) names its own;
//! none is seeded either. `fixpt-tidy` holds that no other is used.

/// The hasher: SipHash-1-3 with fixed keys, the standard one's algorithm.
pub type Unseeded = std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher>;
/// A map hashed by [`Unseeded`].
pub type HashMap<K, V> = std::collections::HashMap<K, V, Unseeded>;
/// A set hashed by [`Unseeded`].
pub type HashSet<K> = std::collections::HashSet<K, Unseeded>;
