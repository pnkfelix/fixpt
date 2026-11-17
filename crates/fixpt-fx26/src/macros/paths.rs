//! A node's path in a form: its steps from the form's root, each `true` a
//! car and `false` a cdr, as a handle into a trie of every path made
//! (the user's, 2026-11-17). The `k`th item of a list is `k` cdrs and a car in, so
//! a path as a vector of its steps is as long as how far along a list it
//! is, and a map keyed by one hashed it whole at every node: a long
//! `begin`'s expansion took time quadratic in its length. A path here is
//! one number: a step from it is one lookup of the pair, equal paths are
//! the same number, and a map keyed by one hashes a word.
//!
//! The numbers are in-memory keys alone: one depends on which paths were
//! made before it, so nothing written, compared for order or hashed into a
//! name or a cache's key may use it. What needs the steps asks for them
//! ([`Path::steps`]; `sort_by_path` numbers them by a walk). The trie is the thread's, as the
//! expander that makes paths and the forms that hold them are: a path is
//! never sent to another thread.

use fixpt_hash::HashMap;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Path(u32);

/// Each path made: its parent and last step, and its length; and each
/// path by its parent and last step.
struct Trie {
    nodes: Vec<(u32, bool, u32)>,
    index: HashMap<(u32, bool), u32>,
}

thread_local! {
    static TRIE: std::cell::RefCell<Trie> = std::cell::RefCell::new(Trie { nodes: vec![(0, false, 0)], index: HashMap::default() });
}

impl Path {
    /// The empty path: a form's root.
    pub const ROOT: Path = Path(0);

    /// This path and one step more: the car (`true`) or the cdr.
    #[must_use]
    pub fn push(self, step: bool) -> Path {
        TRIE.with(|t| {
            let mut t = t.borrow_mut();
            if let Some(&p) = t.index.get(&(self.0, step)) {
                return Path(p);
            }
            let len = t.nodes[self.0 as usize].2 + 1;
            let p = u32::try_from(t.nodes.len()).expect("fewer paths than a u32 counts");
            t.nodes.push((self.0, step, len));
            t.index.insert((self.0, step), p);
            Path(p)
        })
    }

    /// This path and `steps` more, in order.
    #[must_use]
    pub fn extend(self, steps: &[bool]) -> Path {
        steps.iter().fold(self, |p, s| p.push(*s))
    }

    /// How many steps it has.
    pub fn len(self) -> usize {
        TRIE.with(|t| t.borrow().nodes[self.0 as usize].2 as usize)
    }

    pub fn is_empty(self) -> bool {
        self == Path::ROOT
    }

    /// Its last step and the path before it; none at the root.
    pub fn split_last(self) -> Option<(Path, bool)> {
        if self.is_empty() {
            return None;
        }
        TRIE.with(|t| {
            let (parent, step, _) = t.borrow().nodes[self.0 as usize];
            Some((Path(parent), step))
        })
    }

    /// Its first `n` steps' path.
    pub fn prefix(self, n: usize) -> Path {
        let mut p = self;
        for _ in n..self.len() {
            p = p.split_last().expect("longer than n").0;
        }
        p
    }

    /// Whether `p` is this path or a path before it.
    pub fn starts_with(self, p: Path) -> bool {
        let n = p.len();
        n <= self.len() && self.prefix(n) == p
    }

    /// Its steps, first first.
    pub fn steps(self) -> Vec<bool> {
        let mut out = Vec::with_capacity(self.len());
        let mut p = self;
        while let Some((q, s)) = p.split_last() {
            out.push(s);
            p = q;
        }
        out.reverse();
        out
    }
}
