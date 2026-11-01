//! Types as heap data (`docs/research/heap-types.md`, `TODO.md` §202): a
//! **rep** is a type as a graph of nodes, the form every boundary between
//! type stores crosses as it is (a `stage`'s checker, run-time evidence, a
//! `.fasl`, a heap dump), not as printed text read and checked again.
//!
//! This crate knows nothing of the type language: a node is a head (a
//! name: `subr`, `poly`, `ref`, …) and its operands, and what heads mean,
//! and which operands they take, is the checkers' (each one's export and
//! import, `fixpt-fx26`'s `reps.rs`). What it does is what every rep
//! needs: its canonical form, its digest, its binary form, its validation,
//! its readable form, and its place in the heap.
//!
//! - **Nodes** refer to each other by index, so a recursive type is a cycle
//!   of indices and a rep is acyclic data.
//! - **Binders** are a node's, numbered: a bound variable is its binder's
//!   node and its place there ([`Arg::Bound`]), so that types alike but for
//!   the names of their variables have one rep. The names are kept, for
//!   printing, and are no part of a rep's identity.
//! - **Holes** are the variables free in a type, numbered ([`Arg::Hole`]):
//!   what evidence fills.
//! - **Constants** are abstract and generative types ([`Const`]), each
//!   known by its key, not its name (`heap-types.md`, "Abstract types, and
//!   what their identity depends on").
//!
//! A rep built by [`Builder`] is canonical: its minimal graph (equal
//! subgraphs, cycles included, one node), numbered as a walk from the root
//! first meets them; holes and constants numbered so too. Two reps of one
//! type are then equal, and have one [`Rep::digest`].

use std::collections::HashMap;

pub mod binary;
pub mod fill;
pub mod heap;
pub mod text;

/// A type, as a rep. Canonical when made by [`Builder::finish`] (or read
/// by [`binary::decode`] or [`text::read`], which finish one).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rep {
    /// The nodes; the root first.
    pub nodes: Vec<Node>,
    /// The names nodes use (heads, binders, symbols), each once.
    pub names: Vec<String>,
    /// Each hole's name, for printing; a hole is known by its number.
    pub holes: Vec<String>,
    /// The constants the type names.
    pub consts: Vec<Const>,
}

/// A node: its head, the names of the variables it binds, and its operands.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Node {
    /// Its head's name, an index into [`Rep::names`].
    pub head: u32,
    /// The names of the variables it binds, for printing (indices into
    /// [`Rep::names`]); a variable is known by its place here.
    pub binders: Vec<u32>,
    pub args: Vec<Arg>,
    /// Whether its operands are a set, their order no part of what it is
    /// (an effect's atoms, a union's members): in a canonical rep, in an
    /// order of their own (`canonical`), whatever order they were given in.
    pub set: bool,
}

/// An operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Arg {
    /// Another node.
    Node(u32),
    /// The variable bound at place `pos` of node `binder`, which is on every
    /// path from the root to here.
    Bound { binder: u32, pos: u32 },
    /// A free variable, by its number ([`Rep::holes`]).
    Hole(u32),
    /// A constant, by its number ([`Rep::consts`]).
    Const(u32),
    /// A name, an index into [`Rep::names`]: a label, a base type's.
    Sym(u32),
    Int(i64),
    Flag(bool),
}

/// An abstract or a generative type: what identifies it, its key; its
/// name, for printing; and its kind, as its checker names kinds.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Const {
    pub key: u64,
    pub name: String,
    pub kind: String,
}

impl Rep {
    /// The root.
    pub fn root(&self) -> u32 {
        0
    }

    pub fn name(&self, i: u32) -> &str {
        &self.names[i as usize]
    }

    /// A digest of what the type is: its nodes, as their names (not their
    /// indices) and their operands, constants by key; not the names of
    /// binders or holes. Equal for equal reps, in any process (FNV-1a).
    pub fn digest(&self) -> u64 {
        let mut h = Fnv::new();
        h.u64(self.nodes.len() as u64);
        for n in &self.nodes {
            h.str(self.name(n.head));
            h.byte(n.set as u8);
            h.u64(n.binders.len() as u64);
            h.u64(n.args.len() as u64);
            for a in &n.args {
                match *a {
                    Arg::Node(i) => h.tagged(0, i as u64),
                    Arg::Bound { binder, pos } => {
                        h.tagged(1, binder as u64);
                        h.u64(pos as u64);
                    }
                    Arg::Hole(i) => h.tagged(2, i as u64),
                    Arg::Const(i) => h.tagged(3, self.consts[i as usize].key),
                    Arg::Sym(i) => {
                        h.u64(4);
                        h.str(self.name(i));
                    }
                    Arg::Int(k) => h.tagged(5, k as u64),
                    Arg::Flag(b) => h.tagged(6, b as u64),
                }
            }
        }
        h.u64(self.holes.len() as u64);
        h.finish()
    }

    /// Whether this rep is well formed (`heap-types.md`, "The two
    /// checkers"): every index in range, every bound variable's binder one
    /// with a place for it, and on every path from the root to its use.
    /// Not whether its heads mean anything: that is its checker's to say,
    /// as it imports it.
    pub fn validate(&self) -> Result<(), String> {
        let n = self.nodes.len();
        if n == 0 {
            return Err("a rep with no nodes".into());
        }
        let name_ok = |i: u32| (i as usize) < self.names.len();
        for (k, node) in self.nodes.iter().enumerate() {
            if !name_ok(node.head) || !node.binders.iter().all(|&b| name_ok(b)) {
                return Err(format!("node {k}: a name out of range"));
            }
            for a in &node.args {
                let ok = match *a {
                    Arg::Node(i) => (i as usize) < n,
                    Arg::Bound { binder, pos } => (binder as usize) < n && (pos as usize) < self.nodes[binder as usize].binders.len(),
                    Arg::Hole(i) => (i as usize) < self.holes.len(),
                    Arg::Const(i) => (i as usize) < self.consts.len(),
                    Arg::Sym(i) => name_ok(i),
                    Arg::Int(_) | Arg::Flag(_) => true,
                };
                if !ok {
                    return Err(format!("node {k}: an operand out of range, {a:?}"));
                }
            }
        }
        // What binders each node needs from the nodes above it: those its
        // bound variables name, and its operands need, less itself. To a
        // fixed point, for cycles. The root needs none just when every
        // binder is on every path to its uses.
        let mut needs: Vec<Vec<u32>> = vec![Vec::new(); n];
        loop {
            let mut changed = false;
            for k in (0..n).rev() {
                let mut want: Vec<u32> = Vec::new();
                for a in &self.nodes[k].args {
                    match *a {
                        Arg::Bound { binder, .. } => want.push(binder),
                        Arg::Node(i) => want.extend(needs[i as usize].iter().copied()),
                        _ => {}
                    }
                }
                want.retain(|&b| b as usize != k);
                want.sort_unstable();
                want.dedup();
                if want != needs[k] {
                    needs[k] = want;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        match needs[0].first() {
            None => Ok(()),
            Some(b) => Err(format!("a variable of node {b} used where node {b} does not bind it")),
        }
    }
}

/// FNV-1a, 64 bits: the same in every process and every Rust, as
/// `std`'s hasher is not promised to be.
struct Fnv(u64);

impl Fnv {
    fn new() -> Fnv {
        Fnv(0xcbf2_9ce4_8422_2325)
    }
    fn byte(&mut self, b: u8) {
        self.0 = (self.0 ^ b as u64).wrapping_mul(0x0100_0000_01b3);
    }
    fn u64(&mut self, v: u64) {
        v.to_le_bytes().iter().for_each(|b| self.byte(*b));
    }
    fn tagged(&mut self, tag: u8, v: u64) {
        self.byte(tag);
        self.u64(v);
    }
    fn str(&mut self, s: &str) {
        self.u64(s.len() as u64);
        s.bytes().for_each(|b| self.byte(b));
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

/// A digest of `bytes` (FNV-1a), for keys made of what identifies a
/// constant (a definition's stamp and a label, say).
pub fn digest_bytes(bytes: &[u8]) -> u64 {
    let mut h = Fnv::new();
    bytes.iter().for_each(|b| h.byte(*b));
    h.finish()
}

/// A generative type's key, for now (`heap-types.md`, "Step 1, done"): its
/// name and its place in its checker's table, which both checkers number
/// alike; so within a session. Both checkers' exports use it, so that their
/// reps of one type agree.
pub fn generative_key(name: &str, which: u32) -> u64 {
    digest_bytes(format!("generative {name} {which}").as_bytes())
}

/// How a rep is made: nodes added, a slot reserved for a node not yet made
/// (a recursive type's, which its own operands name) and filled later; then
/// [`finish`](Builder::finish)ed, canonical.
#[derive(Default)]
pub struct Builder {
    nodes: Vec<Option<Node>>,
    names: Vec<String>,
    name_ids: HashMap<String, u32>,
    holes: Vec<String>,
    consts: Vec<Const>,
    const_ids: HashMap<u64, u32>,
}

/// A finished rep, and where each hole and constant the builder numbered
/// went: `holes[i]` the rep's number of the builder's hole `i`, none if the
/// type does not name it.
pub struct Finished {
    pub rep: Rep,
    pub holes: Vec<Option<u32>>,
    pub consts: Vec<Option<u32>>,
}

impl Builder {
    pub fn new() -> Builder {
        Builder::default()
    }

    /// Name `s`'s index.
    pub fn name(&mut self, s: &str) -> u32 {
        if let Some(&i) = self.name_ids.get(s) {
            return i;
        }
        let i = self.names.len() as u32;
        self.names.push(s.to_string());
        self.name_ids.insert(s.to_string(), i);
        i
    }

    /// A new hole, named `name`.
    pub fn hole(&mut self, name: &str) -> Arg {
        self.holes.push(name.to_string());
        Arg::Hole(self.holes.len() as u32 - 1)
    }

    /// Constant `c`, once for its key.
    pub fn konst(&mut self, c: Const) -> Arg {
        if let Some(&i) = self.const_ids.get(&c.key) {
            return Arg::Const(i);
        }
        let i = self.consts.len() as u32;
        self.const_ids.insert(c.key, i);
        self.consts.push(c);
        Arg::Const(i)
    }

    /// A slot for a node to be [`fill`](Builder::fill)ed.
    pub fn reserve(&mut self) -> u32 {
        self.nodes.push(None);
        self.nodes.len() as u32 - 1
    }

    pub fn fill(&mut self, slot: u32, head: &str, binders: &[&str], args: Vec<Arg>) {
        let node = Node { head: self.name(head), binders: binders.iter().map(|b| self.name(b)).collect(), args, set: false };
        self.nodes[slot as usize] = Some(node);
    }

    /// The same, a set node: its operands' order no part of it.
    pub fn fill_set(&mut self, slot: u32, head: &str, args: Vec<Arg>) {
        let node = Node { head: self.name(head), binders: Vec::new(), args, set: true };
        self.nodes[slot as usize] = Some(node);
    }

    /// A set node, its slot.
    pub fn add_set(&mut self, head: &str, args: Vec<Arg>) -> u32 {
        let slot = self.reserve();
        self.fill_set(slot, head, args);
        slot
    }

    /// Whether slot `slot` is filled.
    pub(crate) fn is_filled(&self, slot: u32) -> bool {
        self.nodes.get(slot as usize).is_some_and(Option::is_some)
    }

    /// The node in slot `slot`, if filled.
    pub(crate) fn node(&self, slot: u32) -> Option<&Node> {
        self.nodes.get(slot as usize)?.as_ref()
    }

    /// Name `i`.
    pub(crate) fn name_of(&self, i: u32) -> &str {
        &self.names[i as usize]
    }

    /// A node, its slot.
    pub fn add(&mut self, head: &str, binders: &[&str], args: Vec<Arg>) -> u32 {
        let slot = self.reserve();
        self.fill(slot, head, binders, args);
        slot
    }

    /// The rep whose root is node `root`, canonical: the minimal graph of
    /// what `root` reaches, numbered from it. Or why not: a slot never
    /// filled.
    pub fn finish(self, root: u32) -> Result<Finished, String> {
        let nodes: Vec<Node> = self.nodes.into_iter().enumerate().map(|(k, n)| n.ok_or(format!("slot {k} never filled"))).collect::<Result<_, _>>()?;
        canonical(nodes, root, self.names, self.holes, self.consts)
    }
}

/// The canonical rep of `root` in `nodes` (`Builder::finish`).
fn canonical(nodes: Vec<Node>, root: u32, names: Vec<String>, holes: Vec<String>, consts: Vec<Const>) -> Result<Finished, String> {
    let n = nodes.len();
    if root as usize >= n {
        return Err("no root".into());
    }
    let edges = |node: &Node| -> Vec<u32> {
        node.args
            .iter()
            .filter_map(|a| match *a {
                Arg::Node(i) => Some(i),
                Arg::Bound { binder, .. } => Some(binder),
                _ => None,
            })
            .collect()
    };
    for node in &nodes {
        if edges(node).iter().any(|&i| i as usize >= n) {
            return Err("an operand names no node".into());
        }
    }
    // An operand's key, given what each node's is (`of`): a node's and a
    // binder's by theirs; the rest by what they are, a hole by its number
    // if `holes` (within this rep, two holes are two variables) else by
    // none (for an order that is the same whatever the holes' numbers).
    let arg_key = |a: &Arg, of: &dyn Fn(u32) -> u64, holes_by_number: bool| -> Vec<u64> {
        match *a {
            Arg::Node(i) => vec![0, of(i)],
            Arg::Bound { binder, pos } => vec![1, of(binder), pos as u64],
            Arg::Hole(i) => vec![2, if holes_by_number { i as u64 } else { 0 }],
            Arg::Const(i) => vec![3, consts[i as usize].key],
            Arg::Sym(i) => vec![4, digest_bytes(names[i as usize].as_bytes())],
            Arg::Int(k) => vec![5, k as u64],
            Arg::Flag(b) => vec![6, b as u64],
        }
    };
    // A node's key: its own parts (not its binders' names), then its
    // operands' keys, sorted if it is a set.
    let node_key = |node: &Node, of: &dyn Fn(u32) -> u64, holes_by_number: bool| -> Vec<u64> {
        let mut key = vec![digest_bytes(names[node.head as usize].as_bytes()), node.binders.len() as u64, node.args.len() as u64, node.set as u64];
        let mut args: Vec<Vec<u64>> = node.args.iter().map(|a| arg_key(a, of, holes_by_number)).collect();
        if node.set {
            args.sort();
        }
        args.into_iter().for_each(|a| key.extend(a));
        key
    };
    // The minimal graph: nodes in one class are equal, refined from one
    // class by their keys to a fixed point.
    let mut class: Vec<usize> = vec![0; n];
    let mut count = 1;
    loop {
        let keys: Vec<Vec<u64>> = nodes.iter().map(|node| node_key(node, &|i| class[i as usize] as u64, true)).collect();
        let next = numbered(keys.into_iter());
        let c = distinct(&next);
        class = next;
        if c == count {
            break;
        }
        count = c;
    }
    // What orders a set's operands: a digest of each class's structure,
    // refined round by round (as Weisfeiler and Leman's test), which does
    // not depend on how the nodes were numbered, nor the holes; ties, the
    // operands' given order.
    let mut hash: Vec<u64> = vec![0; n];
    let mut seen_classes = 0;
    for _ in 0..=n {
        let next: Vec<u64> = nodes.iter().map(|node| digest_words(&node_key(node, &|i| hash[i as usize], false))).collect();
        let classes = distinct(&numbered(next.iter()));
        hash = next;
        if classes == seen_classes {
            break;
        }
        seen_classes = classes;
    }
    let order_args = |node: &Node| -> Vec<Arg> {
        let mut args = node.args.clone();
        if node.set {
            args.sort_by_cached_key(|a| arg_key(a, &|i| hash[i as usize], false));
        }
        args
    };
    // Numbered as a walk from the root first meets each class, operands in
    // order (a set's in its order above); holes and constants as it first
    // meets them.
    let mut first: HashMap<usize, u32> = HashMap::new();
    let mut order: Vec<usize> = Vec::new();
    let mut stack = vec![root as usize];
    while let Some(k) = stack.pop() {
        let c = class[k];
        if first.contains_key(&c) {
            continue;
        }
        first.insert(c, order.len() as u32);
        order.push(k);
        let ordered = Node { args: order_args(&nodes[k]), ..nodes[k].clone() };
        stack.extend(edges(&ordered).iter().rev().map(|&i| i as usize));
    }
    let mut new_names: Vec<String> = Vec::new();
    let mut name_of: HashMap<u32, u32> = HashMap::new();
    let mut rename = |i: u32| *name_of.entry(i).or_insert_with(|| {
        new_names.push(names[i as usize].clone());
        new_names.len() as u32 - 1
    });
    let (mut hole_of, mut new_holes) = (vec![None; holes.len()], Vec::new());
    let (mut const_of, mut new_consts) = (vec![None; consts.len()], Vec::new());
    let mut out = Vec::with_capacity(order.len());
    for &k in &order {
        let node = &nodes[k];
        let head = rename(node.head);
        let binders = node.binders.iter().map(|&b| rename(b)).collect();
        let args = order_args(node)
            .iter()
            .map(|a| match *a {
                Arg::Node(i) => Arg::Node(first[&class[i as usize]]),
                Arg::Bound { binder, pos } => Arg::Bound { binder: first[&class[binder as usize]], pos },
                Arg::Hole(i) => Arg::Hole(*hole_of[i as usize].get_or_insert_with(|| {
                    new_holes.push(holes[i as usize].clone());
                    new_holes.len() as u32 - 1
                })),
                Arg::Const(i) => Arg::Const(*const_of[i as usize].get_or_insert_with(|| {
                    new_consts.push(consts[i as usize].clone());
                    new_consts.len() as u32 - 1
                })),
                Arg::Sym(i) => Arg::Sym(rename(i)),
                other => other,
            })
            .collect();
        out.push(Node { head, binders, args, set: node.set });
    }
    let rep = Rep { nodes: out, names: new_names, holes: new_holes, consts: new_consts };
    rep.validate()?;
    Ok(Finished { rep, holes: hole_of, consts: const_of })
}

/// A digest of `words` (FNV-1a).
fn digest_words(words: &[u64]) -> u64 {
    let mut h = Fnv::new();
    words.iter().for_each(|w| h.u64(*w));
    h.finish()
}

/// Each of `keys` numbered by its first occurrence among them.
fn numbered<K: std::hash::Hash + Eq>(keys: impl Iterator<Item = K>) -> Vec<usize> {
    let mut seen: HashMap<K, usize> = HashMap::new();
    keys.map(|k| {
        let n = seen.len();
        *seen.entry(k).or_insert(n)
    })
    .collect()
}

fn distinct(class: &[usize]) -> usize {
    class.iter().max().map_or(0, |m| m + 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `(poly {r} (ref int r))`, its binder named `name`.
    fn poly_ref(name: &str) -> Rep {
        let mut b = Builder::new();
        let int = b.add("base", &[], vec![]);
        let int_name = b.name("int");
        b.fill(int, "base", &[], vec![Arg::Sym(int_name)]);
        let poly = b.reserve();
        let r = b.add("ref", &[], vec![Arg::Node(int), Arg::Bound { binder: poly, pos: 0 }]);
        b.fill(poly, "poly", &[name], vec![Arg::Node(r)]);
        b.finish(poly).expect("finishes").rep
    }

    #[test]
    fn types_alike_but_for_their_variables_names_are_one_rep() {
        let (a, b) = (poly_ref("r"), poly_ref("s"));
        assert_eq!(a.digest(), b.digest());
        assert_eq!(a.nodes, b.nodes);
    }

    #[test]
    fn a_cycle_and_its_unrolling_are_one_rep() {
        // `(mu t (pairof int t))` and the same unrolled once.
        let once = {
            let mut b = Builder::new();
            let int = b.add("base", &[], vec![]);
            let p = b.reserve();
            b.fill(p, "pairof", &[], vec![Arg::Node(int), Arg::Node(p)]);
            b.finish(p).expect("finishes").rep
        };
        let twice = {
            let mut b = Builder::new();
            let int = b.add("base", &[], vec![]);
            let p = b.reserve();
            let q = b.add("pairof", &[], vec![Arg::Node(int), Arg::Node(p)]);
            b.fill(p, "pairof", &[], vec![Arg::Node(int), Arg::Node(q)]);
            b.finish(p).expect("finishes").rep
        };
        assert_eq!(once.nodes.len(), 2);
        assert_eq!(once.digest(), twice.digest());
    }

    #[test]
    fn a_sets_operands_in_any_order_are_one_rep() {
        let build = |order: [&str; 3]| {
            let mut b = Builder::new();
            let atoms: Vec<Arg> = order.iter().map(|h| Arg::Node(b.add(h, &[], vec![]))).collect();
            let set = b.add_set("effect", atoms);
            b.finish(set).expect("finishes").rep
        };
        let (a, c) = (build(["spin", "stage", "nondet"]), build(["nondet", "spin", "stage"]));
        assert_eq!(a, c);
        assert_eq!(a.digest(), c.digest());
    }

    #[test]
    fn a_variable_outside_its_binder_is_not_well_formed() {
        // `(pairof (poly {r} int) r)`: `r` used outside the `poly`.
        let names = ["pairof", "poly", "base", "r"].map(String::from).to_vec();
        let node = |head, binders: Vec<u32>, args| Node { head, binders, args, set: false };
        let rep = Rep {
            nodes: vec![
                node(0, vec![], vec![Arg::Node(1), Arg::Bound { binder: 1, pos: 0 }]),
                node(1, vec![3], vec![Arg::Node(2)]),
                node(2, vec![], vec![]),
            ],
            names,
            holes: Vec::new(),
            consts: Vec::new(),
        };
        assert!(rep.validate().is_err());
    }
}
