//! Evidence filling a rep's holes (`heap-types.md`, step 3): a graph
//! substitution, not a textual one.
//!
//! A piece of evidence is a rep whose root is an `evidence` node of one
//! operand, what it is evidence of: a type, a region, or an effect (a set
//! node, `&effect`). Filling a hole puts that operand where the hole was;
//! where the hole is a member of a set whose head the evidence's set has
//! too (an effect variable among an effect's atoms), the evidence's
//! members join the set instead, since a set within a set of its kind is
//! no type's: `(maxeff e (io stdout))`, `e` given `(maxeff (read @r) (io
//! stdin))`, is `(maxeff (read @r) (io stdin) (io stdout))`. A member then
//! in the set twice is there once ([`dedup`]), so that a type filled and
//! the same type exported are one rep. And where a variable's occurrence is
//! a node of its own around its hole (a type variable's, `var`, in the
//! checkers' reps), that node is what the evidence takes the place of.

use crate::{Arg, Builder, Const, Rep};

/// The head of a piece of evidence's root.
pub const EVIDENCE: &str = "evidence";

/// `rep` with each hole named in `given` filled with its evidence, a node
/// of head `occurrence` whose one operand is such a hole the evidence too;
/// the holes not named left holes. Or why not: a piece of evidence that is
/// not one.
pub fn fill(rep: &Rep, given: &[(&str, &Rep)], occurrence: &str) -> Result<Rep, String> {
    let mut b = Builder::new();
    let base = copy_nodes(&mut b, rep);
    // Each piece of evidence copied once, and what it is evidence of.
    let mut of: Vec<Option<Arg>> = Vec::with_capacity(rep.holes.len());
    let mut copied: Vec<Option<Arg>> = vec![None; given.len()];
    for name in &rep.holes {
        let Some(g) = given.iter().position(|(n, _)| n == name) else {
            of.push(None);
            continue;
        };
        if copied[g].is_none() {
            let e = given[g].1;
            let root = &e.nodes[e.root() as usize];
            if e.name(root.head) != EVIDENCE || root.args.len() != 1 {
                return Err(format!("the evidence of `{name}` is no evidence"));
            }
            let at = copy_nodes(&mut b, e);
            // Its root, which nothing filled names: left out of the rep.
            b.fill(at + e.root(), EVIDENCE, &[], Vec::new());
            copied[g] = Some(map_arg(&mut b, e, at, root.args[0], &mut Vec::new(), true));
        }
        of.push(copied[g]);
    }
    // An occurrence of a variable filled is its filler.
    let alias: Vec<Option<Arg>> = rep
        .nodes
        .iter()
        .map(|n| match n.args[..] {
            [Arg::Hole(h)] if rep.name(n.head) == occurrence && !n.set => of[h as usize],
            _ => None,
        })
        .collect();
    let root = match alias[rep.root() as usize] {
        Some(Arg::Node(i)) => i,
        Some(_) => return Err("a variable's evidence is a variable".into()),
        None => base + rep.root(),
    };
    // Then the rep's own nodes, each hole filled.
    let mut own_holes = Vec::new();
    for (k, node) in rep.nodes.iter().enumerate() {
        let mut args = Vec::with_capacity(node.args.len());
        for &a in &node.args {
            match a {
                Arg::Hole(h) if of[h as usize].is_some() => {
                    let filler = of[h as usize].expect("filled");
                    match spliced(&b, node.set, rep.name(node.head), filler) {
                        Some(members) => args.extend(members),
                        None => args.push(filler),
                    }
                }
                Arg::Node(i) if alias[i as usize].is_some() => args.push(alias[i as usize].expect("aliased")),
                other => args.push(map_arg(&mut b, rep, base, other, &mut own_holes, false)),
            }
        }
        let binders: Vec<&str> = node.binders.iter().map(|&n| rep.name(n)).collect();
        let head = rep.name(node.head).to_string();
        if node.set {
            b.fill_set(base + k as u32, &head, args);
        } else {
            b.fill(base + k as u32, &head, &binders, args);
        }
    }
    dedup(b.finish(root)?.rep)
}

/// Reserve a slot for each of `rep`'s nodes, in order; the first's slot.
/// Their contents are filled by [`fill`], or as they are first met for
/// evidence (`fill_once`).
fn copy_nodes(b: &mut Builder, rep: &Rep) -> u32 {
    let base = b.reserve();
    for _ in 1..rep.nodes.len() {
        b.reserve();
    }
    base
}

/// Operand `a` of `rep` (copied at slot `base`) as `b`'s: a node and a
/// binder moved by `base`, a hole one of `b`'s (once for each of `rep`'s,
/// `holes`), a constant and a name by what they are. A node of a piece of
/// `evidence` is copied as it is first met.
fn map_arg(b: &mut Builder, rep: &Rep, base: u32, a: Arg, holes: &mut Vec<Option<Arg>>, evidence: bool) -> Arg {
    match a {
        Arg::Node(i) => {
            if evidence {
                fill_once(b, rep, base, i, holes);
            }
            Arg::Node(base + i)
        }
        Arg::Bound { binder, pos } => Arg::Bound { binder: base + binder, pos },
        Arg::Hole(h) => {
            if holes.len() <= h as usize {
                holes.resize(h as usize + 1, None);
            }
            *holes[h as usize].get_or_insert_with(|| b.hole(&rep.holes[h as usize]))
        }
        Arg::Const(c) => {
            let k = &rep.consts[c as usize];
            b.konst(Const { key: k.key, name: k.name.clone(), kind: k.kind.clone() })
        }
        Arg::Sym(s) => Arg::Sym(b.name(rep.name(s))),
        other => other,
    }
}

/// Node `i` of a piece of evidence `rep`, copied at `base + i`, if it is not
/// yet: its operands mapped, the nodes they name too.
fn fill_once(b: &mut Builder, rep: &Rep, base: u32, i: u32, holes: &mut Vec<Option<Arg>>) {
    if b.is_filled(base + i) {
        return;
    }
    let node = &rep.nodes[i as usize];
    let head = rep.name(node.head).to_string();
    let binders: Vec<String> = node.binders.iter().map(|&n| rep.name(n).to_string()).collect();
    // Filled before its operands, so that a cycle back to it ends.
    b.fill(base + i, &head, &[], Vec::new());
    let args: Vec<Arg> = node.args.iter().map(|&a| map_arg(b, rep, base, a, holes, true)).collect();
    let binders: Vec<&str> = binders.iter().map(String::as_str).collect();
    if node.set {
        b.fill_set(base + i, &head, args);
    } else {
        b.fill(base + i, &head, &binders, args);
    }
}

/// Where a hole is a member of a set of head `head`, and its filler a set
/// node of that head too: the filler's members, which join the set.
fn spliced(b: &Builder, set: bool, head: &str, filler: Arg) -> Option<Vec<Arg>> {
    let Arg::Node(i) = filler else { return None };
    let node = b.node(i)?;
    (set && node.set && b.name_of(node.head) == head).then(|| node.args.clone())
}

/// Reps `reps` as one, its root a node of head `head` whose operands are
/// their roots, in order: what they share there once, as its canonical form
/// finds it (a `.fasl`'s definitions' types, `heap-types.md`, step 5).
pub fn combine(head: &str, reps: &[&Rep]) -> Result<Rep, String> {
    let mut b = Builder::new();
    let mut roots = Vec::with_capacity(reps.len());
    for r in reps {
        let base = copy_nodes(&mut b, r);
        roots.push(map_arg(&mut b, r, base, Arg::Node(r.root()), &mut Vec::new(), true));
    }
    let root = b.add(head, &[], roots);
    Ok(b.finish(root)?.rep)
}

/// The part of `rep` at node `node`, as a rep of its own; a piece of
/// evidence of it (its root an [`EVIDENCE`] node) if `as_evidence` (an
/// effect, which no type is). Or why not: a part naming a variable bound
/// outside it.
pub fn part(rep: &Rep, node: u32, as_evidence: bool) -> Result<Rep, String> {
    let mut b = Builder::new();
    let base = copy_nodes(&mut b, rep);
    let at = map_arg(&mut b, rep, base, Arg::Node(node), &mut Vec::new(), true);
    let Arg::Node(root) = at else { return Err("no part".into()) };
    let root = if as_evidence { b.add(EVIDENCE, &[], vec![Arg::Node(root)]) } else { root };
    // The rep's nodes the part does not reach, left out: filled with what
    // they are, as nothing there names them.
    for k in 0..rep.nodes.len() as u32 {
        if !b.is_filled(base + k) {
            b.fill(base + k, EVIDENCE, &[], Vec::new());
        }
    }
    Ok(b.finish(root)?.rep)
}

/// `rep` with each set's members each there once, made canonical again,
/// until none is there twice: two members equal once canonical (a member
/// the evidence brought and one the set had) are one.
pub fn dedup(mut rep: Rep) -> Result<Rep, String> {
    loop {
        let twice = rep.nodes.iter().any(|n| n.set && (1..n.args.len()).any(|i| n.args[..i].contains(&n.args[i])));
        if !twice {
            return Ok(rep);
        }
        let mut b = Builder::new();
        let base = copy_nodes(&mut b, &rep);
        let mut holes = Vec::new();
        for (k, node) in rep.nodes.iter().enumerate() {
            let mut args: Vec<Arg> = Vec::new();
            for &a in &node.args {
                if !(node.set && args.contains(&a)) {
                    args.push(a);
                }
            }
            let args: Vec<Arg> = args.into_iter().map(|a| map_arg(&mut b, &rep, base, a, &mut holes, false)).collect();
            let head = rep.name(node.head).to_string();
            let binders: Vec<&str> = node.binders.iter().map(|&n| rep.name(n)).collect();
            if node.set {
                b.fill_set(base + k as u32, &head, args);
            } else {
                b.fill(base + k as u32, &head, &binders, args);
            }
        }
        rep = b.finish(base + rep.root())?.rep;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::text;

    fn rep(s: &str) -> Rep {
        text::read(s).unwrap_or_else(|e| panic!("{s}: {e}"))
    }

    /// `e`'s evidence, an effect, joins the effect `e` is a member of.
    #[test]
    fn an_effect_given_joins_the_effect_it_is_in() {
        let checked = rep("(subr (native) (&effect ?0:e (io stdout)) (params) (base int))");
        let given = rep("(evidence (&effect (read (rconst r)) (io stdin)))");
        let filled = fill(&checked, &[("e", &given)], "var").expect("fills");
        let want = rep("(subr (native) (&effect (read (rconst r)) (io stdin) (io stdout)) (params) (base int))");
        assert_eq!(filled, want, "{}", text::write(&filled));
    }

    /// A member the evidence brings that the set has already is there once.
    #[test]
    fn a_member_given_twice_is_there_once() {
        let checked = rep("(subr (native) (&effect ?0:e (io stdout)) (params) (base int))");
        let given = rep("(evidence (&effect (io stdout)))");
        let filled = fill(&checked, &[("e", &given)], "var").expect("fills");
        assert_eq!(filled, rep("(subr (native) (&effect (io stdout)) (params) (base int))"));
    }

    /// A type's hole takes a type, which may have holes of its own; a hole
    /// given nothing is left.
    #[test]
    fn a_type_given_takes_the_holes_place() {
        let checked = rep("(pairof ?0:t ?1:u (frozen #t) #t)");
        let given = rep("(evidence (ref ?0:v (rconst r)))");
        let filled = fill(&checked, &[("t", &given)], "var").expect("fills");
        assert_eq!(filled, rep("(pairof (ref ?0:v (rconst r)) ?1:u (frozen #t) #t)"), "{}", text::write(&filled));
        assert_eq!(filled.holes, ["u", "v"], "numbered as the walk from the root meets them");
    }

    /// A type variable's occurrence, a node around its hole, is what a type
    /// given takes the place of.
    #[test]
    fn a_variables_occurrence_is_its_evidence() {
        let checked = rep("(subr (native) (&effect) (params (var ?0:t)) (var ?0:t))");
        let given = rep("(evidence (base int))");
        let filled = fill(&checked, &[("t", &given)], "var").expect("fills");
        assert_eq!(filled, rep("(subr (native) (&effect) (params (base int)) (base int))"), "{}", text::write(&filled));
    }

    /// What reps combined share is there once.
    #[test]
    fn reps_combined_share_what_they_share() {
        let a = rep("(pairof (base int) (base string) (frozen #t) #t)");
        let b = rep("(ref (pairof (base int) (base string) (frozen #t) #t) (rconst r))");
        let both = combine("fasl-types", &[&a, &b]).expect("combines");
        assert_eq!(both, rep("(fasl-types #1=(pairof (base int) (base string) (frozen #t) #t) (ref #1# (rconst r)))"), "{}", text::write(&both));
    }

    /// A part of a rep is a rep of its own; an effect's, as evidence.
    #[test]
    fn a_part_is_a_rep() {
        let r = rep("(subr (native) (&effect (io stdout)) (params (base int)) (base string))");
        let params = match r.nodes[0].args[2] { Arg::Node(k) => k, _ => panic!("params") };
        let effect = match r.nodes[0].args[1] { Arg::Node(k) => k, _ => panic!("effect") };
        assert_eq!(part(&r, params, false).expect("a part"), rep("(params (base int))"));
        assert_eq!(part(&r, effect, true).expect("a part"), rep("(evidence (&effect (io stdout)))"));
    }

    #[test]
    fn evidence_must_be_evidence() {
        let checked = rep("(pairof ?0:t (base int) (frozen #t) #t)");
        assert!(fill(&checked, &[("t", &rep("(base int)"))], "var").is_err());
    }
}
