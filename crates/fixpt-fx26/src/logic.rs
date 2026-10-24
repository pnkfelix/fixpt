//! The logic's propositions, as procedure types' specifications and the
//! cells' verifier state them (`docs/research/typed-cellular-code.md`,
//! §2 and §8), and a prover for them: what both the checker (a
//! specification within another, behavioural subtyping) and the verifier
//! (a VC) ask.
//!
//! A formula is over atoms of any kind: a specification's are its
//! parameters and its result, the verifier's its terms. Integer
//! expressions are linear where they can be; a product of two unknowns is
//! an atom of its own, which is sound, and all the prover knows of it.
//!
//! The prover refutes the hypotheses with the goal denied: the
//! connectives taken apart, a disjunction case by case (a tableau), and
//! each case's integer literals by Fourier–Motzkin elimination
//! (`fm_refutes`, which `sizes.rs` asks too). Sound, incomplete, and
//! bounded: past its budget it has not proved.

use crate::ast::Rel;
use std::collections::BTreeMap;

/// An integer expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr<A> {
    Atom(A),
    Lit(i64),
    Add(Box<Expr<A>>, Box<Expr<A>>),
    Sub(Box<Expr<A>>, Box<Expr<A>>),
    Mul(Box<Expr<A>>, Box<Expr<A>>),
}

/// A proposition. `Holds(a)`: atom `a`, a boolean, is true (not `#f`).
#[derive(Clone, Debug, PartialEq)]
pub enum Formula<A> {
    True,
    False,
    Rel(Rel, Expr<A>, Expr<A>),
    Holds(A),
    Not(Box<Formula<A>>),
    And(Vec<Formula<A>>),
    Or(Vec<Formula<A>>),
    Implies(Box<Formula<A>>, Box<Formula<A>>),
}

impl<A: Clone> Expr<A> {
    /// Each atom replaced by the expression `f` gives for it.
    pub fn subst<B>(&self, f: &impl Fn(&A) -> Expr<B>) -> Expr<B> {
        let bin = |x: &Expr<A>, y: &Expr<A>| (Box::new(x.subst(f)), Box::new(y.subst(f)));
        match self {
            Expr::Atom(a) => f(a),
            Expr::Lit(k) => Expr::Lit(*k),
            Expr::Add(x, y) => {
                let (x, y) = bin(x, y);
                Expr::Add(x, y)
            }
            Expr::Sub(x, y) => {
                let (x, y) = bin(x, y);
                Expr::Sub(x, y)
            }
            Expr::Mul(x, y) => {
                let (x, y) = bin(x, y);
                Expr::Mul(x, y)
            }
        }
    }
}

impl<A: Clone> Formula<A> {
    /// Each atom replaced: in an expression by what `term` gives, as a
    /// proposition by what `holds` gives.
    pub fn subst<B>(&self, term: &impl Fn(&A) -> Expr<B>, holds: &impl Fn(&A) -> Formula<B>) -> Formula<B> {
        let all = |fs: &[Formula<A>]| fs.iter().map(|f| f.subst(term, holds)).collect();
        match self {
            Formula::True => Formula::True,
            Formula::False => Formula::False,
            Formula::Rel(r, x, y) => Formula::Rel(*r, x.subst(term), y.subst(term)),
            Formula::Holds(a) => holds(a),
            Formula::Not(p) => Formula::Not(Box::new(p.subst(term, holds))),
            Formula::And(ps) => Formula::And(all(ps)),
            Formula::Or(ps) => Formula::Or(all(ps)),
            Formula::Implies(p, q) => Formula::Implies(Box::new(p.subst(term, holds)), Box::new(q.subst(term, holds))),
        }
    }

    /// Whether this says nothing: `true`, or a conjunction of nothing.
    pub fn trivial(&self) -> bool {
        match self {
            Formula::True => true,
            Formula::And(ps) => ps.iter().all(|p| p.trivial()),
            _ => false,
        }
    }

    /// Whether any atom of it satisfies `f`.
    pub fn mentions(&self, f: &impl Fn(&A) -> bool) -> bool {
        fn expr<A>(e: &Expr<A>, f: &impl Fn(&A) -> bool) -> bool {
            match e {
                Expr::Atom(a) => f(a),
                Expr::Lit(_) => false,
                Expr::Add(x, y) | Expr::Sub(x, y) | Expr::Mul(x, y) => expr(x, f) || expr(y, f),
            }
        }
        match self {
            Formula::True | Formula::False => false,
            Formula::Rel(_, x, y) => expr(x, f) || expr(y, f),
            Formula::Holds(a) => f(a),
            Formula::Not(p) => p.mentions(f),
            Formula::And(ps) | Formula::Or(ps) => ps.iter().any(|p| p.mentions(f)),
            Formula::Implies(p, q) => p.mentions(f) || q.mentions(f),
        }
    }
}

/// Behavioural subtyping (Liskov and Wing): a procedure specified `a`
/// fits where one specified `b` is expected if it requires no more and
/// ensures no less: `b`'s `requires` entails `a`'s, and, with it, `a`'s
/// `ensures` entails `b`'s. No specification is `true` for both.
pub fn spec_within(a: Option<&crate::ast::Spec>, b: Option<&crate::ast::Spec>) -> bool {
    if a == b {
        return true;
    }
    let none = (Formula::True, Formula::True);
    let (ra, ea) = a.map_or((&none.0, &none.1), |s| (&s.requires, &s.ensures));
    let (rb, eb) = b.map_or((&none.0, &none.1), |s| (&s.requires, &s.ensures));
    entails(std::slice::from_ref(rb), ra) && entails(&[rb.clone(), ea.clone()], eb)
}

/// `e` written as a program writes it, each atom as `atom` says.
pub fn show_expr<A>(e: &Expr<A>, atom: &impl Fn(&A) -> String) -> String {
    match e {
        Expr::Atom(a) => atom(a),
        Expr::Lit(k) => k.to_string(),
        Expr::Add(x, y) => format!("(+ {} {})", show_expr(x, atom), show_expr(y, atom)),
        Expr::Sub(x, y) => format!("(- {} {})", show_expr(x, atom), show_expr(y, atom)),
        Expr::Mul(x, y) => format!("(* {} {})", show_expr(x, atom), show_expr(y, atom)),
    }
}

/// `f` written as a program writes it.
pub fn show<A>(f: &Formula<A>, atom: &impl Fn(&A) -> String) -> String {
    let all = |ps: &[Formula<A>]| ps.iter().map(|p| format!(" {}", show(p, atom))).collect::<String>();
    match f {
        Formula::True => "#t".into(),
        Formula::False => "#f".into(),
        Formula::Rel(r, x, y) => {
            let op = match r {
                Rel::Lt => "<",
                Rel::Le => "<=",
                Rel::Eq => "=",
                Rel::Ne => "!=",
            };
            let (x, y) = (show_expr(x, atom), show_expr(y, atom));
            if *r == Rel::Ne { format!("(not (= {x} {y}))") } else { format!("({op} {x} {y})") }
        }
        Formula::Holds(a) => atom(a),
        Formula::Not(p) => format!("(not {})", show(p, atom)),
        Formula::And(ps) => format!("(and{})", all(ps)),
        Formula::Or(ps) => format!("(or{})", all(ps)),
        Formula::Implies(p, q) => format!("(implies {} {})", show(p, atom), show(q, atom)),
    }
}

/// `k + Σ c·x ≥ 0` (or `= 0`), the atoms by number.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Lin<K> {
    pub k: i128,
    pub terms: BTreeMap<K, i128>,
}

impl<K: Ord + Clone> Lin<K> {
    pub fn lit(k: i128) -> Lin<K> {
        Lin { k, terms: BTreeMap::new() }
    }

    pub fn var(v: K) -> Lin<K> {
        Lin { k: 0, terms: [(v, 1)].into_iter().collect() }
    }

    /// `self + c·other`, or none past `i128`'s range.
    pub fn add_scaled(&self, other: &Lin<K>, c: i128) -> Option<Lin<K>> {
        let mut out = self.clone();
        out.k = out.k.checked_add(other.k.checked_mul(c)?)?;
        for (v, x) in &other.terms {
            let e = out.terms.entry(v.clone()).or_insert(0);
            *e = e.checked_add(x.checked_mul(c)?)?;
        }
        out.terms.retain(|_, c| *c != 0);
        Some(out)
    }

    fn coef(&self, v: &K) -> i128 {
        self.terms.get(v).copied().unwrap_or(0)
    }

    /// Divided by its coefficients' gcd, the constant rounded down: the
    /// same integer solutions of `≥ 0`.
    fn tightened(self) -> Lin<K> {
        let g = self.terms.values().fold(0i128, |g, c| gcd(g, c.abs()));
        if g <= 1 {
            return self;
        }
        Lin { k: self.k.div_euclid(g), terms: self.terms.into_iter().map(|(v, c)| (v, c / g)).collect() }
    }
}

fn gcd(a: i128, b: i128) -> i128 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// How many constraints Fourier–Motzkin elimination may have at once
/// before it gives up.
pub(crate) const FM_LIMIT: usize = 64;

/// Whether `eqs` (each `= 0`) and `ges` (each `≥ 0`) have no integer
/// solution, as far as Fourier–Motzkin elimination shows. Each equality
/// with a variable of coefficient ±1 is first used to rewrite that
/// variable away; the rest are two inequalities. Then each variable in
/// turn, lowest first, is eliminated by adding every constraint with it
/// positive to every one with it negative, scaled so that it cancels, each
/// sum tightened as integers allow. No room left shows as a constant
/// constraint below 0. Sound (rationals are more room than integers),
/// incomplete, and it gives up past `FM_LIMIT` constraints (as Xi and
/// Pfenning's Dependent ML decides its index constraints).
pub(crate) fn fm_refutes<K: Ord + Clone>(eqs: &[Lin<K>], ges: &[Lin<K>]) -> bool {
    let mut eqs: Vec<Lin<K>> = eqs.to_vec();
    let mut cs: Vec<Lin<K>> = ges.to_vec();
    // Equalities: a variable of coefficient ±1 rewritten away everywhere.
    while let Some(i) = eqs.iter().position(|e| e.terms.values().any(|c| c.abs() == 1)) {
        let e = eqs.remove(i);
        let (v, c) = e.terms.iter().find(|(_, c)| c.abs() == 1).map(|(v, c)| (v.clone(), *c)).expect("found");
        // `c·v + rest = 0`: wherever `v` is, with coefficient `d`, add
        // `-d/c` times `e`, which cancels it (`c` is ±1).
        let rewrite = |x: &Lin<K>| {
            let d = x.coef(&v);
            if d == 0 { Some(x.clone()) } else { x.add_scaled(&e, -d * c) }
        };
        let (Some(es), Some(gs)) = (eqs.iter().map(rewrite).collect::<Option<Vec<_>>>(), cs.iter().map(rewrite).collect::<Option<Vec<_>>>()) else {
            return false;
        };
        (eqs, cs) = (es, gs);
    }
    for e in eqs {
        // `Σ c·x = -k` has no integer solution if the gcd does not divide k.
        let g = e.terms.values().fold(0i128, |g, c| gcd(g, c.abs()));
        if (g == 0 && e.k != 0) || (g > 1 && e.k % g != 0) {
            return true;
        }
        let Some(neg) = Lin::lit(0).add_scaled(&e, -1) else { return false };
        cs.push(e);
        cs.push(neg);
    }
    let mut vars: Vec<K> = cs.iter().flat_map(|c| c.terms.keys().cloned()).collect();
    vars.sort();
    vars.dedup();
    for v in vars {
        let (mut next, mut pos, mut neg) = (Vec::new(), Vec::new(), Vec::new());
        for c in cs {
            match c.coef(&v) {
                0 => next.push(c),
                k if k > 0 => pos.push(c),
                _ => neg.push(c),
            }
        }
        for p in &pos {
            for n in &neg {
                let (x, y) = (p.coef(&v), -n.coef(&v));
                let Some(sum) = Lin::lit(0).add_scaled(p, y).and_then(|s| s.add_scaled(n, x)) else { return false };
                next.push(sum.tightened());
            }
        }
        if next.len() > FM_LIMIT {
            return false;
        }
        cs = next;
    }
    cs.iter().any(|c| c.terms.is_empty() && c.k < 0)
}

/// How many cases the prover may look at before it gives up.
const CASES: usize = 512;

/// What one case has gathered: its integer literals, by atoms' numbers,
/// and its boolean ones.
#[derive(Clone)]
struct Case {
    eqs: Vec<Lin<usize>>,
    ges: Vec<Lin<usize>>,
    nes: Vec<Lin<usize>>,
    bools: Vec<(usize, bool)>,
}

struct Prover<A> {
    /// The atoms met, numbered: an expression's atom, or a product of two
    /// unknowns, as an expression.
    atoms: Vec<Expr<A>>,
    /// The boolean atoms met, numbered.
    flags: Vec<A>,
    cases: usize,
}

/// Whether `hyps` entail `goal`, as far as the prover shows.
pub fn entails<A: Clone + PartialEq>(hyps: &[Formula<A>], goal: &Formula<A>) -> bool {
    if goal.trivial() || hyps.contains(goal) {
        return true;
    }
    let mut p = Prover { atoms: Vec::new(), flags: Vec::new(), cases: 0 };
    let mut todo: Vec<(Formula<A>, bool)> = hyps.iter().map(|h| (h.clone(), true)).collect();
    todo.push((goal.clone(), false));
    let case = Case { eqs: Vec::new(), ges: Vec::new(), nes: Vec::new(), bools: Vec::new() };
    p.refute(case, todo)
}

impl<A: Clone + PartialEq> Prover<A> {
    fn atom(&mut self, e: Expr<A>) -> usize {
        match self.atoms.iter().position(|a| *a == e) {
            Some(i) => i,
            None => {
                self.atoms.push(e);
                self.atoms.len() - 1
            }
        }
    }

    fn flag(&mut self, a: &A) -> usize {
        match self.flags.iter().position(|f| f == a) {
            Some(i) => i,
            None => {
                self.flags.push(a.clone());
                self.flags.len() - 1
            }
        }
    }

    /// `e` as a linear form over the atoms, or none past `i128`.
    fn linear(&mut self, e: &Expr<A>) -> Option<Lin<usize>> {
        match e {
            Expr::Atom(_) => Some(Lin::var(self.atom(e.clone()))),
            Expr::Lit(k) => Some(Lin::lit(*k as i128)),
            Expr::Add(x, y) => self.linear(x)?.add_scaled(&self.linear(y)?, 1),
            Expr::Sub(x, y) => self.linear(x)?.add_scaled(&self.linear(y)?, -1),
            Expr::Mul(x, y) => {
                let (lx, ly) = (self.linear(x)?, self.linear(y)?);
                match (lx.terms.is_empty(), ly.terms.is_empty()) {
                    (true, _) => Lin::lit(0).add_scaled(&ly, lx.k),
                    (_, true) => Lin::lit(0).add_scaled(&lx, ly.k),
                    _ => Some(Lin::var(self.atom(e.clone()))),
                }
            }
        }
    }

    /// Whether no case of `case` with `todo` (each formula and whether it
    /// is to hold, or not) is possible. The formulas that do not split are
    /// taken first, the first of them each time, what one adds going last;
    /// a case is tried for a refutation before it splits, on the first
    /// formula left. (In this order step for step, so that the FX-26
    /// checker's, `check-logic.fx`, numbers the atoms alike.)
    fn refute(&mut self, mut case: Case, mut todo: Vec<(Formula<A>, bool)>) -> bool {
        self.cases += 1;
        if self.cases > CASES {
            return false;
        }
        let splits = |f: &Formula<A>, yes: bool| matches!((f, yes), (Formula::Or(_), true) | (Formula::And(_), false) | (Formula::Implies(..), true));
        while let Some(i) = todo.iter().position(|(f, yes)| !splits(f, *yes)) {
            let (f, yes) = todo.remove(i);
            match (f, yes) {
                (Formula::True, true) | (Formula::False, false) => {}
                (Formula::True, false) | (Formula::False, true) => return true,
                (Formula::Not(p), yes) => todo.push((*p, !yes)),
                (Formula::And(ps), true) | (Formula::Or(ps), false) => todo.extend(ps.into_iter().map(|p| (p, yes))),
                (Formula::Implies(p, q), false) => {
                    todo.push((*p, true));
                    todo.push((*q, false));
                }
                (Formula::Holds(a), yes) => {
                    let k = self.flag(&a);
                    if case.bools.contains(&(k, !yes)) {
                        return true;
                    }
                    case.bools.push((k, yes));
                }
                (Formula::Rel(r, x, y), yes) => {
                    // `y - x`, and what it is said to be.
                    let (Some(lx), Some(ly)) = (self.linear(&x), self.linear(&y)) else { continue };
                    let Some(d) = ly.add_scaled(&lx, -1) else { continue };
                    let Some(neg) = Lin::lit(0).add_scaled(&d, -1) else { continue };
                    let less = |l: Lin<usize>| l.add_scaled(&Lin::lit(1), -1);
                    match (r, yes) {
                        // x < y: y - x - 1 ≥ 0; not: x - y ≥ 0.
                        (Rel::Lt, true) => case.ges.extend(less(d)),
                        (Rel::Lt, false) => case.ges.push(neg),
                        (Rel::Le, true) => case.ges.push(d),
                        (Rel::Le, false) => case.ges.extend(less(neg)),
                        (Rel::Eq, true) | (Rel::Ne, false) => case.eqs.push(d),
                        (Rel::Eq, false) | (Rel::Ne, true) => case.nes.push(d),
                    }
                }
                _ => unreachable!("splits"),
            }
        }
        if fm_refutes(&case.eqs, &case.ges) {
            return true;
        }
        // A split: each way must be refuted.
        if !todo.is_empty() {
            let (f, yes) = todo.remove(0);
            let ways: Vec<(Formula<A>, bool)> = match (f, yes) {
                (Formula::Or(ps), true) => ps.into_iter().map(|p| (p, true)).collect(),
                (Formula::And(ps), false) => ps.into_iter().map(|p| (p, false)).collect(),
                (Formula::Implies(p, q), true) => vec![(*p, false), (*q, true)],
                _ => unreachable!("only splits are left"),
            };
            return ways.into_iter().all(|w| {
                let mut t = todo.clone();
                t.push(w);
                self.refute(case.clone(), t)
            });
        }
        // A disequality: below or above.
        if !case.nes.is_empty() {
            let d = case.nes.remove(0);
            let below = Lin::lit(-1).add_scaled(&d, -1);
            let above = d.add_scaled(&Lin::lit(1), -1);
            let (Some(below), Some(above)) = (below, above) else { return false };
            return [below, above].into_iter().all(|g| {
                let mut c = case.clone();
                c.ges.push(g);
                self.refute(c, Vec::new())
            });
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a(n: u32) -> Expr<u32> {
        Expr::Atom(n)
    }
    fn rel(r: Rel, x: Expr<u32>, y: Expr<u32>) -> Formula<u32> {
        Formula::Rel(r, x, y)
    }
    fn add(x: Expr<u32>, y: Expr<u32>) -> Expr<u32> {
        Expr::Add(Box::new(x), Box::new(y))
    }

    #[test]
    fn linear_facts() {
        // r = x + 1 ⊨ x < r
        let h = [rel(Rel::Eq, a(1), add(a(0), Expr::Lit(1)))];
        assert!(entails(&h, &rel(Rel::Lt, a(0), a(1))));
        assert!(!entails(&h, &rel(Rel::Lt, a(1), a(0))));
        // x < y, y < z ⊨ x + 2 ≤ z, as integers
        let h = [rel(Rel::Lt, a(0), a(1)), rel(Rel::Lt, a(1), a(2))];
        assert!(entails(&h, &rel(Rel::Le, add(a(0), Expr::Lit(2)), a(2))));
        assert!(!entails(&h, &rel(Rel::Le, add(a(0), Expr::Lit(3)), a(2))));
    }

    #[test]
    fn cases() {
        // x < 0 ∨ 0 ≤ x, and either way r is |x|: r ≥ 0.
        let neg = rel(Rel::Lt, a(0), Expr::Lit(0));
        let r_neg = rel(Rel::Eq, a(1), Expr::Sub(Box::new(Expr::Lit(0)), Box::new(a(0))));
        let r_pos = rel(Rel::Eq, a(1), a(0));
        let h = [Formula::Implies(Box::new(neg.clone()), Box::new(r_neg)), Formula::Implies(Box::new(Formula::Not(Box::new(neg))), Box::new(r_pos))];
        assert!(entails(&h, &rel(Rel::Le, Expr::Lit(0), a(1))));
        // x ≠ 0, 0 ≤ x ⊨ 1 ≤ x
        let h = [rel(Rel::Ne, a(0), Expr::Lit(0)), rel(Rel::Le, Expr::Lit(0), a(0))];
        assert!(entails(&h, &rel(Rel::Le, Expr::Lit(1), a(0))));
        // A flag and its denial.
        let h = [Formula::Holds(7), Formula::Implies(Box::new(Formula::Holds(7)), Box::new(rel(Rel::Lt, a(0), a(1))))];
        assert!(entails(&h, &rel(Rel::Lt, a(0), a(1))));
        assert!(!entails(&h[1..], &rel(Rel::Lt, a(0), a(1))));
    }

    #[test]
    fn products_are_atoms() {
        let xy = Expr::Mul(Box::new(a(0)), Box::new(a(1)));
        let h = [rel(Rel::Le, Expr::Lit(0), xy.clone())];
        assert!(entails(&h, &rel(Rel::Le, Expr::Lit(-1), xy.clone())));
        // 2·x is linear: x ≥ 1 ⊨ 2·x ≥ 2.
        let two_x = Expr::Mul(Box::new(Expr::Lit(2)), Box::new(a(0)));
        assert!(entails(&[rel(Rel::Le, Expr::Lit(1), a(0))], &rel(Rel::Le, Expr::Lit(2), two_x)));
    }
}
