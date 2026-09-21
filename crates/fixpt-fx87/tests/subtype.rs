//! The subtyping, subeffecting and subregioning relations.
//!
//! These are what FX-87 has instead of unification, so they deserve direct
//! tests rather than only being exercised through the corpus — a wrong variance
//! is the kind of bug that makes many cases pass and a few fail confusingly.

use fixpt_fx87::ast::{Arena, Binder, Desc, DescId, Kind};
use fixpt_fx87::subtype::{DStore, Rel};
use fixpt_read::Interner;

struct Ctx {
    a: Arena,
    i: Interner,
}

impl Ctx {
    fn new() -> Ctx {
        Ctx { a: Arena::new(), i: Interner::new() }
    }
    fn con(&mut self, name: &str) -> DescId {
        let s = self.i.intern(name);
        self.a.con0(s)
    }
    fn rel(&self) -> Rel<'_> {
        let eq = self.i.get("@=").expect("@= interned");
        let r = self.i.get("ref").expect("ref interned");
        Rel::new(&self.a, eq, r)
    }
    fn prime(&mut self) {
        // Make sure the two special names exist before `rel` asks for them.
        self.i.intern("@=");
        self.i.intern("ref");
    }
}

fn empty() -> DStore {
    DStore::new()
}

#[test]
fn regions_are_below_the_unions_that_contain_them() {
    let mut c = Ctx::new();
    c.prime();
    let red = c.con("@red");
    let blue = c.con("@blue");
    let green = c.con("@green");
    let rb = c.a.desc(Desc::RUnion(vec![red, blue]));

    let r = c.rel();
    assert!(r.region_less(red, rb, &empty(), &empty()));
    assert!(r.region_less(blue, rb, &empty(), &empty()));
    assert!(!r.region_less(green, rb, &empty(), &empty()));
    // A union is below another when every member is.
    assert!(r.region_less(rb, rb, &empty(), &empty()));
    let rbg = c.a.desc(Desc::RUnion(vec![red, blue, green]));
    let r = c.rel();
    assert!(r.region_less(rb, rbg, &empty(), &empty()));
    assert!(!r.region_less(rbg, rb, &empty(), &empty()));
}

#[test]
fn pure_is_below_everything_and_effects_need_the_same_constructor() {
    let mut c = Ctx::new();
    c.prime();
    let red = c.con("@red");
    let blue = c.con("@blue");
    let pure = c.a.desc(Desc::Pure);
    let read_red = c.a.desc(Desc::Read(red));
    let write_red = c.a.desc(Desc::Write(red));
    let rb = c.a.desc(Desc::RUnion(vec![red, blue]));
    let read_rb = c.a.desc(Desc::Read(rb));
    let both = c.a.maxeff(vec![read_red, write_red]);

    let r = c.rel();
    assert!(r.effect_less(pure, read_red, &empty(), &empty()));
    assert!(!r.effect_less(read_red, pure, &empty(), &empty()));
    // Reading is not writing, however large the region.
    assert!(!r.effect_less(read_red, write_red, &empty(), &empty()));
    // A read of a smaller region is below a read of a larger one.
    assert!(r.effect_less(read_red, read_rb, &empty(), &empty()));
    assert!(!r.effect_less(read_rb, read_red, &empty(), &empty()));
    // Every atom has to be covered.
    assert!(r.effect_less(read_red, both, &empty(), &empty()));
    assert!(!r.effect_less(both, read_red, &empty(), &empty()));
}

/// A subroutine's arguments are contravariant and its result covariant — the
/// rule that is easiest to get backwards.
#[test]
fn subroutine_arguments_are_contravariant() {
    let mut c = Ctx::new();
    c.prime();
    let red = c.con("@red");
    let blue = c.con("@blue");
    let int = c.con("int");
    let pure = c.a.desc(Desc::Pure);
    let read_red = c.a.desc(Desc::Read(red));
    let rb = c.a.desc(Desc::RUnion(vec![red, blue]));
    let read_rb = c.a.desc(Desc::Read(rb));

    // A `pure` subroutine is usable where an effectful one was wanted.
    let f_pure = c.a.desc(Desc::Subr { effect: pure, args: vec![int], result: int });
    let f_read = c.a.desc(Desc::Subr { effect: read_red, args: vec![int], result: int });
    let r = c.rel();
    assert!(r.type_less(f_pure, f_read, &empty(), &empty()));
    assert!(!r.type_less(f_read, f_pure, &empty(), &empty()));

    // Now in argument position, where the direction reverses: a subroutine
    // that *takes* a pure function accepts fewer things than one that takes an
    // effectful function, so it is the *super*type.
    let takes_pure =
        c.a.desc(Desc::Subr { effect: pure, args: vec![f_pure], result: int });
    let takes_read =
        c.a.desc(Desc::Subr { effect: pure, args: vec![f_read], result: int });
    let r = c.rel();
    assert!(
        r.type_less(takes_read, takes_pure, &empty(), &empty()),
        "contravariance: accepting more makes you a subtype"
    );
    assert!(!r.type_less(takes_pure, takes_read, &empty(), &empty()));

    // Arity must match.
    let two = c.a.desc(Desc::Subr { effect: pure, args: vec![int, int], result: int });
    let r = c.rel();
    assert!(!r.type_less(f_pure, two, &empty(), &empty()));
    let _ = read_rb;
}

/// A mutable cell cannot vary in what it holds; an immutable one can.
#[test]
fn ref_is_invariant_unless_immutable() {
    let mut c = Ctx::new();
    c.prime();
    let bang = c.con("@!");
    let eq = c.con("@=");
    let int = c.con("int");
    let refsym = c.i.intern("ref");
    let pure = c.a.desc(Desc::Pure);

    // Two function types, one a subtype of the other.
    let f_pure = c.a.desc(Desc::Subr { effect: pure, args: vec![int], result: int });
    let read_bang = c.a.desc(Desc::Read(bang));
    let f_read = c.a.desc(Desc::Subr { effect: read_bang, args: vec![int], result: int });

    let mut_pure = c.a.desc(Desc::Con(refsym, vec![f_pure, bang]));
    let mut_read = c.a.desc(Desc::Con(refsym, vec![f_read, bang]));
    let imm_pure = c.a.desc(Desc::Con(refsym, vec![f_pure, eq]));
    let imm_read = c.a.desc(Desc::Con(refsym, vec![f_read, eq]));

    let r = c.rel();
    // Mutable: no covariance, because it could be written through.
    assert!(
        !r.type_less(mut_pure, mut_read, &empty(), &empty()),
        "a mutable ref must not be covariant in its contents"
    );
    // Immutable: covariance is sound.
    assert!(
        r.type_less(imm_pure, imm_read, &empty(), &empty()),
        "an immutable ref may be covariant"
    );
    assert!(!r.type_less(imm_read, imm_pure, &empty(), &empty()));
    // Same type in the same region is fine either way.
    let same = c.a.desc(Desc::Con(refsym, vec![int, bang]));
    let same2 = c.a.desc(Desc::Con(refsym, vec![int, bang]));
    let r = c.rel();
    assert!(r.type_less(same, same2, &empty(), &empty()));
}

/// `poly` types are equal up to the names of their binders.
#[test]
fn poly_types_compare_up_to_renaming() {
    let mut c = Ctx::new();
    c.prime();
    let t = c.i.intern("t");
    let u = c.i.intern("u");
    let pure = c.a.desc(Desc::Pure);
    let vt = c.a.desc(Desc::Var(t));
    let vu = c.a.desc(Desc::Var(u));
    let ft = c.a.desc(Desc::Subr { effect: pure, args: vec![vt], result: vt });
    let fu = c.a.desc(Desc::Subr { effect: pure, args: vec![vu], result: vu });
    let pt = c.a.desc(Desc::Poly {
        binders: vec![Binder { name: t, kind: Kind::Type }],
        body: ft,
    });
    let pu = c.a.desc(Desc::Poly {
        binders: vec![Binder { name: u, kind: Kind::Type }],
        body: fu,
    });
    let r = c.rel();
    assert!(r.type_less(pt, pu, &empty(), &empty()), "alpha-equivalent polys");

    // Binder kinds must agree.
    let pr = c.a.desc(Desc::Poly {
        binders: vec![Binder { name: u, kind: Kind::Region }],
        body: fu,
    });
    let r = c.rel();
    assert!(!r.type_less(pt, pr, &empty(), &empty()));
}

/// Comparison terminates on types that contain themselves.
#[test]
fn recursive_types_compare_without_diverging() {
    let mut c = Ctx::new();
    c.prime();
    let int = c.con("int");
    let eq = c.con("@=");
    let pairof = c.i.intern("pairof");

    let make = |a: &mut Arena| {
        let l = a.hole();
        a.fill(l, Desc::Con(pairof, vec![int, l, eq]));
        l
    };
    let l1 = make(&mut c.a);
    let l2 = make(&mut c.a);

    let r = c.rel();
    // Two separately-built lists of int are the same type, and asking does not
    // hang — which is the point of the trail.
    assert!(r.type_less(l1, l2, &empty(), &empty()));
    assert!(r.type_less(l2, l1, &empty(), &empty()));
}
