//! The printed form of a description is what the goldens compare, so these
//! check it directly — especially the recursive types, which are the only
//! place the printer does anything clever.

use fixpt_fx87::ast::{Arena, Binder, Desc, Kind};
use fixpt_fx87::unparse::unparse;
use fixpt_read::Interner;

fn setup() -> (Arena, Interner) {
    (Arena::new(), Interner::new())
}

#[test]
fn simple_types_print_flat() {
    let (mut a, mut i) = setup();
    let int = i.intern("int");
    let t = a.con0(int);
    assert_eq!(unparse(&a, &i, t), "int");

    let pure = a.desc(Desc::Pure);
    let s = a.desc(Desc::Subr { effect: pure, args: vec![t, t], result: t });
    assert_eq!(unparse(&a, &i, s), "(subr pure (int int) int)");
}

#[test]
fn effects_and_regions() {
    let (mut a, mut i) = setup();
    let bang = i.intern("@!");
    let red = i.intern("@red");
    let blue = i.intern("@blue");
    let r = a.con0(bang);
    let read = a.desc(Desc::Read(r));
    assert_eq!(unparse(&a, &i, read), "(read @!)");

    let rr = a.con0(red);
    let rb = a.con0(blue);
    let w = a.desc(Desc::Write(rb));
    let m = a.maxeff(vec![read, w]);
    assert_eq!(unparse(&a, &i, m), "(maxeff (read @!) (write @blue))");

    let u = a.desc(Desc::RUnion(vec![rr, rb]));
    let ru = a.desc(Desc::Read(u));
    assert_eq!(unparse(&a, &i, ru), "(read (runion @red @blue))");
}

#[test]
fn maxeff_is_normalised() {
    let (mut a, mut i) = setup();
    let bang = i.intern("@!");
    let r = a.con0(bang);
    let read = a.desc(Desc::Read(r));
    let read2 = a.desc(Desc::Read(r));
    let pure = a.desc(Desc::Pure);

    // `pure` contributes nothing, duplicates collapse, and a single member
    // unwraps — the normal form `effect-less-1?` assumes.
    let m = a.maxeff(vec![pure, read, read2, pure]);
    assert_eq!(unparse(&a, &i, m), "(read @!)");

    // Nested maxeffs flatten.
    let w = a_write(&mut a, &mut i);
    let inner = a.desc(Desc::MaxEff(vec![read, w]));
    let outer = a.maxeff(vec![inner, read2]);
    assert_eq!(unparse(&a, &i, outer), "(maxeff (read @!) (write @=))");
}

fn a_write(a: &mut Arena, i: &mut Interner) -> fixpt_fx87::DescId {
    let eq = i.intern("@=");
    let r = a.con0(eq);
    a.desc(Desc::Write(r))
}

/// `(list 1 2 3)` — the type contains itself.
#[test]
fn a_recursive_type_prints_as_dletrec() {
    let (mut a, mut i) = setup();
    let int = i.intern("int");
    let pairof = i.intern("pairof");
    let eq = i.intern("@=");
    let ti = a.con0(int);
    let re = a.con0(eq);

    // μX. (pairof int X @=), tied through a hole.
    let list = a.hole();
    a.fill(list, Desc::Con(pairof, vec![ti, list, re]));

    assert_eq!(
        unparse(&a, &i, list),
        "(dletrec ((|#1| (pairof int |#1| @=))) (pairof int |#1| @=))"
    );
}

/// Two distinct cycles get distinct names, in discovery order.
///
/// Deliberately *not* asserting the whole printed form. The corpus's case 155
/// shows that how a recursive type prints depends on how it was built: a type
/// written with an explicit source-level `dletrec` prints its body by name
/// (`(subr pure (|#1|) |#2|)`), while one the checker tied itself unrolls once
/// (`(pairof int |#1| @=)`). Until `dletrec` exists as a description form here,
/// asserting a particular body would be inventing a golden — which is the one
/// thing this project's corpora are supposed to rule out. The naming discipline
/// is what this checks, and the real goldens will check the rest.
#[test]
fn two_cycles_are_numbered_in_discovery_order() {
    let (mut a, mut i) = setup();
    let int = i.intern("int");
    let pairof = i.intern("pairof");
    let eq = i.intern("@=");
    let ti = a.con0(int);
    let re = a.con0(eq);

    let make_list = |a: &mut Arena| {
        let l = a.hole();
        a.fill(l, Desc::Con(pairof, vec![ti, l, re]));
        l
    };
    let l1 = make_list(&mut a);
    let l2 = make_list(&mut a);
    let pure = a.desc(Desc::Pure);
    let s = a.desc(Desc::Subr { effect: pure, args: vec![l1], result: l2 });

    let text = unparse(&a, &i, s);
    assert!(text.starts_with("(dletrec ("), "{text}");
    assert!(text.contains("|#1|"), "first cycle unnamed: {text}");
    assert!(text.contains("|#2|"), "second cycle unnamed: {text}");
    // The argument's cycle is met before the result's.
    assert!(
        text.find("|#1|").unwrap() < text.find("|#2|").unwrap(),
        "names should follow discovery order: {text}"
    );
}

/// Sharing that is not a cycle prints twice, as the reference does. Only back
/// edges get names.
#[test]
fn shared_but_acyclic_structure_is_not_named() {
    let (mut a, mut i) = setup();
    let int = i.intern("int");
    let pairof = i.intern("pairof");
    let eq = i.intern("@=");
    let ti = a.con0(int);
    let re = a.con0(eq);
    let inner = a.desc(Desc::Con(pairof, vec![ti, ti, re]));
    let outer = a.desc(Desc::Con(pairof, vec![inner, inner, re]));
    assert_eq!(
        unparse(&a, &i, outer),
        "(pairof (pairof int int @=) (pairof int int @=) @=)"
    );
}

#[test]
fn poly_binders_carry_their_kinds() {
    let (mut a, mut i) = setup();
    let int = i.intern("int");
    let r = i.intern("r");
    let refof = i.intern("ref");
    let ti = a.con0(int);
    let tr = a.desc(Desc::Var(r));
    let rf = a.desc(Desc::Con(refof, vec![ti, tr]));
    let read = a.desc(Desc::Read(tr));
    let s = a.desc(Desc::Subr { effect: read, args: vec![rf], result: ti });
    let p = a.desc(Desc::Poly {
        binders: vec![Binder { name: r, kind: Kind::Region }],
        body: s,
    });
    assert_eq!(unparse(&a, &i, p), "(poly ((r region)) (subr (read r) ((ref int r)) int))");

    // A higher-kinded binder.
    let f = i.intern("f");
    let tf = a.desc(Desc::Var(f));
    let app = a.desc(Desc::DApp { fun: tf, args: vec![ti] });
    let pure = a.desc(Desc::Pure);
    let s2 = a.desc(Desc::Subr { effect: pure, args: vec![app], result: app });
    let p2 = a.desc(Desc::Poly {
        binders: vec![Binder {
            name: f,
            kind: Kind::DFunc(vec![Kind::Type], Box::new(Kind::Type)),
        }],
        body: s2,
    });
    assert_eq!(
        unparse(&a, &i, p2),
        "(poly ((f (dfunc (type) type))) (subr pure ((f int)) (f int)))"
    );
}
