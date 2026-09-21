//! The generated standard environment loads, and description evaluation turns
//! its constructors into what they denote.

use fixpt_fx87::eval::eval;
use fixpt_fx87::parse::DScope;
use fixpt_fx87::unparse::unparse;
use fixpt_fx87::{standard, Parser};

#[test]
fn the_standard_environment_loads() {
    let mut p = Parser::new();
    let std = standard::load(&mut p).expect("standard.fx loads");
    for name in ["+", "car", "cdr", "cons", "new", "get", "list", "vector-ref"] {
        let sym = p.interner.get(name).unwrap_or_else(|| panic!("{name} interned"));
        assert!(std.env.value(sym).is_some(), "{name} should be bound");
    }
    for name in ["int", "bool", "listof", "pairof", "vectorof", "sexp"] {
        let sym = p.interner.get(name).unwrap_or_else(|| panic!("{name} interned"));
        assert!(std.env.desc(sym).is_some(), "{name} should have a kind");
    }
}

/// `listof` is a `dlambda` over a recursive pair type, so `(listof int @=)`
/// denotes exactly the type the goldens print for `(list 1 2 3)`.
///
/// This is the mechanism the whole checker rests on — a description as written
/// is not yet the description it means — so it is worth pinning against a value
/// taken from the corpus rather than invented.
#[test]
fn listof_expands_to_the_recursive_pair_type() {
    let mut p = Parser::new();
    let std = standard::load(&mut p).expect("standard.fx loads");

    let text = "(listof int @=)";
    let mut sources = fixpt_read::SourceMap::new();
    let file = sources.add("<t>", text);
    let forms =
        fixpt_read::Reader::new(text, file, fixpt_read::SyntaxProfile::FX87, &mut p.interner)
            .read_all()
            .expect("reads");
    let written = p.parse_desc(&forms[0], &DScope::default()).expect("parses");
    let meant = eval(&mut p.arena, &std.store, written);

    assert_eq!(
        unparse(&p.arena, &p.interner, meant),
        "(dletrec ((|#1| (pairof int |#1| @=))) (pairof int |#1| @=))",
        "this is the golden type of `(list 1 2 3)`"
    );
}

/// Substituting into a cyclic description must terminate and must re-tie the
/// knot, not share the original's.
#[test]
fn substitution_copies_cycles_rather_than_sharing_them() {
    let mut p = Parser::new();
    let std = standard::load(&mut p).expect("standard.fx loads");

    let text = "(listof int @=) (listof bool @!)";
    let mut sources = fixpt_read::SourceMap::new();
    let file = sources.add("<t>", text);
    let forms =
        fixpt_read::Reader::new(text, file, fixpt_read::SyntaxProfile::FX87, &mut p.interner)
            .read_all()
            .expect("reads");
    let a = p.parse_desc(&forms[0], &DScope::default()).expect("parses");
    let b = p.parse_desc(&forms[1], &DScope::default()).expect("parses");
    let ea = eval(&mut p.arena, &std.store, a);
    let eb = eval(&mut p.arena, &std.store, b);

    assert_ne!(ea, eb, "two expansions are separate objects");
    assert_eq!(
        unparse(&p.arena, &p.interner, eb),
        "(dletrec ((|#1| (pairof bool |#1| @!))) (pairof bool |#1| @!))"
    );
}
