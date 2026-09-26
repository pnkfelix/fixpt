//! The object layout's FX-26 copy, `src/layout.fx`, is generated from the one
//! table in `fixpt_heap::layout`, and must be exactly what the generator
//! produces. `FIXPT_BLESS=1` rewrites it.

const PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/src/layout.fx");

#[test]
fn layout_fx_is_generated_from_the_table() {
    let want = fixpt_heap::layout::fx26_module();
    if std::env::var_os("FIXPT_BLESS").is_some() {
        std::fs::write(PATH, &want).expect("writes layout.fx");
    }
    let have = std::fs::read_to_string(PATH).unwrap_or_default();
    assert!(
        have == want,
        "src/layout.fx is not what fixpt_heap::layout generates; \
         run `FIXPT_BLESS=1 cargo test -p fixpt-fx26 --test layout`"
    );
}

/// And it is FX-26 that checks.
#[test]
fn layout_fx_checks() {
    let mut c = fixpt_fx26::Checker::new();
    let text = format!("{} tag-bloblet", fixpt_fx26::LAYOUT);
    let k = c.check_program(&text).unwrap_or_else(|e| panic!("layout.fx does not check: {e}"));
    assert_eq!(c.show_ty(k.ty), "int");
}

/// Likewise the compiler's table of standard operations, `src/standard.fx`,
/// generated from the lowering's.
#[test]
fn standard_fx_is_generated_from_the_lowering() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/src/standard.fx");
    let want = fixpt_fx26::lower::standard_fx26_module();
    if std::env::var_os("FIXPT_BLESS").is_some() {
        std::fs::write(path, &want).expect("writes standard.fx");
    }
    let have = std::fs::read_to_string(path).unwrap_or_default();
    assert!(have == want, "src/standard.fx is not what the lowering's table generates; run `FIXPT_BLESS=1 cargo test -p fixpt-fx26 --test layout`");
}
