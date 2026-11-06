//! The runtime's primitive table: one entry per name. A name defined twice
//! is found at its first entry alone, so the second is dead (as a
//! one-argument `%fx26-string-copy` once was, beside the three-argument
//! one the lowering calls).

#[test]
fn no_primitive_is_defined_twice() {
    let mut seen = std::collections::HashSet::new();
    let twice: Vec<&str> = fixpt_runtime::PRIMITIVES.iter().map(|d| d.name).filter(|n| !seen.insert(*n)).collect();
    assert!(twice.is_empty(), "defined more than once: {twice:?}");
}
