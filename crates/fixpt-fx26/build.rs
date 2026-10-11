//! `cfg(optimized)`, for tests too slow without optimization: the ones that
//! run every word of the front end are ignored in an unoptimized build, and
//! run in an optimized one with debug assertions on (the `checked` profile)
//! as in release.

fn main() {
    println!("cargo::rustc-check-cfg=cfg(optimized)");
    if std::env::var("OPT_LEVEL").is_ok_and(|o| o != "0") {
        println!("cargo::rustc-cfg=optimized");
    }
}
