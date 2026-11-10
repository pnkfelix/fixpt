//! Binding shapes (`docs/research/binding-shapes.md`, step 2): what a
//! module gives, read before its type is known, written into each form
//! that opens it, and held to its type by the checkers.

use fixpt_fx26::Checker;
use std::path::Path;

/// The Rust checker's word on a file named by `FIXPT_SHAPES_FILE`: for
/// trying one by hand.
#[test]
#[ignore]
fn a_file_is_checked() {
    let Ok(f) = std::env::var("FIXPT_SHAPES_FILE") else { return };
    let text = std::fs::read_to_string(&f).expect("readable");
    let mut c = Checker::new();
    c.base_dir = Path::new(&f).parent().map(|d| d.to_path_buf());
    match fixpt_fx26::compare::check_with_rust_checker(&mut c, &text) {
        Ok(_) => println!("checked"),
        Err(e) => println!("refused: {}", e.message),
    }
}

/// How long the walk of the file `FIXPT_SHAPES_WALK` takes, as a module's
/// items: for measuring by hand.
#[test]
#[ignore]
fn a_file_is_walked_in_time() {
    let Ok(f) = std::env::var("FIXPT_SHAPES_WALK") else { return };
    let text = std::fs::read_to_string(&f).expect("readable");
    let mut c = Checker::new();
    let t0 = std::time::Instant::now();
    let r = c.alpha_renamed(&format!("(define walked (module {text}\n))"));
    println!("{} ms: {}", t0.elapsed().as_millis(), r.map(|_| "walked".to_string()).unwrap_or_else(|e| e.message.to_string()));
}
