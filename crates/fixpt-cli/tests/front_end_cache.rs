//! The front end in the native convention, kept in the cache after its
//! first run, native code and all, and read back after (`TODO.md` §126):
//! programs checked and run alike either way.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// `fixpt eval` of `text`, natively, its cache in `cache`: its status, its
/// output and errors, and the names of the code it made or read back.
fn eval(cache: &std::path::Path, dir: &std::path::Path, text: &str) -> (bool, String, String) {
    let (program, syms) = (dir.join("p.fx"), dir.join("syms"));
    std::fs::write(&program, text).unwrap();
    let _ = std::fs::remove_file(&syms);
    let out = Command::new(FIXPT)
        .args(["--fx26-machine", "fx-regs-rsjit-nativecc", "eval", program.to_str().unwrap()])
        .env("XDG_CACHE_HOME", cache)
        .env_remove("FIXPT_NO_CACHE")
        .env("FIXPT_SYMBOLS", &syms)
        .output()
        .expect("fixpt runs");
    let said = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    (out.status.success(), said, std::fs::read_to_string(&syms).unwrap_or_default())
}

/// The first run keeps the front end; the runs after read it back, and a
/// program's value, and a checker's error, are as the first run gave them;
/// the front end's code read back is named, as compiled code is. The runs
/// after run none of it as register code: the first assembles its
/// register words (thousands) to run it once, they only the program's.
#[test]
fn the_front_end_is_kept_native() {
    let dir = std::env::temp_dir().join(format!("fixpt-front-end-cache-{}", std::process::id()));
    let cache = dir.join("cache");
    std::fs::create_dir_all(&cache).unwrap();
    let good = "(define-type ints (listof int @heap))\n\
                (define* total (subr (maxeff (read @heap) spin) (ints int) int)\n\
                  (lambda (xs acc) (if (null? xs) acc (total (cdr xs) (+ acc (car xs))))))\n\
                (total (list 1 2 3 (string-length \"four\")) 0)\n";
    let bad = "(define f (subr pure (int) int) (lambda (x) (+ x \"a\")))\n";
    let first = (eval(&cache, &dir, good), eval(&cache, &dir, bad));
    let kept: Vec<_> = std::fs::read_dir(cache.join("fixpt")).map(|d| d.flatten().map(|e| e.file_name()).collect()).unwrap_or_default();
    assert!(!kept.is_empty(), "nothing kept in {}", cache.display());
    assert!(first.0.0 && first.0.1.contains("10 : int"), "{}", first.0.1);
    assert!(!first.1.0 && first.1.1.contains("a int is expected here"), "{}", first.1.1);
    let register_words = |names: &str| names.lines().filter(|l| l.contains(" register word ")).count();
    assert!(register_words(&first.0.2) > 1000, "the first run ran no front end: {}", register_words(&first.0.2));
    for _ in 0..2 {
        let (good_again, bad_again) = (eval(&cache, &dir, good), eval(&cache, &dir, bad));
        assert_eq!((good_again.0, &good_again.1), (first.0.0, &first.0.1));
        assert_eq!((bad_again.0, &bad_again.1), (first.1.0, &first.1.1));
        assert!(good_again.2.contains("native lambda/"), "the front end's code not named:\n{}", &good_again.2[..good_again.2.len().min(2000)]);
        // The program's own words only.
        assert!(register_words(&good_again.2) < 20, "the front end run again: {}", register_words(&good_again.2));
    }
    let _ = std::fs::remove_dir_all(&dir);
}
