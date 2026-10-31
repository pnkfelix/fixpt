//! Heap dumps (`TODO.md` §189): a program loaded and its heap dumped,
//! by `fixpt dump IMAGE FILE…` or by the program itself (`dump-heap!`), and
//! resumed, by `fixpt resume IMAGE [FILE…] -- ARG…`, where the load is not
//! done again: what it left in the heap is there, and more of the program
//! may be checked and run after it. A dump of sources changed since, or a
//! file that is no dump, is refused.

use std::path::{Path, PathBuf};
use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");
const PROGRAMS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/dump");

/// A directory of this test's own, with `tests/programs/dump`'s files in it.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("dumps-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("made");
    for e in std::fs::read_dir(PROGRAMS).expect("the programs").flatten() {
        std::fs::copy(e.path(), dir.join(e.file_name())).expect("copied");
    }
    dir
}

/// `fixpt ARGS…` in `dir`: its exit status, its output and its errors.
fn fixpt(dir: &Path, args: &[&str]) -> (Option<i32>, String, String) {
    let out = Command::new(FIXPT).args(args).current_dir(dir).output().expect("fixpt runs");
    (out.status.code(), String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned())
}

#[test]
fn a_dumped_program_resumes_as_its_load_left_it() {
    let dir = scratch("resume");
    let (code, _, err) = fixpt(&dir, &["dump", "counter.img", "counter.fx"]);
    assert_eq!(code, Some(0), "{err}");
    // Each run from the dump starts where the load ended: two bumps.
    for _ in 0..2 {
        let (code, out, err) = fixpt(&dir, &["resume", "counter.img", "--", "a", "b"]);
        assert_eq!((code, out.as_str()), (Some(7), "count 3, args 2\n"), "{err}");
    }
}

#[test]
fn a_resumed_program_is_extended_by_more_files() {
    let dir = scratch("more");
    assert_eq!(fixpt(&dir, &["dump", "counter.img", "counter.fx"]).0, Some(0));
    // `more.fx` bumps, defines `twice`, and defines `main` again, which is
    // the one that runs.
    let (code, out, err) = fixpt(&dir, &["resume", "counter.img", "more.fx"]);
    assert_eq!((code, out.as_str()), (Some(3), "twice: 5\n"), "{err}");
}

#[test]
fn a_program_dumps_its_own_heap() {
    let dir = scratch("self");
    let (code, out, err) = fixpt(&dir, &["run", "self.fx"]);
    assert_eq!((code, out.as_str()), (Some(0), "dumped\n"), "{err}");
    // `main` had set the count before it dumped; `resumed` is the start.
    let (code, out, err) = fixpt(&dir, &["resume", "self.img", "--", "x", "y", "z"]);
    assert_eq!((code, out.as_str()), (Some(5), "resumed: count 41, args 3\n"), "{err}");
}

#[test]
fn a_stale_dump_or_none_is_refused() {
    let dir = scratch("stale");
    assert_eq!(fixpt(&dir, &["dump", "counter.img", "counter.fx"]).0, Some(0));
    let text = std::fs::read_to_string(dir.join("counter.fx")).expect("read");
    std::fs::write(dir.join("counter.fx"), format!("{text};; changed\n")).expect("written");
    let (code, _, err) = fixpt(&dir, &["resume", "counter.img"]);
    assert_eq!(code, Some(1));
    assert!(err.contains("is stale"), "{err}");
    let (code, _, err) = fixpt(&dir, &["resume", "more.fx"]);
    assert_eq!(code, Some(1));
    assert!(err.contains("it is not a dump"), "{err}");
}

#[test]
fn a_machine_that_cannot_dump_says_so() {
    let dir = scratch("machines");
    for m in ["rs-scheme-vm", "fx-ast-eval", "fx-regs-fxjit-nativecc"] {
        let (code, _, err) = fixpt(&dir, &["--machine", m, "dump", "counter.img", "counter.fx"]);
        assert_eq!(code, Some(1), "{m}");
        assert!(err.contains("this machine cannot dump a program"), "{m}: {err}");
        let (code, out, err) = fixpt(&dir, &["--machine", m, "run", "self.fx"]);
        assert_eq!((code, out.as_str()), (Some(0), "no dump: this machine cannot dump its heap\n"), "{m}: {err}");
    }
}
