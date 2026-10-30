//! FX-26's I/O (`TODO.md` §84), as `fixpt run` performs it: what a program
//! writes to its standard output and error, and the status it ends with,
//! the same on every kind of machine (`programs/io/`).

use std::process::{Command, Stdio};

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// One machine of each kind: the lowering's, the evaluator written in
/// FX-26, a cellular interpreter, register code, and native code.
const ALL_MACHINES: [&str; 5] = ["rs-scheme-vm", "fx-ast-eval", "fx-cells-rsinterp", "fx-regs-rsjit-cellcc", "fx-regs-rsjit-nativecc"];
/// The native convention's only where it runs.
const MACHINES: &[&str] = if fixpt_native::NATIVE_CONVENTION_AVAILABLE { &ALL_MACHINES } else { ALL_MACHINES.split_at(4).0 };

/// `program` run on `machine`: its status, standard output and error.
fn run(machine: &str, program: &str) -> (Option<i32>, String, String) {
    let path = format!("{}/tests/programs/io/{program}", env!("CARGO_MANIFEST_DIR"));
    let out = output(Command::new(FIXPT).args(["--fx26-machine", machine, "run", &path]).stdin(Stdio::null()));
    (out.status.code(), String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned())
}

/// Each program on each machine, at once.
fn on_every_machine(program: &'static str) -> Vec<(&'static str, (Option<i32>, String, String))> {
    let runs: Vec<_> = MACHINES.iter().map(|m| (*m, std::thread::spawn(move || run(m, program)))).collect();
    runs.into_iter().map(|(m, t)| (m, t.join().expect("ran"))).collect()
}

#[test]
fn the_standard_streams_written() {
    for (m, (status, out, err)) in on_every_machine("streams.fx") {
        assert_eq!((status, out.as_str(), err.as_str()), (Some(0), "hello, world\n", "to stderr\n"), "{m}");
    }
}

#[test]
fn main_gives_the_status() {
    for (m, (status, out, err)) in on_every_machine("main-status.fx") {
        assert_eq!((status, out.as_str(), err.as_str()), (Some(44), "in main\n", ""), "{m}");
    }
}

#[test]
fn exit_ends_the_run() {
    for (m, (status, out, err)) in on_every_machine("exit.fx") {
        assert_eq!((status, out.as_str(), err.as_str()), (Some(7), "0\n1\n2\n", ""), "{m}");
    }
}

#[test]
fn a_failed_run_exits_70() {
    for (m, (status, out, err)) in on_every_machine("trap.fx") {
        assert_eq!((status, out.as_str()), (Some(70), "before\n"), "{m}: {err}");
        assert!(!err.is_empty(), "{m}: the failure is said");
    }
}

/// A write to a pipe whose reader has gone: an `io-error` of kind
/// `broken-pipe`, which the program answers.
#[test]
fn a_failed_write_is_a_value() {
    for m in MACHINES {
        let path = format!("{}/tests/programs/io/broken-pipe.fx", env!("CARGO_MANIFEST_DIR"));
        let mut child = spawned(Command::new(FIXPT).args(["--fx26-machine", m, "run", &path]).stdin(Stdio::null()));
        drop(child.stdout.take());
        let out = child.wait_with_output().expect("ends");
        let err = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(3), "{m}: {err}");
        assert!(err.starts_with("broken pipe: "), "{m}: {err}");
    }
}

/// Files, relative to the working directory, each machine's its own: two
/// written, one replaced (no file of its left beside it), the names
/// sorted, one read back, a missing one `not-found`.
#[test]
fn files_written_listed_and_read() {
    let path = format!("{}/tests/programs/io/files.fx", env!("CARGO_MANIFEST_DIR"));
    for m in MACHINES {
        let dir = std::env::temp_dir().join(format!("fixpt-io-files-{m}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("a directory");
        let out = output(Command::new(FIXPT).args(["--fx26-machine", m, "run", &path]).current_dir(&dir).stdin(Stdio::null()));
        let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        assert_eq!((out.status.code(), stdout.as_ref()), (Some(5), "a.txt\nb.txt\nbee, again\n"), "{m}: {stderr}");
        let mut left: Vec<_> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().file_name().into_string().unwrap()).collect();
        left.sort();
        assert_eq!(left, ["a.txt", "b.txt"], "{m}");
        std::fs::remove_dir_all(&dir).expect("removed");
    }
}

/// Files (Heist's `FIXPT-CHANGES.md` F5), in a directory of each
/// machine's own: what each path is, a link not followed, and a link's
/// target.
#[test]
fn files_inspected() {
    let path = format!("{}/tests/programs/io/fs.fx", env!("CARGO_MANIFEST_DIR"));
    let want = "a.txt file 5\n. directory\nl symlink\nl -> a.txt\nnope not-found\na.txt no link\n";
    for m in MACHINES {
        let dir = std::env::temp_dir().join(format!("fixpt-io-fs-{m}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("a directory");
        std::os::unix::fs::symlink("a.txt", dir.join("l")).expect("a link");
        let out = output(Command::new(FIXPT).args(["--fx26-machine", m, "run", &path]).current_dir(&dir).stdin(Stdio::null()));
        let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        assert_eq!((out.status.code(), stdout.as_ref()), (Some(0), want), "{m}: {stderr}");
        std::fs::remove_dir_all(&dir).expect("removed");
    }
}

/// A process waited for (Heist's `FIXPT-CHANGES.md` F6): a `pselect` with
/// arms for its output and its end, which comes after all its output; and
/// `process-exit` alone, the output taken after.
#[test]
fn a_process_waited_for() {
    for (m, (status, out, err)) in on_every_machine("process-wait.fx") {
        assert_eq!((status, out.as_str()), (Some(0), "one|two|exited 3; exited 4, then late|\n"), "{m}: {err}");
    }
}

/// A task waits for a process while another ticks on the clock: neither
/// keeps the other from running.
#[test]
fn a_task_waits_for_a_process_while_another_runs() {
    for (m, (status, out, err)) in on_every_machine("process-tasks.fx") {
        assert_eq!((status, out.as_str()), (Some(0), "out\nend 5\n"), "{m}: {err}");
    }
}

/// News of whichever process has some (F6), one arm for any number: each's
/// output, and each end once.
#[test]
fn news_of_any_process() {
    for (m, (status, out, err)) in on_every_machine("process-news.fx") {
        assert_eq!(
            (status, out.as_str()),
            (Some(0), "[A\n][B1\nB2\n] ended, last first: 0 1 ; no news left\n"),
            "{m}: {err}"
        );
    }
}

/// The program's own arguments after `--`, an empty one too; and a sleep
/// on the clock, which the clock then shows has passed.
#[test]
fn arguments_and_the_clock() {
    let path = format!("{}/tests/programs/io/args-clock.fx", env!("CARGO_MANIFEST_DIR"));
    let runs: Vec<_> = MACHINES
        .iter()
        .map(|m| {
            let path = path.clone();
            (*m, std::thread::spawn(move || output(Command::new(FIXPT).args(["--fx26-machine", m, "run", &path, "--", "one", "two words", ""]))))
        })
        .collect();
    for (m, t) in runs {
        let out = t.join().expect("ran");
        let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        assert_eq!((out.status.code(), stdout.as_ref()), (Some(0), "one;two words;;"), "{m}: {stderr}");
    }
}

/// The standard input, a line at a time: a `\r\n` ending left off as a
/// `\n` is, a line not UTF-8 a failure the program goes on from, the last
/// line with no ending, then the end.
#[test]
fn the_standard_input_read_by_lines() {
    use std::io::Write as _;
    let path = format!("{}/tests/programs/io/echo.fx", env!("CARGO_MANIFEST_DIR"));
    for m in MACHINES {
        let mut child = spawned(Command::new(FIXPT).args(["--fx26-machine", m, "run", &path]).stdin(Stdio::piped()));
        child.stdin.take().expect("piped").write_all(b"one\r\ntwo\n\xff\xfe\nlast").expect("written");
        let out = child.wait_with_output().expect("ends");
        let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        assert_eq!((out.status.code(), stdout.as_ref()), (Some(4), "0: one\n1: two\n2: bad\n3: last\n"), "{m}: {stderr}");
    }
}

/// `program` run on `machine`, its standard input a pipe written `input`
/// after `delay`, then closed, or, `input` none, held open until it ends,
/// however long it takes to start:
/// its status, and its standard output and error.
/// Held while a child is made (`TODO.md` §99): on macOS a pipe is made and
/// only then marked close-on-exec, so a child another thread makes between
/// the two inherits it, and holds it open: a child whose input it is sees
/// no end until that one ends (a wait for a key then ended at its
/// deadline), one whose output it is no broken pipe.
static SPAWN: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// `c` started, its output and errors piped, no other child made meanwhile.
fn spawned(c: &mut Command) -> std::process::Child {
    let _making = SPAWN.lock().unwrap_or_else(|e| e.into_inner());
    c.stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().expect("fixpt runs")
}

/// `c` run to its end, as `Command::output` runs it, made as `spawned`.
fn output(c: &mut Command) -> std::process::Output {
    spawned(c).wait_with_output().expect("ends")
}

fn run_fed(machine: &str, program: &str, input: Option<&'static [u8]>, delay: std::time::Duration) -> (Option<i32>, String, String) {
    use std::io::Write as _;
    let path = format!("{}/tests/programs/io/{program}", env!("CARGO_MANIFEST_DIR"));
    let mut child = spawned(Command::new(FIXPT).args(["--fx26-machine", machine, "run", &path]).stdin(Stdio::piped()));
    let mut stdin = child.stdin.take().expect("piped");
    // Fed, then closed; or, no input, held open here until the run ends.
    let (feeder, held) = match input {
        Some(bytes) => (
            Some(std::thread::spawn(move || {
                std::thread::sleep(delay);
                let _ = stdin.write_all(bytes);
            })),
            None,
        ),
        None => (None, Some(stdin)),
    };
    let out = child.wait_with_output().expect("ends");
    drop(held);
    if let Some(f) = feeder {
        f.join().expect("fed");
    }
    (out.status.code(), String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned())
}

/// The standard input by bytes (`TODO.md` §95), after a line: two bytes,
/// then the rest that has come into a bytevector, then the end; the
/// terminal's operations say a pipe is no terminal.
#[test]
fn the_standard_input_read_by_bytes() {
    let runs: Vec<_> = MACHINES.iter().map(|m| (*m, std::thread::spawn(move || run_fed(m, "bytes.fx", Some(b"hello\nABcdefg"), Default::default())))).collect();
    for (m, t) in runs {
        let (status, out, err) = t.join().expect("ran");
        let want = "hello\n65\n66\nready\n5\n99\neof\neof\nraw: none\nrestore: none\nsize: none\n";
        assert_eq!((status, out.as_str()), (Some(0), want), "{m}: {err}");
    }
}

/// A process waits for a key, a message or a deadline (`TODO.md` §95): a
/// key that comes later than the wait began, the input's end, and, no
/// key, the deadline, a second on.
#[test]
fn a_process_waits_for_a_key() {
    let ms = std::time::Duration::from_millis;
    let cases: [(Option<&'static [u8]>, i32); 3] = [(Some(b"q"), 113), (Some(b""), 255), (None, 1)];
    let mut runs = Vec::new();
    for m in MACHINES {
        for (input, want) in cases {
            runs.push((m, want, std::thread::spawn(move || run_fed(m, "key-or-message.fx", input, ms(300)))));
        }
    }
    for (m, want, t) in runs {
        let (status, _, err) = t.join().expect("ran");
        assert_eq!(status, Some(want), "{m}: {err}");
    }
}

/// Each form runs once (`TODO.md` §96): a definition that writes, an
/// expression that writes, a process a definition spawned, then `main`;
/// the evaluator written in FX-26 too, which once ran every definition
/// again with each later form.
#[test]
fn each_form_runs_once() {
    for (m, (status, out, err)) in on_every_machine("once.fx") {
        assert_eq!((status, out.as_str()), (Some(42), "define x\nan expression\nthe process\nmain\n"), "{m}: {err}");
    }
}
