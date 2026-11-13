//! Where a process's time goes, by phase (`TODO.md` §252): with
//! `FIXPT_PHASE_TIMES=dir`, each process writes `dir/PID.tsv`, the
//! exclusive time of each path of phases it was in, in nanoseconds, with
//! how often each was entered and the collections each began. A phase is
//! named (`rust-front`, `rust-compile`, `fx:check-program`, `run:regs`,
//! `gc:minor`, …) and entered at the few places that start such work
//! ([`enter`]); entering one pauses the one below, so each moment is the
//! innermost phase's, kept under the path that led to it, as a flame graph
//! keeps it (`a;b;c`). A collection is a phase too, so its time is taken
//! from the mutator's that began it ([`collection`]).
//!
//! Off, as it is unless the variable is set, [`enter`] is a load and a
//! test. On, the file is written at the process's exit (`atexit`); on
//! `SIGTERM`, `SIGINT` or `SIGHUP`, by a thread of its own, after which the
//! signal is raised again, as it was not handled; and, so that a process
//! killed otherwise leaves its times, when a thread's last phase ends and a
//! second has passed since the last write. Its first line says which wrote
//! it. `scripts/phase-times.py` sums a run's files.

use std::collections::BTreeMap;
use fixpt_hash::HashMap;
use std::path::PathBuf;
use std::sync::atomic::{AtomicI32, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant};

/// Where the files go, if the times are kept.
static DIR: OnceLock<Option<PathBuf>> = OnceLock::new();
/// When the process began keeping them.
static START: OnceLock<Instant> = OnceLock::new();
/// The phases' names, by number, and the numbers by name (made on first
/// use, a `HashMap` having no `const` constructor).
type Names = (Vec<String>, Option<HashMap<String, u32>>);
static NAMES: Mutex<Names> = Mutex::new((Vec::new(), None));
/// Every thread's times, live or ended.
static THREADS: Mutex<Vec<Arc<Mutex<Thread>>>> = Mutex::new(Vec::new());
/// When the file was last written, in milliseconds from `START`.
static WRITTEN: AtomicU64 = AtomicU64::new(0);
/// The pipe the signal handler writes the signal's number to.
static SIGNAL_PIPE: AtomicI32 = AtomicI32::new(-1);

/// Whether the times are kept: `FIXPT_PHASE_TIMES` names a directory.
pub fn on() -> bool {
    DIR.get_or_init(begin).is_some()
}

/// The directory, the exit handler and the signals' set up, once.
fn begin() -> Option<PathBuf> {
    let dir = PathBuf::from(std::env::var_os("FIXPT_PHASE_TIMES").filter(|d| !d.is_empty())?);
    std::fs::create_dir_all(&dir).ok()?;
    START.get_or_init(Instant::now);
    // SAFETY: `at_exit` is an `extern "C" fn()` that does not unwind (it
    // catches panics) and touches only this module's state.
    unsafe {
        libc::atexit(at_exit);
    }
    signals();
    Some(dir)
}

/// A path's times.
#[derive(Default, Clone, Copy)]
struct Times {
    nanos: u64,
    entries: u64,
    collections: u64,
    copied: u64,
}

/// A thread's paths, as a tree: node 0 the thread outside every phase.
struct Thread {
    nodes: Vec<Node>,
    stack: Vec<usize>,
    last: Instant,
}

struct Node {
    phase: u32,
    parent: usize,
    kids: Vec<(u32, usize)>,
    times: Times,
}

impl Thread {
    fn new() -> Thread {
        Thread { nodes: vec![Node { phase: u32::MAX, parent: 0, kids: Vec::new(), times: Times::default() }], stack: vec![0], last: Instant::now() }
    }

    /// The time since the last change, the innermost phase's.
    fn charge(&mut self, now: Instant) {
        let top = *self.stack.last().expect("the root");
        self.nodes[top].times.nanos += now.saturating_duration_since(self.last).as_nanos() as u64;
        self.last = now;
    }

    /// Phase `phase` entered: whether it was pushed, not already the
    /// innermost (a compiler's compile within its own, say), which a path
    /// would only repeat.
    fn push(&mut self, phase: u32) -> bool {
        let top = *self.stack.last().expect("the root");
        if top != 0 && self.nodes[top].phase == phase {
            return false;
        }
        self.charge(Instant::now());
        let kid = match self.nodes[top].kids.iter().find(|(p, _)| *p == phase) {
            Some(&(_, k)) => k,
            None => {
                let k = self.nodes.len();
                self.nodes.push(Node { phase, parent: top, kids: Vec::new(), times: Times::default() });
                self.nodes[top].kids.push((phase, k));
                k
            }
        };
        self.nodes[kid].times.entries += 1;
        self.stack.push(kid);
        true
    }

    /// The innermost phase ended: whether none is left.
    fn pop(&mut self) -> bool {
        self.charge(Instant::now());
        if self.stack.len() > 1 {
            self.stack.pop();
        }
        self.stack.len() == 1
    }
}

thread_local! {
    static ME: Arc<Mutex<Thread>> = {
        let t = Arc::new(Mutex::new(Thread::new()));
        THREADS.lock().unwrap_or_else(|e| e.into_inner()).push(t.clone());
        t
    };
}

/// Phase `name`'s number.
fn number(name: &str) -> u32 {
    let mut names = NAMES.lock().unwrap_or_else(|e| e.into_inner());
    let (all, index) = &mut *names;
    let index = index.get_or_insert_with(HashMap::default);
    if let Some(&n) = index.get(name) {
        return n;
    }
    all.push(name.to_string());
    index.insert(name.to_string(), all.len() as u32 - 1);
    all.len() as u32 - 1
}

/// A phase entered, until this is dropped.
#[must_use = "the phase lasts while this lives"]
pub struct Phase {
    /// Whether it was pushed, and is to be popped.
    on: bool,
}

/// Phase `name` entered (nothing if the times are not kept).
pub fn enter(name: &str) -> Phase {
    if !on() {
        return Phase { on: false };
    }
    let n = number(name);
    Phase { on: ME.with(|t| t.lock().unwrap_or_else(|e| e.into_inner()).push(n)) }
}

/// Phase `prefix` + `name` entered: one of a family (`fx:` and an entry's
/// name), the name made only if the times are kept.
pub fn enter_named(prefix: &str, name: &str) -> Phase {
    if !on() {
        return Phase { on: false };
    }
    enter(&format!("{prefix}{name}"))
}

/// A collection begun, phase `name` (`gc:minor`, `gc:major`): counted as
/// one the phase below began.
pub fn collection(name: &str) -> Phase {
    let p = enter(name);
    if p.on {
        ME.with(|t| {
            let mut t = t.lock().unwrap_or_else(|e| e.into_inner());
            let below = t.stack[t.stack.len().saturating_sub(2)];
            t.nodes[below].times.collections += 1;
        });
    }
    p
}

impl Phase {
    /// Of a collection: the words it copied, counted to the phase below.
    pub fn copied(&self, words: u64) {
        if self.on {
            ME.with(|t| {
                let mut t = t.lock().unwrap_or_else(|e| e.into_inner());
                let below = t.stack[t.stack.len().saturating_sub(2)];
                t.nodes[below].times.copied += words;
            });
        }
    }
}

impl Drop for Phase {
    fn drop(&mut self) {
        if !self.on {
            return;
        }
        let empty = ME.with(|t| t.lock().unwrap_or_else(|e| e.into_inner()).pop());
        if empty {
            let start = *START.get().expect("begun");
            let now = start.elapsed().as_millis() as u64;
            let last = WRITTEN.load(Ordering::Relaxed);
            if now >= last + 1000 && WRITTEN.compare_exchange(last, now, Ordering::Relaxed, Ordering::Relaxed).is_ok() {
                write("snapshot");
            }
        }
    }
}

/// The process's file written now, `how` saying why: every thread's paths,
/// each open phase charged up to now. A thread whose times cannot be read
/// within a while (it holds them as a signal stops it) is left out.
fn write(how: &str) {
    let Some(Some(dir)) = DIR.get() else { return };
    let names = NAMES.lock().map(|n| n.0.clone()).unwrap_or_default();
    let threads: Vec<_> = THREADS.lock().map(|t| t.clone()).unwrap_or_default();
    let mut paths: BTreeMap<String, Times> = BTreeMap::new();
    let mut missed = 0;
    let now = Instant::now();
    for t in threads {
        let Some(t) = locked_soon(&t) else {
            missed += 1;
            continue;
        };
        let top = *t.stack.last().expect("the root");
        for (i, node) in t.nodes.iter().enumerate() {
            let mut times = node.times;
            if i == top {
                times.nanos += now.saturating_duration_since(t.last).as_nanos() as u64;
            }
            if i > 0 && times.nanos == 0 && times.entries == 0 && times.collections == 0 {
                continue;
            }
            let mut parts = Vec::new();
            let mut at = i;
            while at != 0 {
                parts.push(names.get(t.nodes[at].phase as usize).map_or("?", |s| s.as_str()));
                at = t.nodes[at].parent;
            }
            parts.push("other");
            parts.reverse();
            let e = paths.entry(parts.join(";")).or_default();
            e.nanos += times.nanos;
            e.entries += times.entries;
            e.collections += times.collections;
            e.copied += times.copied;
        }
    }
    let args: Vec<String> = std::env::args().collect();
    let mut out = format!("# fixpt phase times\t{how}\n# pid\t{}\n# args\t{}\n", std::process::id(), args.join(" "));
    if missed > 0 {
        out.push_str(&format!("# threads not read\t{missed}\n"));
    }
    out.push_str("# path\tnanos\tentries\tcollections\tcopied\n");
    for (p, t) in paths {
        out.push_str(&format!("{p}\t{}\t{}\t{}\t{}\n", t.nanos, t.entries, t.collections, t.copied));
    }
    let path = dir.join(format!("{}.tsv", std::process::id()));
    let tmp = path.with_extension("tmp");
    if std::fs::write(&tmp, out).is_ok() {
        let _ = std::fs::rename(&tmp, &path);
    }
}

/// `t`'s times, if they can be had within a tenth of a second.
fn locked_soon(t: &Mutex<Thread>) -> Option<std::sync::MutexGuard<'_, Thread>> {
    let until = Instant::now() + Duration::from_millis(100);
    loop {
        match t.try_lock() {
            Ok(g) => return Some(g),
            Err(std::sync::TryLockError::Poisoned(e)) => return Some(e.into_inner()),
            Err(std::sync::TryLockError::WouldBlock) if Instant::now() < until => std::thread::yield_now(),
            Err(_) => return None,
        }
    }
}

extern "C" fn at_exit() {
    let _ = std::panic::catch_unwind(|| write("exit"));
}

/// The signals that end a process by default, which the times are written
/// at: each handled where nothing else handles it, by a write of its number
/// to a pipe, which a thread of this module's reads.
fn signals() {
    let mut fds = [0 as libc::c_int; 2];
    // SAFETY: `fds` is two ints, as `pipe` writes.
    if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
        return;
    }
    SIGNAL_PIPE.store(fds[1], Ordering::Relaxed);
    let read = fds[0];
    let spawned = std::thread::Builder::new().name("fixpt-phases".into()).spawn(move || {
        let mut b = [0u8; 1];
        // SAFETY: `b` is one byte, as `read` is told.
        while unsafe { libc::read(read, b.as_mut_ptr().cast(), 1) } == 1 {
            let sig = b[0] as libc::c_int;
            let _ = std::panic::catch_unwind(|| write(&format!("signal {sig}")));
            // As though it had not been handled: its default, again.
            // SAFETY: setting a signal's default and raising it.
            unsafe {
                libc::signal(sig, libc::SIG_DFL);
                libc::raise(sig);
            }
        }
    });
    if spawned.is_err() {
        return;
    }
    for sig in [libc::SIGTERM, libc::SIGINT, libc::SIGHUP] {
        // SAFETY: `old` and `sa` are `sigaction`s, zeroed then set; the
        // handler only writes a byte to a pipe, which a signal handler may.
        unsafe {
            let mut old: libc::sigaction = std::mem::zeroed();
            if libc::sigaction(sig, std::ptr::null(), &mut old) != 0 || old.sa_sigaction != libc::SIG_DFL {
                continue;
            }
            let mut sa: libc::sigaction = std::mem::zeroed();
            sa.sa_sigaction = on_signal as *const () as usize;
            sa.sa_flags = libc::SA_RESTART;
            libc::sigemptyset(&mut sa.sa_mask);
            libc::sigaction(sig, &sa, std::ptr::null_mut());
        }
    }
}

extern "C" fn on_signal(sig: libc::c_int) {
    let fd = SIGNAL_PIPE.load(Ordering::Relaxed);
    let b = sig as u8;
    // SAFETY: `write` of one byte from the stack, async-signal-safe.
    unsafe {
        libc::write(fd, (&b as *const u8).cast(), 1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_phase_s_time_is_its_own_not_the_one_below() {
        let mut t = Thread::new();
        let (a, b) = (number("test-a"), number("test-b"));
        assert!(t.push(a));
        std::thread::sleep(Duration::from_millis(20));
        assert!(t.push(b));
        assert!(!t.push(b), "the innermost again: no deeper path");
        std::thread::sleep(Duration::from_millis(40));
        assert!(!t.pop());
        std::thread::sleep(Duration::from_millis(20));
        assert!(t.pop());
        let ta = t.nodes[1].times;
        let tb = t.nodes[2].times;
        assert_eq!((ta.entries, tb.entries), (1, 1));
        assert!(tb.nanos >= 40_000_000 && ta.nanos >= 40_000_000 && ta.nanos < 70_000_000, "{} {}", ta.nanos, tb.nanos);
        assert_eq!(t.nodes[2].parent, 1);
    }
}
