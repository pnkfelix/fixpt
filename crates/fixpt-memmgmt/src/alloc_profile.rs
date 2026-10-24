//! Who allocates from Rust (`TODO.md` §126): with `FIXPT_ALLOC_PROFILE=N`,
//! every `N`th allocation or reallocation through the global allocator
//! has its caller's stack taken, and at the end the stacks are told on the
//! standard error, grouped by their first frames in Fixpt's own crates,
//! most first. The heap FX-26 programs run on never comes here (it
//! allocates in its own reserved memory); what does is Rust's: vectors,
//! maps and strings of the compilers, the checker and the call-outs. Off,
//! it costs a load and a test on each allocation.

use std::alloc::{GlobalAlloc, Layout, System};
use std::backtrace::Backtrace;
use std::cell::Cell;
use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

/// The global allocator: the system's, counted, and sampled when asked.
pub struct Counting;

/// The sampling period, 0 for none (`start`), and the allocations so far.
static PERIOD: AtomicU64 = AtomicU64::new(0);
static COUNT: AtomicU64 = AtomicU64::new(0);
/// Each sample's stack and size.
static SAMPLES: Mutex<Vec<(Backtrace, usize)>> = Mutex::new(Vec::new());

thread_local! {
    /// Whether this thread is taking a sample, whose own allocations are
    /// not sampled.
    static BUSY: Cell<bool> = const { Cell::new(false) };
}

/// `FIXPT_ALLOC_PROFILE`, read once, before anything is sampled: reading
/// the environment allocates, which the allocator cannot do itself.
pub fn start() {
    let n = std::env::var("FIXPT_ALLOC_PROFILE").ok().and_then(|n| n.parse::<u64>().ok()).unwrap_or(0);
    PERIOD.store(n, Ordering::Relaxed);
}

fn note(size: usize) {
    let period = PERIOD.load(Ordering::Relaxed);
    if period == 0 || !COUNT.fetch_add(1, Ordering::Relaxed).is_multiple_of(period) {
        return;
    }
    let _ = BUSY.try_with(|busy| {
        if busy.replace(true) {
            return;
        }
        let stack = Backtrace::force_capture();
        if let Ok(mut s) = SAMPLES.lock() {
            s.push((stack, size));
        }
        busy.set(false);
    });
}

// SAFETY: each call is the system allocator's, as given; `note` only
// counts, and takes a sample with this thread's own allocations not
// sampled again.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        note(layout.size());
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        note(layout.size());
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        note(new_size);
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

/// The samples, told on the standard error, if any were taken: each
/// stack's first three frames in Fixpt's crates (`fixpt`), past the
/// allocator's and the standard library's, with how many allocations and
/// bytes they stand for (the samples times the period).
pub fn report() {
    let period = PERIOD.load(Ordering::Relaxed);
    if period == 0 {
        return;
    }
    BUSY.with(|b| b.set(true));
    let samples = std::mem::take(&mut *SAMPLES.lock().expect("not poisoned"));
    let mut by: HashMap<String, (u64, u64)> = HashMap::new();
    for (stack, size) in &samples {
        let text = stack.to_string();
        let frames: Vec<&str> = text
            .lines()
            .filter_map(|l| l.trim_start().split_once(": ").filter(|(n, _)| n.bytes().all(|b| b.is_ascii_digit())).map(|(_, f)| f))
            .filter(|f| f.contains("fixpt") && !f.contains("alloc_profile"))
            .take(3)
            .collect();
        let e = by.entry(frames.join("\n    <- ")).or_default();
        e.0 += period;
        e.1 += period * *size as u64;
    }
    let mut rows: Vec<_> = by.into_iter().collect();
    rows.sort_by(|a, b| b.1.0.cmp(&a.1.0));
    let total = COUNT.load(Ordering::Relaxed);
    eprintln!("; allocations: {total}, sampled one in {period}: {} samples", samples.len());
    for (frames, (n, bytes)) in rows.iter().take(30) {
        eprintln!("; {n:>12} allocations, {bytes:>14} bytes: {frames}");
    }
}
