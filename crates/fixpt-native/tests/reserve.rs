//! A probe, not a test: how much address space this system lets a process
//! reserve, and whether memory it promises is there when written. For the
//! segmented heap (PLAN.md, "Regions that end"), which reserves one large
//! range up front and makes segments of it usable as it grows.
//!
//!     cargo test --release -p fixpt-native --test reserve -- --ignored --nocapture
//!
//! It writes at most `TOUCH_BUDGET` bytes' worth of pages in any one phase,
//! and frees each range before the next, so as not to push the machine
//! into swapping.

use fixpt_native::reserve::{Reservation, probe};
use std::time::Instant;

const GB: usize = 1 << 30;
const TOUCH_BUDGET: usize = 2 * GB;

/// This process's resident size in bytes, as `ps` reports it.
fn resident() -> usize {
    let out = std::process::Command::new("ps").args(["-o", "rss=", "-p", &std::process::id().to_string()]).output();
    out.ok().and_then(|o| String::from_utf8_lossy(&o.stdout).trim().parse::<usize>().ok()).unwrap_or(0) * 1024
}

/// The largest power of two from 1 GB up for which `ok` holds.
fn largest(ok: impl Fn(usize) -> bool) -> usize {
    let (mut len, mut best) = (GB, 0);
    while len <= 1 << 50 && ok(len) {
        best = len;
        len *= 2;
    }
    best
}

fn human(n: usize) -> String {
    match n {
        n if n >= GB => format!("{} GB", n / GB),
        n if n >= 1 << 20 => format!("{} MB", n >> 20),
        n => format!("{} KB", n >> 10),
    }
}

#[test]
#[ignore = "a probe: cargo test --release -p fixpt-native --test reserve -- --ignored --nocapture"]
fn reserve() {
    let pg = probe::page();
    eprintln!("page size {pg} bytes; resident at start {:.1} MB", resident() as f64 / 1e6);

    let none = largest(|n| Reservation::new(n).is_some());
    eprintln!("largest reservation with no access: {} GB (2^{})", none / GB, none.trailing_zeros());
    let rw = largest(probe::can_map_writable);
    eprintln!("largest mapping readable and writable, untouched: {} GB (2^{})", rw / GB, rw.trailing_zeros());

    // A reservation made usable piece by piece, as the heap would.
    let len = none.min(1 << 40);
    let mut r = Reservation::new(len).expect("reserved again");
    let (mut committed, seg) = (0, 64 << 20);
    while committed < 64 * GB && r.commit(committed, seg) {
        committed += seg;
    }
    eprintln!("of a {} GB reservation, {} GB made writable in 64 MB segments", len / GB, committed / GB);
    drop(r);

    // Writes at a stride across a large range made writable at once: does
    // each page written become resident, and at what cost?
    let span = none.min(16 << 40);
    eprintln!("\nstrided writes across {} GB made writable at once, one word per stride:", span / GB);
    eprintln!("| stride | writes | span written | time | per write | resident gained |");
    for stride in [pg, 4 * pg, 1 << 20, 16 << 20, 256 << 20, GB, 64 * GB] {
        let writes = (span / stride).min(TOUCH_BUDGET / pg);
        if writes == 0 {
            continue;
        }
        let mut r = Reservation::new(span).expect("reserved again");
        assert!(r.commit(0, span), "made writable at once");
        let before = resident();
        let t = Instant::now();
        for i in 0..writes {
            r.write_word(i * stride, (i as u64) ^ 0x9e37_79b9_7f4a_7c15);
        }
        let dt = t.elapsed().as_secs_f64();
        let gained = resident().saturating_sub(before);
        eprintln!(
            "| {} | {writes} | {:.1} GB | {:.1} ms | {:.0} ns | {:.1} MB |",
            human(stride),
            (writes * stride) as f64 / GB as f64,
            dt * 1e3,
            dt * 1e9 / writes as f64,
            gained as f64 / 1e6
        );
    }

    // Every word of the pages written, with data that does not compress:
    // are they really there?
    let dense = TOUCH_BUDGET;
    let mut r = Reservation::new(dense).expect("reserved");
    assert!(r.commit(0, dense));
    let before = resident();
    let t = Instant::now();
    let mut x = 0x2545_f491_4f6c_dd1du64;
    for i in 0..dense / 8 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        r.write_word(8 * i, x);
    }
    let dt = t.elapsed().as_secs_f64();
    eprintln!(
        "\n{} GB written densely with random words: {:.0} ms, resident gained {:.1} MB",
        dense / GB,
        dt * 1e3,
        resident().saturating_sub(before) as f64 / 1e6
    );
}
