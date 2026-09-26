//! A probe, not a test: a huge zero-filled `Vec<u64>`, in safe code, as a
//! heap sized to its maximum up front would have. The allocator hands it to
//! the system, which commits a page only when it is touched and takes
//! everything back when it is freed (PLAN.md, "Regions that end").
//!
//!     cargo test --release -p fixpt-heap --test lazy -- --ignored --nocapture
fn resident() -> usize {
    let out = std::process::Command::new("ps").args(["-o", "rss=", "-p", &std::process::id().to_string()]).output();
    out.ok().and_then(|o| String::from_utf8_lossy(&o.stdout).trim().parse::<usize>().ok()).unwrap_or(0) * 1024
}
#[test]
#[ignore = "a probe: cargo test --release -p fixpt-heap --test lazy -- --ignored --nocapture"]
fn lazy() {
    for gb in [8usize, 64, 512, 4096] {
        let words = gb << 27;
        let before = resident();
        let t = std::time::Instant::now();
        let mut v: Vec<u64> = vec![0; words];
        let made = t.elapsed().as_secs_f64();
        let mid = resident();
        let t = std::time::Instant::now();
        let stride = 1 << 17; // 1 MB of words
        let mut n = 0;
        let mut i = 0;
        while i < words && n < 100_000 {
            v[i] = i as u64;
            i += stride;
            n += 1;
        }
        let wrote = t.elapsed().as_secs_f64();
        eprintln!(
            "{gb} GB: made in {:.3} ms, resident +{:.1} MB; {n} writes 1 MB apart in {:.1} ms, resident +{:.1} MB",
            made * 1e3,
            mid.saturating_sub(before) as f64 / 1e6,
            wrote * 1e3,
            resident().saturating_sub(mid) as f64 / 1e6
        );
        let t = std::time::Instant::now();
        drop(v);
        eprintln!("   dropped in {:.3} ms, resident now {:.1} MB", t.elapsed().as_secs_f64() * 1e3, resident() as f64 / 1e6);
    }
}
