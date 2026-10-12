//! `TODO.md` §86, stage 1: how far an inferred "may fail" would spread, in
//! the front end written in FX-26 and in the benchmark ports
//! (`fixpt_fx26::debts`). `cargo run --release -p fixpt-fx26 --example
//! debts [FILE.fx …]`; with no files, the front end and every port under
//! `mllang-bench/fx` and `scheme-bench`.

use fixpt_fx26::Checker;
use fixpt_fx26::debts::{Debt, Summary, indexes, summarize, units};
use fixpt_read::FileId;

/// `text` checked as one program, with operand types kept: its summary,
/// or why it could not be checked.
fn measure(text: &str) -> Result<(Summary, Summary), String> {
    let mut c = Checker::new();
    c.record_operands = true;
    let forms = c.read_in(FileId(0), text).map_err(|e| e.message)?;
    let done = c.declare_ahead(&forms).map_err(|e| e.message)?;
    let mut tops = Vec::new();
    for (f, done) in forms.iter().zip(done) {
        if !done {
            tops.extend(c.top_all(f).map_err(|e| e.message)?);
        }
    }
    let us = units(&c, &tops);
    Ok((summarize(&us, &|_| false), summarize(&us, &indexes)))
}

fn add(into: &mut Summary, s: Summary) {
    into.units += s.units;
    into.by_call += s.by_call;
    into.only_given += s.only_given;
    for (k, n) in s.by_worst {
        *into.by_worst.entry(k).or_default() += n;
    }
    for (k, n) in s.ops {
        *into.ops.entry(k).or_default() += n;
    }
}

fn show(title: &str, s: &Summary) {
    let n = |k: Option<Debt>| s.by_worst.get(&k).copied().unwrap_or(0);
    let pct = |k: usize| if s.units == 0 { 0.0 } else { 100.0 * k as f64 / s.units as f64 };
    let free = n(None) - s.by_call - s.only_given;
    println!("\n## {title}: {} definitions\n", s.units);
    println!("| class                                         | definitions |      % |");
    println!("| --------------------------------------------- | -----------:| ------:|");
    for (label, k) in [
        ("failure-free, and everything it calls", free),
        ("failure-free, but calls a procedure it is given", s.only_given),
        ("failure-free itself, calls one that may fail", s.by_call),
        ("internal debt only (owed)", n(Some(Debt::Owed))),
        ("passes debt to callers (via a parameter)", n(Some(Debt::Passed))),
        ("states debt (calls `error`)", n(Some(Debt::Stated))),
    ] {
        println!("| {label:<45} | {k:>11} | {:>5.1}% |", pct(k));
    }
    let mut ops: Vec<(&(String, Debt), &usize)> = s.ops.iter().collect();
    ops.sort_by(|a, b| b.1.cmp(a.1).then(a.0.0.cmp(&b.0.0)));
    println!("\n| operation            | stands     | sites |");
    println!("| -------------------- | ---------- | -----:|");
    for ((op, d), k) in ops.iter().take(25) {
        println!("| {op:<20} | {:<10} | {k:>5} |", format!("{d:?}"));
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
    let ports: Vec<String> = if args.is_empty() {
        let mut v = Vec::new();
        for d in ["mllang-bench/fx/mlton", "mllang-bench/fx/ocaml", "mllang-bench/fx/benchmarksgame", "scheme-bench"] {
            let mut fs: Vec<String> = std::fs::read_dir(format!("{root}/{d}")).unwrap().filter_map(|e| {
                let p = e.ok()?.path();
                (p.extension()? == "fx").then(|| p.display().to_string())
            }).collect();
            fs.sort();
            v.extend(fs);
        }
        v
    } else {
        args
    };
    if std::env::args().len() == 1 {
        match measure(&fixpt_fx26::front_end()) {
            Ok((s, b)) => {
                show("The front end written in FX-26", &s);
                show("The front end, were every index proved in bounds", &b);
            }
            Err(e) => println!("the front end: {e}"),
        }
    }
    let (mut all, mut bounded) = (Summary::default(), Summary::default());
    let (mut measured, mut failed) = (0, Vec::new());
    for p in &ports {
        let text = std::fs::read_to_string(p).unwrap();
        match measure(&text) {
            Ok((s, b)) => {
                measured += 1;
                add(&mut all, s);
                add(&mut bounded, b);
            }
            Err(e) => failed.push(format!("{p}: {}", e.lines().next().unwrap_or(""))),
        }
    }
    show(&format!("The benchmark ports ({measured} of {})", ports.len()), &all);
    show("The ports, were every index proved in bounds", &bounded);
    for f in failed {
        println!("not measured: {f}");
    }
}
