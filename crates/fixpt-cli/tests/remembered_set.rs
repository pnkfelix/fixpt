//! The remembered set's bound (`TODO.md` §276): a minor collection is due
//! once stores of young values have made half a nursery's words of clean
//! cards dirty, so that none scans more; on every machine, each of whose
//! write barriers marks and counts as `Heap::set_slot` does.

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");


/// A nursery of 4096 words: a budget of 4096 / 2 / 64 = 32 cards.
const NURSERY: &str = "4096";
const BUDGET: u64 = 32;

/// Fresh lists stored into 1000 old references, 10 times over, on machine
/// `m`: more cards made dirty, each time, than the budget.
fn bounded_on(m: &str) {
    let path = format!("{}/tests/programs/gc/cards.fx", env!("CARGO_MANIFEST_DIR"));
    let out = Command::new(FIXPT)
        .args(["--machine", m, "eval", &path])
        .env("FIXPT_NURSERY", NURSERY)
        .env("FIXPT_GC_TRACE", "1")
        .env("FIXPT_VERIFY_BARRIER", "1")
        .output()
        .expect("runs");
    let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    assert!(stdout.lines().last().is_some_and(|l| l.starts_with("10000 : int")), "{m}: {stdout}{stderr}");
    let cards: Vec<u64> = stderr
        .lines()
        .filter(|l| l.starts_with("; gc minor"))
        .filter_map(|l| l.strip_suffix(" dirty cards")?.rsplit(' ').next()?.parse().ok())
        .collect();
    assert!(cards.len() >= 10, "{m}: {} minor collections", cards.len());
    let most = cards.iter().copied().max().unwrap_or(0);
    assert!(most <= BUDGET, "{m}: a minor collection scanned {most} dirty cards, past the budget of {BUDGET}");
    assert!(cards.contains(&BUDGET), "{m}: no minor collection the budget's ({cards:?})");
}

macro_rules! on_each {
    ($($test:ident: $m:literal),* $(,)?) => {
        $( #[test] fn $test() { bounded_on($m) } )*
    };
}
on_each!(
    on_rs_scheme_vm: "rs-scheme-vm",
    on_fx_ast_eval: "fx-ast-eval",
    on_fx_cells_rsinterp: "fx-cells-rsinterp",
    on_fx_cells_rsinterp_nativecc: "fx-cells-rsinterp-nativecc",
    on_fx_cells_asminterp: "fx-cells-asminterp",
    on_fx_cells_rsjit_cellcc: "fx-cells-rsjit-cellcc",
    on_fx_cells_fxjit_cellcc: "fx-cells-fxjit-cellcc",
    on_fx_cells_stencils_cellcc: "fx-cells-stencils-cellcc",
    on_fx_regs_rsjit_cellcc: "fx-regs-rsjit-cellcc",
    on_fx_regs_fxjit_cellcc: "fx-regs-fxjit-cellcc",
    on_fx_regs_rsjit_nativecc: "fx-regs-rsjit-nativecc",
    on_fx_regs_fxjit_nativecc: "fx-regs-fxjit-nativecc",
);
