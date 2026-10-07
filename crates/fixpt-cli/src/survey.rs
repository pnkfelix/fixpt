//! `fixpt regcode-survey`: what the register code the compilers make today
//! still leaves to a simplifier (`TODO.md` §44), counted in each program's
//! words, once the program has run (so that its globals hold their values).
//!
//! A forward pass over each word's register code keeps what is known of
//! RESULT, the registers and the frame slots: a constant, or a value
//! number (the same operation on the same values is the same value). What
//! is known is forgotten where a branch arrives, and registers where a call
//! is made: an under-count of what a simplifier that merges paths would
//! find. Each finding is also counted where it is in a loop (between a
//! backward branch's target and the branch), a crude stand-in for how
//! often it runs; these are static counts, not counts of what runs.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_heap::layout::cellular::{CLOSURE_WORD, GLOBAL_FIELDS, GLOBAL_VALUE, ROUTINES, WORD_CELL0, WORD_TWIN};
use fixpt_heap::layout::regcode::OPS;
use fixpt_heap::{Heap, Value};
use std::collections::{BTreeMap, HashMap, HashSet};

/// What one program's register code leaves: each kind of finding, in all
/// and in loops, and by operation.
#[derive(Default)]
struct Found {
    words: usize,
    cells: usize,
    kinds: BTreeMap<&'static str, (usize, usize)>,
    ops: BTreeMap<String, usize>,
    /// Where findings of the kind asked to be shown are: word and cell.
    show: Option<String>,
    shown: Vec<String>,
    here: String,
    /// Whether literal globals and modules' literal members count as
    /// known, as if propagated, and simple operations on constants are
    /// worked out, so that what they make is known too.
    propagate: bool,
}

impl Found {
    fn note(&mut self, kind: &'static str, looped: bool, op: Option<&str>) {
        if self.show.as_ref().is_some_and(|s| kind.contains(s.as_str())) && self.shown.len() < 40 {
            self.shown.push(format!("{} {kind} {}", self.here, op.unwrap_or("")));
        }
        let e = self.kinds.entry(kind).or_default();
        e.0 += 1;
        e.1 += looped as usize;
        if let Some(op) = op {
            *self.ops.entry(format!("{kind}: {op}")).or_default() += 1;
        }
    }
}

/// What is known of a place: a constant, or a value number.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Known {
    Const(u64, bool),
    Vn(u32),
}

/// The pass's state over one word.
struct Pass {
    result: Option<Known>,
    regs: HashMap<i64, Known>,
    slots: HashMap<i64, Known>,
    vns: HashMap<(String, Vec<Known>), u32>,
    tested: HashSet<Known>,
    next: u32,
}

impl Pass {
    fn fresh(&mut self) -> Known {
        self.next += 1;
        Known::Vn(self.next)
    }
    /// Where a branch arrives: nothing known, each place a value of its
    /// own (not the same unknown everywhere).
    fn forget(&mut self) {
        self.result = Some(self.fresh());
        self.regs.clear();
        self.slots.clear();
        self.tested.clear();
        for k in 0..=fixpt_heap::layout::regcode::REGS as i64 {
            let v = self.fresh();
            self.regs.insert(k, v);
        }
    }
    fn get(m: &HashMap<i64, Known>, k: i64) -> Option<Known> {
        m.get(&k).copied()
    }
    /// An operation `op` on `ins`: the same value as before if it was made
    /// before (a repeat), else a new one.
    fn op(&mut self, op: &str, ins: Vec<Known>, found: &mut Found, looped: bool) -> Known {
        let key = (op.to_string(), ins);
        if let Some(v) = self.vns.get(&key) {
            found.note("pure operation repeated", looped, Some(op));
            return Known::Vn(*v);
        }
        let v = self.fresh();
        if let Known::Vn(n) = v {
            self.vns.insert(key, n);
        }
        v
    }
}

/// Whether a constant is an immediate (not an object in the heap).
fn immediate(v: Value) -> bool {
    !v.is_bloblet() && !v.is_pair()
}

/// The identity element of `op` on the right, if it has one.
fn identity(op: &str) -> Option<i64> {
    match op {
        "int-add" | "int-sub" | "+" | "-" => Some(0),
        "%fx26-mul" => Some(1),
        _ => None,
    }
}

/// `op` worked out on two immediates `x` and `y`, where it is one of the
/// simple ones and they are fixnums (or any immediates, for `eq`).
fn fold(op: &str, x: u64, y: u64) -> Option<Value> {
    let fx = |r: u64| (r & 7 == 0).then_some((r as i64) >> 3);
    let small = |n: i64| (n.abs() < 1 << 30).then_some(n);
    Some(match op {
        "eq" => Value::boolean(x == y),
        "int-eq" => Value::boolean(fx(x)? == fx(y)?),
        "int-less" | "<" => Value::boolean(fx(x)? < fx(y)?),
        "int-add" | "+" => Value::fixnum(small(fx(x)? + fx(y)?)?),
        "int-sub" | "-" => Value::fixnum(small(fx(x)? - fx(y)?)?),
        "%fx26-mul" => Value::fixnum(small(fx(x)?.checked_mul(fx(y)?)?)?),
        _ => return None,
    })
}

/// Every word with register code that `start` reaches, through its cells,
/// its register code's, closures and the globals they name.
fn words_of(heap: &Heap, start: Value) -> Vec<Value> {
    let closure = fixpt_heap::layout::kind("cellular-closure");
    let (mut todo, mut seen, mut out) = (vec![start], HashSet::new(), Vec::new());
    let push = |v: Value, todo: &mut Vec<Value>| {
        if heap.is_cellular_word(v) {
            todo.push(v);
        } else if v.is_bloblet() && heap.bloblet_kind(v) == closure {
            todo.push(heap.bloblet_slot(v, CLOSURE_WORD));
        } else if v.is_bloblet() && heap.bloblet_kind(v) == fixpt_heap::layout::kind("bloblet") && heap.bloblet_head(v).fields >= GLOBAL_FIELDS {
            let g = heap.bloblet_slot(v, GLOBAL_VALUE);
            if g.is_bloblet() && heap.bloblet_kind(g) == closure {
                todo.push(heap.bloblet_slot(g, CLOSURE_WORD));
            }
        }
    };
    while let Some(w) = todo.pop() {
        if !seen.insert(w.raw()) || !heap.is_cellular_word(w) {
            continue;
        }
        for k in WORD_CELL0..=heap.bloblet_head(w).fields {
            push(heap.bloblet_slot(w, k), &mut todo);
        }
        let rw = heap.bloblet_slot(w, WORD_TWIN);
        if heap.is_register_word(rw) {
            out.push(rw);
            for k in WORD_CELL0..=heap.bloblet_head(rw).fields {
                push(heap.bloblet_slot(rw, k), &mut todo);
            }
        }
    }
    out
}

/// One word's register code, surveyed into `found`.
fn survey_word(heap: &Heap, rw: Value, found: &mut Found) {
    let fields = heap.bloblet_head(rw).fields;
    let cell = |k: usize| heap.bloblet_slot(rw, k);
    // Where each instruction starts, where branches arrive, and what is in
    // a loop.
    let mut starts = Vec::new();
    let mut k = WORD_CELL0;
    while k <= fields {
        starts.push(k - WORD_CELL0);
        k += 1 + OPS[cell(k).as_fixnum() as usize].1;
    }
    let n = fields + 1 - WORD_CELL0;
    let (mut target, mut looped) = (vec![false; n + 1], vec![false; n + 1]);
    for &at in &starts {
        let (name, ops, _) = OPS[cell(WORD_CELL0 + at).as_fixnum() as usize];
        if matches!(name, "branch" | "branchf" | "brancht" | "global-guard") {
            let to = (at as i64 + 1 + ops as i64 + cell(WORD_CELL0 + at + ops).as_fixnum()) as usize;
            target[to.min(n)] = true;
            if to <= at {
                for l in looped.iter_mut().take(at + 1).skip(to) {
                    *l = true;
                }
            }
        }
    }
    found.words += 1;
    found.cells += n;
    let mut p = Pass { result: None, regs: HashMap::new(), slots: HashMap::new(), vns: HashMap::new(), tested: HashSet::new(), next: 0 };
    let routine = |v: Value| ROUTINES.get(v.as_fixnum() as usize).map_or("?", |r| r.0).to_string();
    let prim = |v: Value| fixpt_runtime::PRIMITIVES.get(v.as_fixnum() as usize).map_or("?", |d| d.name).to_string();
    // What RESULT was loaded from, for `global g; field k`: the global.
    let mut from_global: Option<Value> = None;
    let wname = heap.symbol_name(heap.bloblet_slot(rw, fixpt_heap::layout::cellular::WORD_NAME));
    for &at in &starts {
        if target[at] {
            p.forget();
        }
        found.here = format!("{wname}@{at}");
        let lp = looped[at];
        let (name, _, _) = OPS[cell(WORD_CELL0 + at).as_fixnum() as usize];
        let o = |i: usize| cell(WORD_CELL0 + at + 1 + i);
        let was_global = from_global.take();
        match name {
            "const" => p.result = Some(Known::Const(o(0).raw(), immediate(o(0)))),
            "global" => {
                let g = o(0);
                let v = heap.bloblet_slot(g, GLOBAL_VALUE);
                from_global = Some(g);
                p.result = Some(p.fresh());
                if immediate(v) {
                    found.note("global load of a literal", lp, None);
                    if found.propagate {
                        p.result = Some(Known::Const(v.raw(), true));
                    }
                }
            }
            "field" => {
                if let Some(g) = was_global {
                    let m = heap.bloblet_slot(g, GLOBAL_VALUE);
                    let k = o(0).as_fixnum() as usize;
                    if m.is_bloblet() && heap.bloblet_kind(m) != fixpt_heap::layout::kind("cellular-closure") && k <= heap.bloblet_head(m).fields && immediate(heap.bloblet_slot(m, k)) {
                        found.note("global module's literal member read", lp, None);
                        if found.propagate {
                            p.result = Some(Known::Const(heap.bloblet_slot(m, k).raw(), true));
                            continue;
                        }
                    }
                }
                p.result = Some(match p.result {
                    Some(r) => p.op(&format!("field {}", o(0).as_fixnum()), vec![r], &mut Found::default(), lp),
                    None => p.fresh(),
                });
            }
            "reg" => p.result = Some(Pass::get(&p.regs, o(0).as_fixnum()).unwrap_or_else(|| p.fresh())),
            "setreg" => match p.result {
                Some(v) => {
                    p.regs.insert(o(0).as_fixnum(), v);
                }
                None => {
                    p.regs.remove(&o(0).as_fixnum());
                }
            },
            "movereg" => match Pass::get(&p.regs, o(0).as_fixnum()) {
                Some(v) => {
                    p.regs.insert(o(1).as_fixnum(), v);
                }
                None => {
                    p.regs.remove(&o(1).as_fixnum());
                }
            },
            "stack" => p.result = Some(Pass::get(&p.slots, o(0).as_fixnum()).unwrap_or_else(|| p.fresh())),
            "setstk" => match p.result {
                Some(v) => {
                    p.slots.insert(o(0).as_fixnum(), v);
                }
                None => {
                    p.slots.remove(&o(0).as_fixnum());
                }
            },
            "load" => match Pass::get(&p.slots, o(1).as_fixnum()) {
                Some(v) => {
                    p.regs.insert(o(0).as_fixnum(), v);
                }
                None => {
                    p.regs.remove(&o(0).as_fixnum());
                }
            },
            "store" => match Pass::get(&p.regs, o(0).as_fixnum()) {
                Some(v) => {
                    p.slots.insert(o(1).as_fixnum(), v);
                }
                None => {
                    p.slots.remove(&o(1).as_fixnum());
                }
            },
            "save" => p.slots.clear(),
            "op1" | "prim1" | "op2" | "prim2" | "op2imm" | "prim2imm" => {
                let op = if name.starts_with("op") { routine(o(0)) } else { prim(o(0)) };
                let a = p.result;
                let b = match name {
                    "op2" | "prim2" => Pass::get(&p.regs, o(1).as_fixnum()),
                    "op2imm" | "prim2imm" => Some(Known::Const(o(1).raw(), immediate(o(1)))),
                    _ => None,
                };
                let two = !name.ends_with('1');
                let consts = |x: Option<Known>| matches!(x, Some(Known::Const(_, true)));
                if consts(a) && (!two || consts(b)) {
                    found.note("operation on constants", lp, Some(&op));
                } else if two
                    && let Some(id) = identity(&op)
                    && b == Some(Known::Const(Value::fixnum(id).raw(), true))
                {
                    found.note("identity", lp, Some(&op));
                }
                let worked = match (found.propagate, a, b) {
                    (true, Some(Known::Const(x, true)), Some(Known::Const(y, true))) if two => fold(&op, x, y),
                    _ => None,
                };
                p.result = match (a, b, two) {
                    _ if worked.is_some() => worked.map(|v: Value| Known::Const(v.raw(), true)),
                    (Some(a), Some(b), true) => Some(p.op(&op, vec![a, b], found, lp)),
                    (Some(a), _, false) => Some(p.op(&op, vec![a], found, lp)),
                    _ => Some(p.fresh()),
                };
            }
            "branchf" | "brancht" => match p.result {
                Some(Known::Const(..)) => found.note("branch on a constant", lp, None),
                Some(v) => {
                    if !p.tested.insert(v) {
                        found.note("test repeated on a path", lp, None);
                    }
                }
                None => {}
            },
            "args" | "vargs" => {
                for k in 1..=fixpt_heap::layout::regcode::REGS as i64 {
                    let v = p.fresh();
                    p.regs.insert(k, v);
                }
            }
            "lexical" | "global-guard" | "pop" | "branch" | "return" | "setglbl" | "setfield" => {
                if name == "lexical" {
                    p.result = Some(p.fresh());
                }
            }
            // A call, an allocation or a call-out: RESULT new, and the
            // registers forgotten.
            _ => {
                p.result = Some(p.fresh());
                p.regs.clear();
            }
        }
    }
}

/// The survey of one program's text: compiled by the Rust compiler with
/// register code, run, and its words surveyed.
fn survey(text: &str, propagate: bool, show: Option<String>) -> Result<Found, String> {
    let (c, tops) = crate::bench::checked(text)?;
    let mut s = Fx26Session::with_backend(Backend::Bytecode).map_err(|e| e.message)?;
    s.scheme.engine.set_step_limit(None);
    let mut found = Found { propagate, show, ..Found::default() };
    s.scheme.scope(|sc| {
        let w = sc.make(|m| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, text);
            comp.registers = true;
            comp.program(&tops).unwrap_or(Value::FALSE)
        });
        sc.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_registers);
        let none = sc.make(|_| Value::NULL);
        sc.call_global("%run-word", &[w, none]).map_err(|e| e.to_string())?;
        sc.make(|m| {
            let w = m.get(w);
            let heap = m.heap();
            for rw in words_of(heap, w) {
                survey_word(heap, rw, &mut found);
            }
            Value::NULL
        });
        Ok::<(), String>(())
    })?;
    Ok(found)
}

/// `fixpt regcode-survey [--propagate] [--show KIND] [--front-end] [FILE...]`.
pub fn command(args: &[String]) -> i32 {
    let mut programs = Vec::new();
    let mut files: Vec<std::path::PathBuf> = Vec::new();
    let (mut propagate, mut show) = (false, None);
    let mut args = args.iter();
    while let Some(a) = args.next() {
        if a == "--propagate" {
            propagate = true;
        } else if a == "--show" {
            show = args.next().cloned();
        } else if a == "--front-end" {
            programs.push(("front end".to_string(), fixpt_fx26::bootstrap_program()));
        } else {
            files.push(a.into());
        }
    }
    if files.is_empty() && programs.is_empty() {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../fixpt-fx26/tests/programs/bench");
        let Ok(entries) = std::fs::read_dir(dir) else { return 2 };
        files = entries.filter_map(|e| Some(e.ok()?.path())).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
        files.sort();
    }
    for path in files {
        let Ok(text) = std::fs::read_to_string(&path) else {
            eprintln!("fixpt regcode-survey: cannot read {}", path.display());
            return 1;
        };
        programs.push((path.file_stem().map_or_else(|| path.display().to_string(), |s| s.to_string_lossy().to_string()), text));
    }
    let kinds = [
        "operation on constants",
        "branch on a constant",
        "identity",
        "test repeated on a path",
        "pure operation repeated",
        "global load of a literal",
        "global module's literal member read",
    ];
    let mut totals = Found::default();
    println!("| program | words | cells | {} |", kinds.join(" | "));
    println!("| --- | ---: | ---: |{}", " ---: |".repeat(kinds.len()));
    for (name, text) in &programs {
        match survey(text, propagate, show.clone()) {
            Ok(f) => {
                for s in &f.shown {
                    println!("  {s}");
                }
                let row: Vec<String> = kinds.iter().map(|k| f.kinds.get(k).map_or("0".into(), |(a, l)| format!("{a} ({l})"))).collect();
                println!("| {name} | {} | {} | {} |", f.words, f.cells, row.join(" | "));
                totals.words += f.words;
                totals.cells += f.cells;
                for (k, (a, l)) in f.kinds {
                    let e = totals.kinds.entry(k).or_default();
                    e.0 += a;
                    e.1 += l;
                }
                for (k, n) in f.ops {
                    *totals.ops.entry(k).or_default() += n;
                }
            }
            Err(e) => println!("| {name} | !! {e} |"),
        }
    }
    println!("\n(n) of each: in a loop. By operation, over all:");
    let mut ops: Vec<_> = totals.ops.into_iter().collect();
    ops.sort_by(|a, b| b.1.cmp(&a.1));
    for (k, n) in ops.iter().take(30) {
        println!("  {n:>6}  {k}");
    }
    0
}
