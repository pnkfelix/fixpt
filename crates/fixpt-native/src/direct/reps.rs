//! Where native code keeps `i64`, `u64` and `f64` values: raw, as the
//! machine's 64 bits (an `f64`'s moved into a `d` register for each
//! operation), in registers only (`RESULT`, REG1…REG8), and as the value they are
//! everywhere else (the exact integer: a fixnum, or a bignum past 60 bits).
//! Register code does not say which: it is the same for every machine, and
//! its registers hold values. This pass says, instruction by instruction,
//! forward over the procedure's register code:
//!
//! - an operation of `i64` or `u64` (`prim1`, `prim2`, `prim2imm` of such a
//!   primitive) takes its operands raw and gives its value raw, a
//!   comparison and `T->int` excepted; so does one of `f64` the machine does
//!   exactly as IEEE says (`raw_op`), a comparison excepted;
//! - `reg`, `setreg` and `movereg` move a register as it is;
//! - anything else that reads a register reads it as a value: a raw one is
//!   boxed first, in its register. So nothing raw is stored in a frame,
//!   passed, returned or kept in the heap, and a collection never sees one.
//!   (A call or call-out leaves the registers undefined: register code keeps
//!   nothing in them across one.)
//!
//! Where ways meet, a register raw on one is raw after (one that is a value
//! on another is unboxed on that way): a loop's variable stays raw around
//! the loop.

use fixpt_heap::layout::cellular::ROUTINES;
use fixpt_heap::layout::regcode::OPS;
use fixpt_heap::Value;

/// How a register holds its value.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(super) enum Rep {
    /// Nothing defined here, as far as this pass knows.
    Undefined,
    /// A value, as everything but native code sees it.
    Value,
    /// An `i64` (signed) or `u64`'s 64 bits.
    Raw { signed: bool },
    /// An `f64`'s 64 bits.
    F64,
    /// A value known to be a fixnum: in a procedure's fixnum version only
    /// (`fast`), where an `int` operation's operands so known are not
    /// tested, and its value, overflow going over to the general version,
    /// is one.
    Fix,
}

impl Rep {
    fn raw(self) -> bool {
        matches!(self, Rep::Raw { .. } | Rep::F64)
    }
}

/// `RESULT`, then REG1…REG8.
pub(super) type Reps = [Rep; 9];

/// Where two ways meet.
pub(super) fn join(a: &Reps, b: &Reps) -> Reps {
    std::array::from_fn(|r| match (a[r], b[r]) {
        (Rep::Undefined, x) | (x, Rep::Undefined) => x,
        (x, _) | (_, x) if x.raw() => x,
        // Optimistic: known where either way knows it, the other way testing
        // it (`checks`), if it is live.
        (Rep::Fix, _) | (_, Rep::Fix) => Rep::Fix,
        _ => Rep::Value,
    })
}

/// The registers a way into `to` must unbox, and to what: a value there,
/// raw at `to`.
pub(super) fn unboxes(from: &Reps, to: &Reps) -> Vec<(usize, Rep)> {
    (0..9).filter(|&r| matches!(from[r], Rep::Value | Rep::Fix) && to[r].raw()).map(|r| (r, to[r])).collect()
}

/// The registers a way into `to` must test for a fixnum, in a fixnum
/// version: a value there, known at `to`, and `live` there.
pub(super) fn checks(from: &Reps, to: &Reps, live: &[bool; 9]) -> Vec<usize> {
    (0..9).filter(|&r| from[r] == Rep::Value && to[r] == Rep::Fix && live[r]).collect()
}

/// An operation native code does on raw operands, by its primitive's name:
/// an `i64` or `u64` one (`%fx26-u64*`, `%fx26-int->i64`), or one of `f64`
/// the machine does exactly as the runtime does (arithmetic, `abs`, `neg`,
/// `sqrt`, the roundings, comparisons: IEEE's own; not `min` and `max`,
/// whose signed zeros may differ, nor the elementary functions).
#[derive(Clone, Copy)]
pub(super) enum RawOp<'n> {
    /// Whether signed, and the name after the type (`*`, `-xor`; `from` for
    /// `int->T`).
    Int { signed: bool, what: &'n str },
    /// The name after `f64`.
    F64 { what: &'n str },
}

pub(super) fn raw_op(name: &str) -> Option<RawOp<'_>> {
    let rest = name.strip_prefix("%fx26-")?;
    if rest == "int->f64" {
        return Some(RawOp::F64 { what: "from-int" });
    }
    if let Some(what) = rest.strip_prefix("f64") {
        let native = ["+", "-", "*", "/", "-abs", "-neg", "-sqrt", "-floor", "-ceiling", "-truncate", "-round", "<", "<=", ">", ">=", "=", "->int"];
        return native.contains(&what).then_some(RawOp::F64 { what });
    }
    let (t, what) = match rest.strip_prefix("int->") {
        Some(t) => (t, "from"),
        None => (rest.get(..3)?, &rest[3..]),
    };
    let signed = match t {
        "i64" => true,
        "u64" => false,
        _ => return None,
    };
    Some(RawOp::Int { signed, what })
}

/// What a raw operation takes and gives. An integer one: its first operand
/// raw (all of them, `int->T`'s int too, which unboxing wraps); its second
/// raw but for a shift's count; its value raw but for a comparison's and
/// `T->int`'s. An `f64` one: its operands raw, and its value but for a
/// comparison's.
fn raw_shape(op: RawOp<'_>) -> (Rep, Rep, Rep) {
    let compare = |w: &str| matches!(w, "<" | "<=" | ">" | ">=" | "=");
    match op {
        RawOp::Int { signed, what } => {
            let raw = Rep::Raw { signed };
            let second = if matches!(what, "-shl" | "-shr") { Rep::Value } else { raw };
            let result = if compare(what) || what == "->int" { Rep::Value } else { raw };
            (raw, second, result)
        }
        // `int->f64` takes an int; `f64->int` gives one.
        RawOp::F64 { what: "from-int" } => (Rep::Value, Rep::Value, Rep::F64),
        RawOp::F64 { what } => (Rep::F64, Rep::F64, if compare(what) || what == "->int" { Rep::Value } else { Rep::F64 }),
    }
}

/// A conversion before an instruction: register `r`, raw as `rep` says,
/// boxed; or a value unboxed to `rep`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(super) enum Convert {
    Box { r: usize, rep: Rep },
    Unbox { r: usize, rep: Rep },
    /// In a fixnum version: register `r` tested for a fixnum, the general
    /// version taking over at this instruction if it is not.
    Check { r: usize },
}

/// How a register's value is used from a point on: not at all, only as a
/// raw `f64` (an operand of an `f64` operation `raw_op` does), or otherwise.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) enum Demand {
    None,
    F64,
    Other,
}

type Demands = [Demand; 9];

/// What instruction `op` asks of the registers before it, given what is
/// asked of them after (`after`): backward, as liveness is, each use joined
/// in and each definition clearing its register. Moves pass the demand on;
/// an operand of an `f64` operation asks for a raw `f64`; anything else,
/// conservatively, for a value. Only a genuine `f64` operand asks for one,
/// so that a flat array's element read raw is an `f64`'s by the program's
/// types.
fn demand_step(op: &str, o: &dyn Fn(usize) -> Value, prim: &dyn Fn(usize) -> &'static str, after: &Demands) -> Demands {
    let k = |j: usize| o(j).as_fixnum() as usize;
    let mut d = *after;
    let def = |d: &mut Demands, r: usize| d[r] = Demand::None;
    let use_ = |d: &mut Demands, r: usize, how: Demand| d[r] = d[r].max(how);
    let mv = |d: &mut Demands, from: usize, to: usize| {
        let how = d[to];
        d[to] = Demand::None;
        if from != 0 || to != 0 {
            d[from] = d[from].max(how);
        }
    };
    let regs = |n: usize| 1..=n.min(8);
    match op {
        "args" => regs(k(0)).for_each(|r| def(&mut d, r)),
        "vargs" => regs(8).for_each(|r| def(&mut d, r)),
        "const" | "global" | "lexical" | "stack" => def(&mut d, 0),
        "load" => def(&mut d, k(0)),
        "reg" if k(0) == 0 => def(&mut d, 0),
        "reg" => mv(&mut d, k(0), 0),
        "setreg" => mv(&mut d, 0, k(0)),
        "movereg" if k(0) == 0 => def(&mut d, k(1)),
        "movereg" => mv(&mut d, k(0), k(1)),
        "store" => use_(&mut d, k(0), Demand::Other),
        "setstk" | "setglbl" | "return" | "branchf" | "brancht" => use_(&mut d, 0, Demand::Other),
        "op1" | "op2imm" | "field" | "op2" | "setfield" => {
            def(&mut d, 0);
            use_(&mut d, 0, Demand::Other);
            if matches!(op, "op2" | "setfield") {
                use_(&mut d, k(1), Demand::Other);
            }
        }
        "prim1" | "prim2" | "prim2imm" => {
            let (x, y) = match raw_op(prim(k(0))) {
                Some(op @ RawOp::F64 { .. }) => {
                    let (x, y, _) = raw_shape(op);
                    let how = |r: Rep| if r == Rep::F64 { Demand::F64 } else { Demand::Other };
                    (how(x), how(y))
                }
                _ => (Demand::Other, Demand::Other),
            };
            def(&mut d, 0);
            use_(&mut d, 0, x);
            if op == "prim2" {
                use_(&mut d, k(1), y);
            }
        }
        "prim" | "lambda" | "cellular" | "invoke" | "tailinvoke" | "invokeself" => {
            let n = if matches!(op, "prim" | "lambda" | "cellular") { k(1) } else { k(0) };
            d = [Demand::None; 9];
            if matches!(op, "invoke" | "tailinvoke") {
                use_(&mut d, 0, Demand::Other);
            }
            regs(n).for_each(|r| use_(&mut d, r, Demand::Other));
        }
        "branch" | "global-guard" | "value-guard" | "save" | "pop" => {}
        _ => d = [Demand::Other; 9],
    }
    d
}

/// Whether instruction `op` reads a flat array's element (`flatarray-ref`).
fn is_flat_ref(op: &str, o: &dyn Fn(usize) -> Value, prim: &dyn Fn(usize) -> &'static str) -> bool {
    matches!(op, "prim2" | "prim2imm") && prim(o(0).as_fixnum() as usize) == "%fx26-flatarray-ref"
}

/// Instruction `op`, operands `o`, on `reps`: the conversions it needs
/// first, and `reps` after it. `prim` names a primitive by number.
/// `raw_ref`: whether a `flatarray-ref` here gives its element raw, an
/// `f64`'s bits, since only `f64` operations use it (`demand_step`).
/// `fast`: in a procedure's fixnum version.
pub(super) fn step(op: &str, o: &dyn Fn(usize) -> Value, prim: &dyn Fn(usize) -> &'static str, raw_ref: bool, fast: bool, reps: &mut Reps) -> Vec<Convert> {
    let mut first = Vec::new();
    let k = |j: usize| o(j).as_fixnum() as usize;
    let mut need = |reps: &mut Reps, r: usize, want: Rep| {
        match (reps[r], want) {
            // A known fixnum is a value already, and stays known.
            (Rep::Fix, Rep::Value) => return,
            (rep, Rep::Value) if rep.raw() => first.push(Convert::Box { r, rep }),
            (Rep::Value | Rep::Fix, rep) if rep.raw() => first.push(Convert::Unbox { r, rep }),
            (Rep::Value, Rep::Fix) => first.push(Convert::Check { r }),
            (rep, Rep::Fix) if rep.raw() => first.extend([Convert::Box { r, rep }, Convert::Check { r }]),
            _ => {}
        }
        if reps[r] != Rep::Undefined {
            reps[r] = want;
        }
    };
    let regs = |n: usize| 1..=n.min(8);
    match op {
        "args" => regs(k(0)).for_each(|r| reps[r] = Rep::Value),
        "vargs" => regs(8).for_each(|r| reps[r] = Rep::Value),
        "const" if fast && o(0).is_fixnum() => reps[0] = Rep::Fix,
        "const" | "global" | "lexical" | "stack" => reps[0] = Rep::Value,
        "reg" => reps[0] = if k(0) == 0 { Rep::Value } else { reps[k(0)] },
        "setreg" => reps[k(0)] = reps[0],
        "movereg" => reps[k(1)] = if k(0) == 0 { Rep::Value } else { reps[k(0)] },
        "load" => reps[k(0)] = Rep::Value,
        "store" => need(reps, k(0), Rep::Value),
        // In a fixnum version, `int`'s operations: operands known (tested
        // first where they are not), a sum or difference one too.
        "op2" | "op2imm" if fast && int_routine(k(0)) => {
            need(reps, 0, Rep::Fix);
            if op == "op2" {
                need(reps, k(1), Rep::Fix);
            }
            reps[0] = if matches!(ROUTINES[k(0)].0, "int-add" | "int-sub") { Rep::Fix } else { Rep::Value };
        }
        "op1" | "op2imm" | "field" => {
            need(reps, 0, Rep::Value);
            reps[0] = Rep::Value;
        }
        "op2" | "setfield" => {
            need(reps, 0, Rep::Value);
            need(reps, k(1), Rep::Value);
            reps[0] = Rep::Value;
        }
        "setstk" | "setglbl" | "return" | "branchf" | "brancht" => need(reps, 0, Rep::Value),
        "prim1" | "prim2" | "prim2imm" => {
            let (x, y, out) = match raw_op(prim(k(0))) {
                Some(op) => raw_shape(op),
                None => (Rep::Value, Rep::Value, Rep::Value),
            };
            need(reps, 0, x);
            if op == "prim2" {
                need(reps, k(1), y);
            }
            reps[0] = if raw_ref && is_flat_ref(op, o, prim) { Rep::F64 } else { out };
        }
        // Calls and call-outs: their operands values; the registers then
        // undefined, `RESULT` the value.
        "prim" | "lambda" | "cellular" | "invoke" | "tailinvoke" | "invokeself" => {
            let n = if matches!(op, "prim" | "lambda" | "cellular") { k(1) } else { k(0) };
            if matches!(op, "invoke" | "tailinvoke") {
                need(reps, 0, Rep::Value);
            }
            // `flatarray-set!` takes a raw `f64` to store as it is.
            let set = op == "prim" && prim(k(0)) == "%fx26-flatarray-set!";
            let keep = set && reps[3] == Rep::F64;
            regs(n).filter(|&r| !(keep && r == 3)).for_each(|r| need(reps, r, Rep::Value));
            *reps = [Rep::Undefined; 9];
            reps[0] = Rep::Value;
        }
        "branch" | "global-guard" | "value-guard" | "save" | "pop" => {}
        _ => {
            // Any other: every register a value, to be safe.
            (0..9).for_each(|r| need(reps, r, Rep::Value));
        }
    }
    first
}

/// Each instruction's registers where it starts (by instruction, in order),
/// and where it ends, over the procedure's cells, from the fixpoint of
/// `step` and `join`. `starts` are where the instructions start.
/// Whether cellular routine `n` is one of `int`'s that a fixnum version does
/// without testing its operands.
pub(super) fn int_routine(n: usize) -> bool {
    matches!(ROUTINES.get(n).map(|r| r.0), Some("int-add" | "int-sub" | "int-less" | "int-eq"))
}

pub(super) fn reps_of(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str, fast: bool) -> (Vec<Reps>, Vec<Reps>) {
    let raw_refs = raw_refs(cells, starts, prim);
    let ns = starts.len();
    let at: std::collections::HashMap<usize, usize> = starts.iter().enumerate().map(|(si, &i)| (i, si)).collect();
    let succ = |si: usize| -> Vec<usize> {
        let i = starts[si];
        let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
        let to = || at.get(&((i as i64 + 1 + n as i64 + cells[i + n].as_fixnum()) as usize)).copied();
        let next = (si + 1 < ns).then_some(si + 1);
        match op {
            "return" | "tailinvoke" => vec![],
            "branch" => to().into_iter().collect(),
            "branchf" | "brancht" | "global-guard" | "value-guard" => next.into_iter().chain(to()).collect(),
            _ => next.into_iter().collect(),
        }
    };
    let mut ins: Vec<Option<Reps>> = vec![None; ns];
    let mut outs = vec![[Rep::Undefined; 9]; ns];
    if ns > 0 {
        ins[0] = Some([Rep::Undefined; 9]);
    }
    loop {
        let mut changed = false;
        for si in 0..ns {
            let Some(mut reps) = ins[si] else { continue };
            let i = starts[si];
            let o = |j: usize| cells[i + 1 + j];
            step(OPS[cells[i].as_fixnum() as usize].0, &o, prim, raw_refs[si], fast, &mut reps);
            outs[si] = reps;
            for t in succ(si) {
                let new = match &ins[t] {
                    Some(old) => join(old, &reps),
                    None => reps,
                };
                if ins[t] != Some(new) {
                    ins[t] = Some(new);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    (ins.into_iter().map(|r| r.unwrap_or([Rep::Undefined; 9])).collect(), outs)
}

/// Successors of each instruction, by index into `starts`.
fn successors(cells: &[Value], starts: &[usize]) -> Vec<Vec<usize>> {
    let ns = starts.len();
    let at: std::collections::HashMap<usize, usize> = starts.iter().enumerate().map(|(si, &i)| (i, si)).collect();
    (0..ns)
        .map(|si| {
            let i = starts[si];
            let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
            let to = || at.get(&((i as i64 + 1 + n as i64 + cells[i + n].as_fixnum()) as usize)).copied();
            let next = (si + 1 < ns).then_some(si + 1);
            match op {
                "return" | "tailinvoke" => vec![],
                "branch" => to().into_iter().collect(),
                "branchf" | "brancht" | "global-guard" | "value-guard" => next.into_iter().chain(to()).collect(),
                _ => next.into_iter().collect(),
            }
        })
        .collect()
}

/// Which instructions are a `flatarray-ref` whose element only `f64`
/// operations use: the backward fixpoint of `demand_step`, over the ways
/// out of each instruction.
pub(super) fn raw_refs(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str) -> Vec<bool> {
    let (before, succ) = demands(cells, starts, prim);
    let ns = starts.len();
    (0..ns)
        .map(|si| {
            let i = starts[si];
            let o = |j: usize| cells[i + 1 + j];
            let after = succ[si].iter().fold(Demand::None, |m, &t| m.max(before[t][0]));
            is_flat_ref(OPS[cells[i].as_fixnum() as usize].0, &o, prim) && after == Demand::F64
        })
        .collect()
}

/// Which registers each instruction's value is used from (live, as it
/// starts), from `demands`.
pub(super) fn live_in(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str) -> Vec<[bool; 9]> {
    demands(cells, starts, prim).0.iter().map(|d| std::array::from_fn(|r| d[r] != Demand::None)).collect()
}

/// What each instruction asks of the registers as it starts (the backward
/// fixpoint of `demand_step`), and each instruction's successors.
fn demands(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str) -> (Vec<Demands>, Vec<Vec<usize>>) {
    let ns = starts.len();
    let succ = successors(cells, starts);
    let mut before = vec![[Demand::None; 9]; ns];
    loop {
        let mut changed = false;
        for si in (0..ns).rev() {
            let mut after = [Demand::None; 9];
            for &t in &succ[si] {
                for r in 0..9 {
                    after[r] = after[r].max(before[t][r]);
                }
            }
            let i = starts[si];
            let o = |j: usize| cells[i + 1 + j];
            let d = demand_step(OPS[cells[i].as_fixnum() as usize].0, &o, prim, &after);
            if d != before[si] {
                before[si] = d;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    (before, succ)
}
