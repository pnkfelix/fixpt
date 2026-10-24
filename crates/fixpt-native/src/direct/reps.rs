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
//! - a frame slot that only `f64` operations read (`raw_slots`) holds an
//!   `f64` raw: what is stored there is unboxed first, and what is read
//!   from it is raw (`TODO.md` §91). The frame keeps such slots after its
//!   values, as its bloblet's suffix, which no collection traces;
//! - anything else that reads a register reads it as a value: a raw one is
//!   boxed first, in its register. So nothing raw is stored in a frame's
//!   values, passed, returned or kept in the heap's values, and a
//!   collection never sees one.
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
/// raw `f64` (an operand of an `f64` operation `raw_op` does), otherwise,
/// or both: as an `f64` somewhere, so an `f64` by the program's types, and
/// otherwise too (as a loop's `f64` total is, returned at its end).
///
/// `Any`: passed to a call, which takes an `f64` raw or as a value: no
/// evidence of an `f64`, and no use against one.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(super) enum Demand {
    None,
    F64,
    Other,
    Both,
    Any,
}

impl Demand {
    /// Both ways' uses.
    fn join(self, other: Demand) -> Demand {
        match (self, other) {
            (Demand::None, x) | (x, Demand::None) => x,
            (Demand::Any, x) | (x, Demand::Any) => x,
            (x, y) if x == y => x,
            (Demand::Other, Demand::Other) => Demand::Other,
            _ => Demand::Both,
        }
    }
}

type Demands = [Demand; 9];

/// What instruction `op` asks of the registers before it, given what is
/// asked of them after (`after`): backward, as liveness is, each use joined
/// in and each definition clearing its register. Moves pass the demand on;
/// an operand of an `f64` operation asks for a raw `f64`; anything else,
/// conservatively, for a value. Only a genuine `f64` operand asks for one,
/// so that a flat array's element read raw is an `f64`'s by the program's
/// types.
fn demand_step(op: &str, o: &dyn Fn(usize) -> Value, prim: &dyn Fn(usize) -> &'static str, after: &Demands, raw: &[bool]) -> Demands {
    let k = |j: usize| o(j).as_fixnum() as usize;
    let mut d = *after;
    let def = |d: &mut Demands, r: usize| d[r] = Demand::None;
    let use_ = |d: &mut Demands, r: usize, how: Demand| d[r] = d[r].join(how);
    let mv = |d: &mut Demands, from: usize, to: usize| {
        let how = d[to];
        d[to] = Demand::None;
        if from != 0 || to != 0 {
            d[from] = d[from].join(how);
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
        // Into a raw slot, an `f64`.
        "store" => use_(&mut d, k(0), if raw_slot(raw, k(1)) { Demand::F64 } else { Demand::Other }),
        "setstk" => use_(&mut d, 0, if raw_slot(raw, k(0)) { Demand::F64 } else { Demand::Other }),
        "setglbl" | "return" | "branchf" | "brancht" => use_(&mut d, 0, Demand::Other),
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
        // Of three: `RESULT`, a constant and `REGk`; an `f64` to write at a
        // blobref (`blobref-set!`) taken raw.
        "prim3imm" => {
            def(&mut d, 0);
            use_(&mut d, 0, Demand::Other);
            use_(&mut d, k(2), if is_f64_set(o, prim) { Demand::F64 } else { Demand::Other });
        }
        "prim" | "lambda" | "cellular" | "invoke" | "tailinvoke" | "invokeself" => {
            let n = if matches!(op, "prim" | "lambda" | "cellular") { k(1) } else { k(0) };
            d = [Demand::None; 9];
            if matches!(op, "invoke" | "tailinvoke") {
                use_(&mut d, 0, Demand::Other);
            }
            let how = if matches!(op, "invoke" | "tailinvoke" | "invokeself") { Demand::Any } else { Demand::Other };
            regs(n).for_each(|r| use_(&mut d, r, how));
        }
        "branch" | "global-guard" | "save" | "pop" => {}
        _ => d = [Demand::Other; 9],
    }
    d
}

/// Whether instruction `op` reads a flat array's element (`flatarray-ref`),
/// or an `f64` at a blobref (`blobref-get`).
fn is_flat_ref(op: &str, o: &dyn Fn(usize) -> Value, prim: &dyn Fn(usize) -> &'static str) -> bool {
    let name = || prim(o(0).as_fixnum() as usize);
    (matches!(op, "prim2" | "prim2imm") && name() == "%fx26-flatarray-ref")
        || (op == "prim2imm" && name() == "%fx26-suffix-ref-get" && o(1) == Value::fixnum(fixpt_heap::layout::FLAT_F64))
}

/// Whether `prim3imm`, operands `o`, writes an `f64` at a blobref
/// (`blobref-set!`), which it may take raw.
pub(super) fn is_f64_set(o: &dyn Fn(usize) -> Value, prim: &dyn Fn(usize) -> &'static str) -> bool {
    prim(o(0).as_fixnum() as usize) == "%fx26-suffix-ref-set!" && o(1) == Value::fixnum(fixpt_heap::layout::FLAT_F64)
}

/// Instruction `op`, operands `o`, on `reps`: the conversions it needs
/// first, and `reps` after it. `prim` names a primitive by number.
/// `raw_ref`: whether a `flatarray-ref` (or `f64` `blobref-get`) here gives its element raw, an
/// `f64`'s bits, since only `f64` operations use it (`demand_step`).
/// `fast`: in a procedure's fixnum version.
pub(super) fn step(op: &str, o: &dyn Fn(usize) -> Value, prim: &dyn Fn(usize) -> &'static str, raw_ref: bool, fast: bool, raw: &[bool], calls: Calls, reps: &mut Reps) -> Vec<Convert> {
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
        // The parameters the procedure takes raw (`raw_params`), raw: a
        // caller that knows it passes them so, any other's unboxed at the
        // entry (`direct.rs`).
        "args" => regs(k(0)).for_each(|r| reps[r] = if raw_param(calls.own, r) { Rep::F64 } else { Rep::Value }),
        "vargs" => regs(8).for_each(|r| reps[r] = Rep::Value),
        "const" if fast && o(0).is_fixnum() => reps[0] = Rep::Fix,
        "stack" => reps[0] = if raw_slot(raw, k(0)) { Rep::F64 } else { Rep::Value },
        "const" | "global" | "lexical" => reps[0] = Rep::Value,
        "reg" => reps[0] = if k(0) == 0 { Rep::Value } else { reps[k(0)] },
        "setreg" => reps[k(0)] = reps[0],
        "movereg" => reps[k(1)] = if k(0) == 0 { Rep::Value } else { reps[k(0)] },
        "load" => reps[k(0)] = if raw_slot(raw, k(1)) { Rep::F64 } else { Rep::Value },
        "store" => need(reps, k(0), if raw_slot(raw, k(1)) { Rep::F64 } else { Rep::Value }),
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
        "setstk" => need(reps, 0, if raw_slot(raw, k(0)) { Rep::F64 } else { Rep::Value }),
        // An `f64` returned raw, where the caller takes it so (`direct.rs`,
        // `raw_return`); boxed there where it does not.
        "return" if reps[0] == Rep::F64 => {}
        "setglbl" | "return" | "branchf" | "brancht" => need(reps, 0, Rep::Value),
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
        "prim3imm" => {
            need(reps, 0, Rep::Value);
            if !(is_f64_set(o, prim) && reps[k(2)] == Rep::F64) {
                need(reps, k(2), Rep::Value);
            }
            reps[0] = Rep::Value;
        }
        // Calls and call-outs: their operands values; the registers then
        // undefined, `RESULT` the value.
        "prim" | "lambda" | "cellular" | "invoke" | "tailinvoke" | "invokeself" => {
            let n = if matches!(op, "prim" | "lambda" | "cellular") { k(1) } else { k(0) };
            if matches!(op, "invoke" | "tailinvoke") {
                need(reps, 0, Rep::Value);
            }
            // `flatarray-set!` takes a raw `f64` to store as it is; a call of
            // a procedure known here (this one, or one bound as compiled),
            // its arguments as it takes them.
            let set = op == "prim" && prim(k(0)) == "%fx26-flatarray-set!";
            let keep = set && reps[3] == Rep::F64;
            let callee = match op {
                "invokeself" => calls.own,
                "invoke" | "tailinvoke" => calls.callee,
                _ => 0,
            };
            for r in regs(n).filter(|&r| !(keep && r == 3)) {
                need(reps, r, if raw_param(callee, r) { Rep::F64 } else { Rep::Value });
            }
            *reps = [Rep::Undefined; 9];
            // A call whose value only `f64` operations use takes it raw.
            reps[0] = if raw_ref && matches!(op, "invoke" | "invokeself") { Rep::F64 } else { Rep::Value };
        }
        "branch" | "global-guard" | "save" | "pop" => {}
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

pub(super) fn reps_of(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str, fast: bool, raw: &[bool], raw_refs: &[bool], own: u8, callees: &[u8]) -> (Vec<Reps>, Vec<Reps>) {
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
            "branchf" | "brancht" | "global-guard" => next.into_iter().chain(to()).collect(),
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
            step(OPS[cells[i].as_fixnum() as usize].0, &o, prim, raw_refs[si], fast, raw, Calls { own, callee: callees[si] }, &mut reps);
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
                "branchf" | "brancht" | "global-guard" => next.into_iter().chain(to()).collect(),
                _ => next.into_iter().collect(),
            }
        })
        .collect()
}

/// Which instructions are a `flatarray-ref` (or `f64` `blobref-get`) whose
/// element only `f64` operations use, or a call (not in tail position)
/// whose value only they use: the backward fixpoint of `demand_step`, over
/// the ways out of each instruction.
pub(super) fn raw_refs(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str, raw: &[bool]) -> Vec<bool> {
    let (before, succ) = demands(cells, starts, prim, raw);
    refs_of(cells, starts, prim, &before, &succ)
}

/// `raw_refs` and `live_in`, from one `demands`.
pub(super) fn refs_and_live(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str, raw: &[bool]) -> (Vec<bool>, Vec<[bool; 9]>) {
    let (before, succ) = demands(cells, starts, prim, raw);
    let refs = refs_of(cells, starts, prim, &before, &succ);
    (refs, before.iter().map(|d| std::array::from_fn(|r| d[r] != Demand::None)).collect())
}

/// `raw_refs`, from the demands as each instruction starts and the ways
/// out of each.
fn refs_of(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str, before: &[Demands], succ: &[Vec<usize>]) -> Vec<bool> {
    let ns = starts.len();
    (0..ns)
        .map(|si| {
            let i = starts[si];
            let o = |j: usize| cells[i + 1 + j];
            let after = succ[si].iter().fold(Demand::None, |m, &t| m.join(before[t][0]));
            let op = OPS[cells[i].as_fixnum() as usize].0;
            (is_flat_ref(op, &o, prim) || matches!(op, "invoke" | "invokeself")) && after == Demand::F64
        })
        .collect()
}

/// Which parameters raw: the procedure's own (`own`, for `args` and
/// `invokeself`), and, for an `invoke` or `tailinvoke` of a procedure known
/// where it is compiled, that one's (`callee`); bit 0 for REG1.
#[derive(Copy, Clone, Default)]
pub(super) struct Calls {
    pub own: u8,
    pub callee: u8,
}

/// Whether parameter register `r` (REG1…REG8) is one `params` says is
/// taken raw.
pub(super) fn raw_param(params: u8, r: usize) -> bool {
    (1..=8).contains(&r) && params & 1 << (r - 1) != 0
}

/// The parameters (REG1…REG8, bit 0 for REG1) a procedure takes raw: those
/// only `f64` operations use (an operand, or a raw slot's store), so `f64`s
/// by the program's types; a call's operand, which takes either, counting
/// for neither (`Demand::Any`). None of a variadic procedure's, or one whose
/// first instruction is not `args`.
pub(super) fn raw_params(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str, raw: &[bool]) -> u8 {
    if starts.first().is_none_or(|&i| OPS[cells[i].as_fixnum() as usize].0 != "args") {
        return 0;
    }
    let (before, succ) = demands(cells, starts, prim, raw);
    let n = cells[starts[0] + 1].as_fixnum() as usize;
    let f64s = |r: usize| !succ[0].is_empty() && succ[0].iter().all(|&t| before[t][r] == Demand::F64);
    (1..=n.min(8)).filter(|&r| f64s(r)).fold(0, |m, r| m | 1 << (r - 1))
}

/// Which registers each instruction's value is used from (live, as it
/// starts), from `demands`.
pub(super) fn live_in(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str, raw: &[bool]) -> Vec<[bool; 9]> {
    demands(cells, starts, prim, raw).0.iter().map(|d| std::array::from_fn(|r| d[r] != Demand::None)).collect()
}

/// What each instruction asks of the registers as it starts (the backward
/// fixpoint of `demand_step`), and each instruction's successors.
fn demands(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str, raw: &[bool]) -> (Vec<Demands>, Vec<Vec<usize>>) {
    let ns = starts.len();
    let succ = successors(cells, starts);
    let mut before = vec![[Demand::None; 9]; ns];
    loop {
        let mut changed = false;
        for si in (0..ns).rev() {
            let mut after = [Demand::None; 9];
            for &t in &succ[si] {
                for r in 0..9 {
                    after[r] = after[r].join(before[t][r]);
                }
            }
            let i = starts[si];
            let o = |j: usize| cells[i + 1 + j];
            let d = demand_step(OPS[cells[i].as_fixnum() as usize].0, &o, prim, &after, raw);
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

/// Whether frame slot `n` holds a raw `f64` (`raw_slots`).
fn raw_slot(raw: &[bool], n: usize) -> bool {
    raw.get(n).copied().unwrap_or(false)
}

/// What `webs` finds: for each instruction that touches a frame slot, the
/// slot and its web (an instruction's index standing for the web); and of
/// each web, whether it is an `f64`'s and whether it is read.
struct Webs {
    web: Vec<Option<(usize, usize)>>,
    f64_web: Vec<bool>,
    used_web: Vec<bool>,
}

/// Which of the procedure's `slots` frame slots hold a raw `f64`
/// (`TODO.md` §91). Register code may use a slot for one variable, then
/// another, so a slot is taken apart into *webs*: its writes (`setstk`,
/// `store`) and reads (`stack`, `load`) joined where a write reaches a
/// read, each web one variable's. A web is an `f64`'s where the program's
/// types say so: one of its reads is used by an `f64` operation, or one of
/// its writes stores what an `f64` operation made (each as if no slot were
/// raw, so that nothing here rests on itself). A slot is raw if every web
/// of it is an `f64`'s, or never read: what is stored there is unboxed,
/// and a read used otherwise (a loop's `f64` total, returned at its end)
/// boxes it there. A slot that holds an `f64` and something else in turn
/// is first split (`split_slots`).
pub(super) fn raw_slots(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str, slots: usize) -> Vec<bool> {
    raw_of(&webs(cells, starts, prim, slots), slots)
}

/// `raw_slots`, from the webs.
fn raw_of(w: &Webs, slots: usize) -> Vec<bool> {
    let mut raw = vec![true; slots];
    for &(slot, web) in w.web.iter().flatten() {
        if slot < slots && w.used_web[web] && !w.f64_web[web] {
            raw[slot] = false;
        }
    }
    raw
}

/// `cells`, a procedure's register code, with each frame slot that holds
/// an `f64` and, in turn, something else (a web of each, `webs`) split in
/// two: its `f64` webs moved to a slot of their own, past the frame's
/// others, which `raw_slots` then keeps raw; the frame (`save`, `pop`) that
/// much larger. Register code reuses a slot for variables whose lives do
/// not meet, of any type, so without this one `int` in a slot boxes every
/// `f64` stored there (`nbody`'s `pairs`: the inlined `put`'s `v`, and the
/// loop's next `j`). The same cells if nothing is split, or the frame
/// would pass 64 slots.
pub(super) fn split_slots(cells: Vec<Value>, prim: &dyn Fn(usize) -> &'static str) -> Vec<Value> {
    split_slots_raw(cells, prim).0
}

/// `split_slots`, and where it split nothing but found the webs, the
/// frame's size and its `raw_slots`, from the same webs.
pub(super) fn split_slots_raw(cells: Vec<Value>, prim: &dyn Fn(usize) -> &'static str) -> (Vec<Value>, Option<(usize, Vec<bool>)>) {
    let (mut starts, mut frames, mut i) = (Vec::new(), Vec::new(), 0);
    while i < cells.len() {
        starts.push(i);
        let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
        if matches!(op, "save" | "pop") {
            frames.push(cells[i + 1].as_fixnum() as usize);
        }
        i += 1 + n;
    }
    let Some(&m) = frames.first() else { return (cells, None) };
    if frames.iter().any(|&f| f != m) {
        return (cells, None);
    }
    let w = webs(&cells, &starts, prim, m);
    let mut f64s = vec![false; m];
    let mut others = vec![false; m];
    for &(slot, web) in w.web.iter().flatten() {
        if slot < m && w.f64_web[web] {
            f64s[slot] = true;
        } else if slot < m && w.used_web[web] {
            others[slot] = true;
        }
    }
    // Each mixed slot's new place.
    let mut moved = vec![None; m];
    let mut next = m;
    for slot in (0..m).filter(|&s| f64s[s] && others[s]) {
        moved[slot] = Some(next);
        next += 1;
    }
    if next == m || next > 64 {
        return (cells, Some((m, raw_of(&w, m))));
    }
    let mut out = cells;
    for (si, &i) in starts.iter().enumerate() {
        let op = OPS[out[i].as_fixnum() as usize].0;
        match (op, w.web[si]) {
            ("save" | "pop", _) => out[i + 1] = Value::fixnum(next as i64),
            (_, Some((slot, web))) if w.f64_web[web] => {
                if let Some(to) = moved[slot] {
                    // The slot is the first operand of `stack` and `setstk`,
                    // the second of `load` and `store`.
                    let k = if matches!(op, "load" | "store") { i + 2 } else { i + 1 };
                    out[k] = Value::fixnum(to as i64);
                }
            }
            _ => {}
        }
    }
    (out, None)
}

/// The webs of the procedure's `slots` frame slots (`raw_slots`).
fn webs(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str, slots: usize) -> Webs {
    let ns = starts.len();
    let none = vec![false; slots];
    let (before, succ) = demands(cells, starts, prim, &none);
    let refs = refs_of(cells, starts, prim, &before, &succ);
    let (ins, _) = reps_of(cells, starts, prim, false, &none, &refs, 0, &vec![0; starts.len()]);
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); ns];
    for (si, ts) in succ.iter().enumerate() {
        for &t in ts {
            preds[t].push(si);
        }
    }
    // Each instruction's slot access: (slot, read?, register).
    let access = |si: usize| -> Option<(usize, bool, usize)> {
        let i = starts[si];
        let o = |j: usize| cells[i + 1 + j].as_fixnum() as usize;
        match OPS[cells[i].as_fixnum() as usize].0 {
            "stack" => Some((o(0), true, 0)),
            "load" => Some((o(1), true, o(0))),
            "setstk" => Some((o(0), false, 0)),
            "store" => Some((o(1), false, o(0))),
            _ => None,
        }
    };
    // Webs: a union-find over the instructions that touch a slot, each
    // access's parent the access that stands for its web.
    let mut parent: Vec<usize> = (0..ns).collect();
    fn find(parent: &mut [usize], x: usize) -> usize {
        let mut r = x;
        while parent[r] != r {
            r = parent[r];
        }
        let mut y = x;
        while parent[y] != r {
            let next = parent[y];
            parent[y] = r;
            y = next;
        }
        r
    }
    // A slot at a time, not a search back from each read (`TODO.md` §114):
    // where the slot is live (a read of it comes before any write) and
    // some write of it has been, every write that reaches there reaches a
    // read, so one web holds them. A frame may have hundreds of slots, and
    // a module's body thousands of instructions and no branch, so this is
    // done by basic block: each slot's work its own reads and writes, and
    // the blocks where it is live. A block's chain of instructions, each
    // but the first its one predecessor's one successor (and a loop of
    // those, unreachable, cut).
    let leader = |t: usize| t == 0 || preds[t].len() != 1 || succ[preds[t][0]].len() != 1;
    let (mut block, mut order, mut lasts) = (vec![usize::MAX; ns], Vec::with_capacity(ns), Vec::new());
    for cut in [false, true] {
        for l in 0..ns {
            if block[l] != usize::MAX || !(cut || leader(l)) {
                continue;
            }
            let mut t = l;
            loop {
                block[t] = lasts.len();
                order.push(t);
                match succ[t][..] {
                    [n] if !leader(n) && block[n] == usize::MAX => t = n,
                    _ => break,
                }
            }
            lasts.push(t);
        }
    }
    let nb = lasts.len();
    let mut bpreds: Vec<Vec<usize>> = vec![Vec::new(); nb];
    for (b, &l) in lasts.iter().enumerate() {
        for &t in &succ[l] {
            bpreds[block[t]].push(b);
        }
    }
    // Each slot's reads and writes, block by block, each block's in order.
    let mut by_slot: Vec<Vec<usize>> = Vec::new();
    for &si in &order {
        if let Some((slot, _, _)) = access(si) {
            if by_slot.len() <= slot {
                by_slot.resize(slot + 1, Vec::new());
            }
            by_slot[slot].push(si);
        }
    }
    // By block, for which slot it was last touched (and then whether its
    // first access reads, its last write), live and reached. The union-find
    // has a node for each instruction and one for each block's start
    // (`ns + b`), and says for which slot each was set.
    let (mut touched, mut first_reads, mut last_write) = (vec![usize::MAX; nb], vec![false; nb], vec![usize::MAX; nb]);
    let (mut live, mut reached) = (vec![usize::MAX; nb], vec![usize::MAX; nb]);
    let (mut own, mut own_of) = (vec![0; ns + nb], vec![usize::MAX; ns + nb]);
    for (slot, touches) in by_slot.iter().enumerate() {
        let writes = |si: usize| matches!(access(si), Some((s, false, _)) if s == slot);
        let mut blocks = Vec::new();
        for &si in touches {
            let b = block[si];
            if touched[b] != slot {
                (touched[b], first_reads[b], last_write[b]) = (slot, !writes(si), usize::MAX);
                blocks.push(b);
            }
            if writes(si) {
                last_write[b] = si;
            }
        }
        // Live where a block reads the slot first, and back from there
        // through blocks that do not touch it.
        let mut work: Vec<usize> = blocks.iter().copied().filter(|&b| first_reads[b]).collect();
        for &b in &work {
            live[b] = slot;
        }
        let mut region = work.clone();
        while let Some(c) = work.pop() {
            for &p in &bpreds[c] {
                if live[p] != slot && touched[p] != slot {
                    live[p] = slot;
                    region.push(p);
                    work.push(p);
                }
            }
        }
        // Reached, where live: on from each block that writes it.
        let mut work: Vec<usize> = blocks.iter().copied().filter(|&b| last_write[b] != usize::MAX).collect();
        while let Some(p) = work.pop() {
            for &t in &succ[lasts[p]] {
                let c = block[t];
                if live[c] == slot && reached[c] != slot {
                    reached[c] = slot;
                    work.push(c);
                }
            }
        }
        // A web's root an access where it has one.
        let mut union = |x: usize, y: usize| {
            for z in [x, y] {
                if own_of[z] != slot {
                    (own_of[z], own[z]) = (slot, z);
                }
            }
            let (a, b) = (find(&mut own, x), find(&mut own, y));
            if a < ns {
                own[b] = a;
            } else {
                own[a] = b;
            }
        };
        // In a block, a read joined to the write before it, or to the
        // block's start; and each block's start where live and reached to
        // the end of each block before it, its last write or its start.
        let mut at = (usize::MAX, usize::MAX);
        for &si in touches {
            let b = block[si];
            if at.0 != b {
                at = (b, if reached[b] == slot { ns + b } else { usize::MAX });
            }
            if writes(si) {
                at.1 = si;
            } else if at.1 != usize::MAX {
                union(si, at.1);
            }
        }
        for &c in region.iter().filter(|&&c| reached[c] == slot) {
            for &p in &bpreds[c] {
                if touched[p] == slot && last_write[p] != usize::MAX {
                    union(ns + c, last_write[p]);
                } else if reached[p] == slot {
                    union(ns + c, ns + p);
                }
            }
        }
        for &si in touches {
            if own_of[si] != slot {
                (own_of[si], own[si]) = (slot, si);
            }
            parent[si] = find(&mut own, si);
        }
    }
    // What each web shows: an `f64`'s, and whether it is read (used).
    let mut f64_web = vec![false; ns];
    let mut used_web = vec![false; ns];
    for si in 0..ns {
        let Some((_, read, reg)) = access(si) else { continue };
        let w = find(&mut parent, si);
        if read {
            let after = succ[si].iter().fold(Demand::None, |m, &t| m.join(before[t][reg]));
            if matches!(after, Demand::F64 | Demand::Both) {
                f64_web[w] = true;
            }
            if after != Demand::None {
                used_web[w] = true;
            }
        } else if ins[si][reg] == Rep::F64 {
            f64_web[w] = true;
        }
    }
    let mut web = vec![None; ns];
    for (si, w) in web.iter_mut().enumerate() {
        if let Some((slot, _, _)) = access(si) {
            *w = Some((slot, find(&mut parent, si)));
        }
    }
    Webs { web, f64_web, used_web }
}


#[doc(hidden)]
pub mod oracle;

#[cfg(test)]
mod tests {
    use super::*;
    use fixpt_heap::layout::regcode::op;

    /// A slot that holds an `f64`, then an `int` (as `nbody`'s `pairs`
    /// reused one for an inlined `put`'s `v` and the loop's next `j`): its
    /// `f64` web moved to a slot of its own, kept raw; the `int`'s left, a
    /// value's; the frame one larger.
    #[test]
    fn a_slot_of_an_f64_and_an_int_is_split() {
        let prim = |p: usize| fixpt_runtime::PRIMITIVES.get(p).map_or("?", |d| d.name);
        let add = fixpt_runtime::PRIMITIVES.iter().position(|d| d.name == "%fx26-f64+").expect("f64+") as i64;
        let c = |op_name: &str, args: &[i64]| -> Vec<Value> {
            std::iter::once(Value::fixnum(op(op_name) as i64)).chain(args.iter().map(|&a| Value::fixnum(a))).collect()
        };
        let cells: Vec<Value> = [
            c("args", &[1]),
            c("save", &[1]),
            c("reg", &[1]),
            c("prim2", &[add, 1]),
            c("setstk", &[0]), // the `f64`
            c("stack", &[0]),
            c("prim2", &[add, 1]),
            c("setreg", &[1]),
            c("const", &[5]),
            c("setstk", &[0]), // the `int`
            c("stack", &[0]),
            c("pop", &[1]),
            c("return", &[]),
        ]
        .concat();
        let split = split_slots(cells.clone(), &prim);
        let mut starts = Vec::new();
        let mut i = 0;
        while i < split.len() {
            starts.push(i);
            i += 1 + OPS[split[i].as_fixnum() as usize].1;
        }
        let operand = |k: usize| split[starts[k] + 1].as_fixnum();
        assert_eq!((operand(1), operand(4), operand(5), operand(9), operand(10), operand(11)), (2, 1, 1, 0, 0, 2));
        assert_eq!(raw_slots(&split, &starts, &prim, 2), [false, true]);
        // Unsplit, the slot was a value's, and every `f64` stored there boxed.
        assert_eq!(raw_slots(&cells, &starts, &prim, 1), [false]);
    }
}
