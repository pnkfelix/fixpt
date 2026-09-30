//! Where native code keeps `i64` and `u64` values: raw, as the machine's 64
//! bits, in registers only (`RESULT`, REG1…REG8), and as the value they are
//! everywhere else (the exact integer: a fixnum, or a bignum past 60 bits).
//! Register code does not say which: it is the same for every machine, and
//! its registers hold values. This pass says, instruction by instruction,
//! forward over the procedure's register code:
//!
//! - an operation of `i64` or `u64` (`prim1`, `prim2`, `prim2imm` of such a
//!   primitive) takes its operands raw and gives its value raw, a
//!   comparison and `T->int` excepted;
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
}

/// `RESULT`, then REG1…REG8.
pub(super) type Reps = [Rep; 9];

/// Where two ways meet.
pub(super) fn join(a: &Reps, b: &Reps) -> Reps {
    std::array::from_fn(|r| match (a[r], b[r]) {
        (Rep::Undefined, x) | (x, Rep::Undefined) => x,
        (x @ Rep::Raw { .. }, _) | (_, x @ Rep::Raw { .. }) => x,
        _ => Rep::Value,
    })
}

/// The registers a way into `to` must unbox: a value there, raw at `to`.
pub(super) fn unboxes(from: &Reps, to: &Reps) -> Vec<usize> {
    (0..9).filter(|&r| from[r] == Rep::Value && matches!(to[r], Rep::Raw { .. })).collect()
}

/// A 64-bit integer operation, by its primitive's name (`%fx26-u64*`,
/// `%fx26-int->i64`): whether its type is signed, and what it does (the
/// name after the type, `*` or `-xor`; `from` for `int->T`).
pub(super) fn raw_op(name: &str) -> Option<(bool, &str)> {
    let rest = name.strip_prefix("%fx26-")?;
    let (t, op) = match rest.strip_prefix("int->") {
        Some(t) => (t, "from"),
        None => (rest.get(..3)?, &rest[3..]),
    };
    let signed = match t {
        "i64" => true,
        "u64" => false,
        _ => return None,
    };
    Some((signed, op))
}

/// What a 64-bit operation takes and gives: its first operand raw (all of
/// them, `int->T`'s int too, which unboxing wraps); its second raw but for a
/// shift's count; its value raw but for a comparison's and `T->int`'s.
fn raw_shape(signed: bool, op: &str) -> (Rep, Rep, Rep) {
    let raw = Rep::Raw { signed };
    let second = if matches!(op, "-shl" | "-shr") { Rep::Value } else { raw };
    let result = if matches!(op, "<" | "<=" | ">" | ">=" | "=" | "->int") { Rep::Value } else { raw };
    (raw, second, result)
}

/// A conversion before an instruction: register `r` boxed, or unboxed.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(super) enum Convert {
    Box { r: usize, signed: bool },
    Unbox { r: usize },
}

/// Instruction `op`, operands `o`, on `reps`: the conversions it needs
/// first, and `reps` after it. `prim` names a primitive by number.
pub(super) fn step(op: &str, o: &dyn Fn(usize) -> Value, prim: &dyn Fn(usize) -> &'static str, reps: &mut Reps) -> Vec<Convert> {
    let mut first = Vec::new();
    let k = |j: usize| o(j).as_fixnum() as usize;
    let mut need = |reps: &mut Reps, r: usize, want: Rep| {
        match (reps[r], want) {
            (Rep::Raw { signed }, Rep::Value) => first.push(Convert::Box { r, signed }),
            (Rep::Value, Rep::Raw { .. }) => first.push(Convert::Unbox { r }),
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
        "const" | "global" | "lexical" | "stack" => reps[0] = Rep::Value,
        "reg" => reps[0] = if k(0) == 0 { Rep::Value } else { reps[k(0)] },
        "setreg" => reps[k(0)] = reps[0],
        "movereg" => reps[k(1)] = if k(0) == 0 { Rep::Value } else { reps[k(0)] },
        "load" => reps[k(0)] = Rep::Value,
        "store" => need(reps, k(0), Rep::Value),
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
                Some((signed, what)) => raw_shape(signed, what),
                None => (Rep::Value, Rep::Value, Rep::Value),
            };
            need(reps, 0, x);
            if op == "prim2" {
                need(reps, k(1), y);
            }
            reps[0] = out;
        }
        // Calls and call-outs: their operands values; the registers then
        // undefined, `RESULT` the value.
        "prim" | "lambda" | "cellular" | "invoke" | "tailinvoke" | "invokeself" => {
            let n = if matches!(op, "prim" | "lambda" | "cellular") { k(1) } else { k(0) };
            if matches!(op, "invoke" | "tailinvoke") {
                need(reps, 0, Rep::Value);
            }
            regs(n).for_each(|r| need(reps, r, Rep::Value));
            *reps = [Rep::Undefined; 9];
            reps[0] = Rep::Value;
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
pub(super) fn reps_of(cells: &[Value], starts: &[usize], prim: &dyn Fn(usize) -> &'static str) -> (Vec<Reps>, Vec<Reps>) {
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
            step(OPS[cells[i].as_fixnum() as usize].0, &o, prim, &mut reps);
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
