//! Register code (PLAN.md 13h′) as machine code, on the machine stack code
//! (threaded words, interpreted or compiled) runs on, so that each may call
//! the other. The two differ in their machine model, not in being compiled:
//! stack code passes and keeps every value on the data stack, register code
//! in registers.
//!
//! `RESULT` is `x0`; `REG1`…`REG8` are `x1`…`x8`; `REG0` is `CLO`. While
//! register code runs, `CUR` is its register word, and `IP`, which it has no
//! use for as an ip, points at the word's last field, so that its constants
//! and global cells are one load away (`cell`). Whatever may collect is a
//! call-out, or a call, and everything live is in the frame by then (the
//! compiler sees to it): afterwards the machine's registers are loaded from
//! the state, `IP` made again, and `RESULT` taken from the data stack, where
//! a call-out, or a return, leaves a value. Those resume points are what the
//! word's resume table lists, so that a return, or a continuation captured
//! in a call-out, comes back to them.
//!
//! A call whose callee's word has compiled register code jumps to it with
//! the arguments in registers; any other pushes them as a stack frame. A
//! stack-code caller enters a word with register code through the word's
//! own entry, which moves the frame's arguments into registers.

use super::*;
use fixpt_heap::layout::regcode::{OPS, REGS};
use fixpt_heap::layout::threaded::{routine, WORD_TWIN};

const RESULT: Reg = 0;
const X12: Reg = 12;

/// `REGk`'s machine register.
fn reg(k: usize) -> Reg {
    if k == 0 { CLO } else { k as Reg }
}

impl Asm {
    /// `IP` := the address of the running register word's field `fields`,
    /// its last, from which field `f` is `8 × (fields − f)` bytes up.
    fn pool(&mut self, fields: usize) {
        self.e(mov(IP, CUR));
        self.sub_const(IP, IP, 4 + 8 * fields as u64);
    }
    /// `d := n − k`, for a constant `k` of any size (clobbers `X16`).
    fn sub_const(&mut self, d: Reg, n: Reg, k: u64) {
        if k < 4096 {
            self.e(sub_imm(d, n, k as u32));
        } else {
            self.es(&mov_imm64(X16, k));
            self.e(sub(d, n, X16));
        }
    }
    /// `dst` := field `f` of the running register word.
    fn cell(&mut self, dst: Reg, f: usize, fields: usize) {
        let off = 8 * (fields - f) as u64;
        if off < 32768 {
            self.e(ldr(dst, IP, off as u32));
        } else {
            self.es(&mov_imm64(X16, off));
            self.e(add(X16, IP, X16));
            self.e(ldr(dst, X16, 0));
        }
    }
    /// `dst` := field `f` of the bloblet whose `suffix + 4` is in `b`.
    fn field_of(&mut self, dst: Reg, b: Reg, f: usize) {
        let off = field_off(f);
        if off >= -256 {
            self.e(ldur(dst, b, off));
        } else {
            self.sub_const(X16, b, -off as u64);
            self.e(ldr(dst, X16, 0));
        }
    }
    /// Frame slot `n`: `8n` bytes below `FP`.
    fn slot(&mut self, r: Reg, n: usize, store: bool) {
        let off = 8 * n as i64;
        if off <= 256 {
            self.e(if store { stur(r, FP, -off) } else { ldur(r, FP, -off) });
        } else {
            self.sub_const(X16, FP, off as u64);
            self.e(if store { str(r, X16, 0) } else { ldr(r, X16, 0) });
        }
    }
    /// `IP` := the address of the running word's field `f`, as a threaded
    /// ip is, for what reads the word from where the ip is (`save`).
    fn ip_at(&mut self, f: usize) {
        self.e(mov(IP, CUR));
        self.sub_const(IP, IP, 4 + 8 * f as u64);
    }
    /// Push `REG1`…`REGn`, `REG1` deepest.
    fn push_regs(&mut self, n: usize) {
        for k in 1..=n {
            self.e(str_pre(reg(k), DSP, -8));
        }
    }
    /// Back from somewhere that may have collected: the value on the data
    /// stack into `RESULT`, and `IP` made again.
    fn resumed(&mut self, fields: usize) {
        self.e(ldr_post(RESULT, DSP, 8));
        self.pool(fields);
    }
    /// A call-out to routine `n` with the ip at field `f`: as
    /// [`callout`](Asm::callout), but on, whatever the routine, to the code
    /// after it, or, for control, to the resume point `f` names.
    fn r_callout(&mut self, n: u64, f: usize) {
        self.ip_at(f);
        self.save();
        self.e(mov(0, ST));
        self.e(movz(1, n as u32, 0));
        self.e(ldr(X16, ST, off(offset_of!(State, callout))));
        self.e(blr(X16));
        let exit = self.exit_common;
        self.cbnz(0, exit);
        self.load();
        if CONTROL_CALLOUTS.contains(&ROUTINES[n as usize].0) {
            self.enter_cur(X13);
        }
    }
}

/// Whether runtime primitive `p` is the one called `name`.
fn prim_named(p: usize, name: &str) -> bool {
    fixpt_runtime::PRIMITIVES.get(p).is_some_and(|d| d.name == name)
}

impl Asm {
    /// `what` on `REG1`… into `RESULT`, without calling out; to `slow` when
    /// it cannot be done so.
    fn inline(&mut self, what: &str, slow: Label) {
        match what {
            // A pair from the heap's free space, if there is room short of
            // where a collection is due: `top` bumped by two words.
            "cons" => {
                self.e(ldr(W, ST, off(offset_of!(State, words))));
                self.e(ldr(X13, ST, off(offset_of!(State, top))));
                self.e(ldr(X14, X13, 0));
                self.e(ldr(X15, ST, off(offset_of!(State, alloc_limit))));
                self.e(add_imm(X16, X14, 2));
                self.e(cmp(X16, X15));
                self.b_cond(Cond::Hi, slow);
                // The pair's address, and, off the path from `top` to the
                // result, its tag added to the base first.
                self.e(add_lsl(X11, W, X14, 3));
                self.e(add_imm(W, W, TAG_PAIR as u32));
                self.e(stp(1, 2, X11, 0));
                self.e(str(X16, X13, 0));
                self.e(add_lsl(RESULT, W, X14, 3));
            }
            // A string's length is its suffix's first word; its characters
            // follow, two to a word.
            "string-length" => {
                self.e(mov(X11, 1));
                self.e(ldur(X15, X11, -4));
                self.e(add_lsl(RESULT, XZR, X15, 3));
            }
            "string-ref" => {
                self.e(mov(X11, 1));
                self.e(ldur(X15, X11, -4));
                self.e(asr_imm(X13, 2, 3));
                self.e(cmp(X13, X15));
                self.b_cond(Cond::Hs, slow);
                self.e(add_lsl(X14, X11, X13, 2));
                self.e(ldur_w(X15, X14, 4));
                self.value(X16, Value::char('\0'));
                self.e(add_lsl(RESULT, X16, X15, 8));
            }
            // A pair in a region's current chunk, if the handle has a slot
            // in the heap's table and the chunk has room: its fill bumped
            // by two words. Anything else calls in: `#f`, the heap's; a
            // region with no chunk yet, or a full one (its fill and end
            // are 0 when it has none).
            "rcons" => {
                self.e(tst_low(1, 3));
                self.b_cond(Cond::Ne, slow);
                self.e(cmp_imm(1, 8 * fixpt_heap::heap::REGION_SLOTS as u32));
                self.b_cond(Cond::Hs, slow);
                self.e(ldr(X13, ST, off(offset_of!(State, regions))));
                self.e(add_lsl(X13, X13, 1, 1));
                self.e(ldp(X14, X15, X13, 0));
                self.e(add_imm(X16, X14, 2));
                self.e(cmp(X16, X15));
                self.b_cond(Cond::Hi, slow);
                self.e(ldr(X15, ST, off(offset_of!(State, words))));
                self.e(add_lsl(X11, X15, X14, 3));
                self.e(stp(2, 3, X11, 0));
                self.e(str(X16, X13, 0));
                self.e(add_imm(RESULT, X11, TAG_PAIR as u32));
            }
            other => unreachable!("{other} is not done inline"),
        }
    }
}

/// A register word's machine code: its register entry first, then an
/// instruction's code after another; and where each cell's resume point
/// is (`-1` for none), for [`NativeMachine::install`].
pub fn assemble_register_word(heap: &Heap, rw: Value, far: [i64; 2]) -> Result<(Vec<u32>, Vec<i64>), String> {
    let fields = heap.bloblet_head(rw).fields;
    let cells: Vec<Value> = (WORD_CELL0..=fields).map(|k| heap.bloblet_slot(rw, k)).collect();
    let mut starts = vec![false; cells.len() + 1];
    let mut i = 0;
    while i < cells.len() {
        starts[i] = true;
        i += 1 + OPS[cells[i].as_fixnum() as usize].1;
    }
    let mut a = Asm::new();
    let labels: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
    let mut resume = vec![-1i64; cells.len()];
    let far_exit = a.exit_common;
    let near_exit = a.label();
    a.exit_common = near_exit;
    // The register entry.
    a.fuel();
    a.rs_limit();
    a.pool(fields);
    // Where a backward branch goes: a loop's head, 32-aligned (words are),
    // so that the loop's speed does not depend on where the word lands.
    let mut loop_heads = vec![false; cells.len() + 1];
    let mut j = 0;
    while j < cells.len() {
        let (name, n, _) = OPS[cells[j].as_fixnum() as usize];
        if name == "branch" || name == "branchf" {
            let to = j as i64 + 2 + cells[j + 1].as_fixnum();
            if to <= j as i64 {
                loop_heads[to as usize] = true;
            }
        }
        j += 1 + n;
    }
    let mut i = 0;
    while i < cells.len() {
        if loop_heads[i] {
            while a.here() % 8 != 0 {
                a.e(NOP);
            }
        }
        a.bind(labels[i]);
        let (name, n, _) = OPS[cells[i].as_fixnum() as usize];
        let o = |j: usize| cells[i + 1 + j];
        let f = |j: usize| WORD_CELL0 + i + 1 + j;
        let next = i + 1 + n;
        let k = |v: Value| v.as_fixnum() as usize;
        match name {
            "args" => {}
            "const" => {
                let v = o(0);
                if v.is_fixnum() || v.raw() & 7 == 3 {
                    a.es(&mov_imm64(RESULT, v.raw()));
                } else {
                    a.cell(RESULT, f(0), fields);
                }
            }
            "global" | "setglbl" => {
                a.cell(X16, f(0), fields);
                a.e(mov(X11, X16));
                a.e(if name == "global" { ldur(RESULT, X11, field_off(2)) } else { stur(RESULT, X11, field_off(2)) });
            }
            "reg" => a.e(mov(RESULT, reg(k(o(0))))),
            "setreg" => a.e(mov(reg(k(o(0))), RESULT)),
            "movereg" => a.e(mov(reg(k(o(1))), reg(k(o(0))))),
            "lexical" => {
                a.e(mov(X11, CLO));
                a.field_of(RESULT, X11, CLOSURE_FREE0 + k(o(0)));
            }
            // A frame of `m` slots, and below them the link: where a call
            // by `blr` returns to, which a call from this frame replaces.
            // The collector scans the frame, and the link reads as a
            // fixnum: every point a `blr` returns to is 8-aligned (as
            // Larceny aligns its return points), and a call no `blr` made
            // has 0 (the adapter).
            "save" => {
                let m = k(o(0));
                a.sub_const(DSP, DSP, 8 * (m as u64 + 1));
                a.value(X15, Value::FALSE);
                for s in 1..=m {
                    a.e(str(X15, DSP, 8 * s as u32));
                }
                a.e(str(LR, DSP, 0));
                a.e(add_imm(FP, DSP, 8 * m as u32));
                a.ds_limit();
            }
            "pop" => {
                let m = k(o(0));
                a.slot(LR, m, false);
                a.e(add_imm(DSP, DSP, 8 * (m as u32 + 1)));
            }
            "stack" => a.slot(RESULT, k(o(0)), false),
            "setstk" => a.slot(RESULT, k(o(0)), true),
            "load" => a.slot(reg(k(o(0))), k(o(1)), false),
            "store" => a.slot(reg(k(o(0))), k(o(1)), true),
            "op1" => match ROUTINES[k(o(0))].0 {
                r @ ("pair-car" | "pair-cdr") => {
                    a.e(ldur(RESULT, RESULT, if r == "pair-car" { -1 } else { 7 }));
                }
                r => return Err(format!("op1 {r} in register code")),
            },
            "op2" | "op2imm" => {
                let other = if name == "op2" {
                    reg(k(o(1)))
                } else {
                    let v = o(1);
                    if v.is_fixnum() || v.raw() & 7 == 3 {
                        a.es(&mov_imm64(X13, v.raw()));
                    } else {
                        a.cell(X13, f(1), fields);
                    }
                    X13
                };
                match ROUTINES[k(o(0))].0 {
                    r @ ("int-add" | "int-sub") => {
                        a.e(if r == "int-add" { adds(RESULT, RESULT, other) } else { subs(RESULT, RESULT, other) });
                        a.trap_if(Cond::Vs, Trap::Overflow { routine: if r == "int-add" { "int-add" } else { "int-sub" } });
                    }
                    r @ ("int-less" | "eq") => {
                        a.e(cmp(RESULT, other));
                        a.value(X16, Value::TRUE);
                        a.value(X15, Value::FALSE);
                        a.e(csel(RESULT, X16, X15, if r == "eq" { Cond::Eq } else { Cond::Lt }));
                    }
                    r => return Err(format!("{name} {r} in register code")),
                }
            }
            "field" => {
                a.field_of(RESULT, RESULT, k(o(0)));
            }
            "setfield" => {
                a.e(mov(X11, RESULT));
                let off = field_off(k(o(0)));
                if off >= -256 {
                    a.e(stur(reg(k(o(1))), X11, off));
                } else {
                    a.sub_const(X16, X11, -off as u64);
                    a.e(str(reg(k(o(1))), X16, 0));
                }
            }
            "prim" | "lambda" | "threaded" => {
                let (count, routine_n, at) = match name {
                    "prim" => (k(o(1)), routine("prim"), f(0)),
                    "lambda" => (k(o(1)), routine("closure"), f(0)),
                    _ => (k(o(1)), k(o(0)) as u64, WORD_CELL0 + next),
                };
                // Some are done here, when they can be: the call-out is then
                // only the way for what cannot (a full heap, an index out of
                // range, which it reports).
                let slow = a.label();
                let done = a.label();
                let inline = match (name, count) {
                    ("threaded", 2) if ROUTINES[k(o(0))].0 == "cons" => Some("cons"),
                    ("prim", 1) if prim_named(k(o(0)), "string-length") => Some("string-length"),
                    ("prim", 2) if prim_named(k(o(0)), "string-ref") => Some("string-ref"),
                    ("prim", 3) if prim_named(k(o(0)), "%region-cons") => Some("rcons"),
                    _ => None,
                };
                if let Some(what) = inline {
                    a.inline(what, slow);
                    a.b(done);
                }
                a.bind(slow);
                a.push_regs(count);
                a.r_callout(routine_n, at);
                resume[next] = a.here() as i64;
                a.resumed(fields);
                a.bind(done);
            }
            "invoke" | "tailinvoke" => {
                let tail = name == "tailinvoke";
                let count = k(o(0));
                let threaded = a.label();
                // The callee, its word, and the word's twin.
                a.e(mov(W, RESULT));
                a.e(mov(X11, W));
                a.e(ldur(X12, X11, field_off(CLOSURE_WORD)));
                a.e(mov(X11, X12));
                a.e(ldur(X10, X11, field_off(WORD_TWIN)));
                a.value(X15, Value::FALSE);
                a.e(cmp(X10, X15));
                a.b_cond(Cond::Eq, threaded);
                a.e(mov(X11, X10));
                a.e(ldur(X15, X11, field_off(WORD_ENTRY)));
                a.cbz(X15, threaded);
                // Register code: the arguments stay where they are. A call
                // pushes a return entry marked as one `blr` made (its `8k`
                // negated), so that the callee returns by `ret`, with the
                // value in `RESULT`. The entry is loaded last: making the
                // return entry may need X16 for a large offset.
                let back = a.label();
                if !tail {
                    a.ip_at(WORD_CELL0 + next);
                    a.push_return_marked();
                }
                a.e(ldr_reg(X16, TABLE, X15));
                a.e(mov(CLO, W));
                a.e(mov(CUR, X10));
                if tail {
                    a.e(br(X16));
                } else {
                    // The instruction after the `blr` 8-aligned (words are).
                    if a.here() % 2 == 0 {
                        a.e(NOP);
                    }
                    a.e(blr(X16));
                    a.b(back);
                }
                // Stack code: the arguments as its frame. It returns the
                // stack's way, so an entry this procedure was called with
                // by `blr` is unmarked first, in a tail call.
                a.bind(threaded);
                a.fuel();
                a.push_regs(count);
                a.ds_limit();
                a.rs_limit();
                if tail {
                    a.unmark_return();
                } else {
                    a.ip_at(WORD_CELL0 + next);
                    a.push_return();
                }
                if count == 0 {
                    a.e(sub_imm(FP, DSP, 8));
                } else {
                    a.e(add_imm(FP, DSP, 8 * (count as u32 - 1)));
                }
                a.e(mov(CLO, W));
                a.e(mov(CUR, X12));
                a.ip_at(WORD_CELL0);
                a.e(movz(X13, (8 * WORD_CELL0) as u32, 0));
                a.enter_cur(X13);
                if !tail {
                    // Returned to the stack's way (the resume table), the
                    // value on the data stack; or by `ret`, in `RESULT`.
                    resume[next] = a.here() as i64;
                    a.e(ldr_post(RESULT, DSP, 8));
                    a.bind(back);
                    a.pool(fields);
                }
            }
            // To an entry a `blr` pushed: the caller's registers from it,
            // and back to the link. By `br`, not `ret`: `ret` is predicted
            // from the processor's stack of return addresses, which a deep
            // recursion (a `map` of a long list) overflows, and then nearly
            // every return mispredicts (`docs/performance.md`). To any other
            // entry, the stack's way.
            "return" => {
                let stack = a.label();
                a.e(ldr(X13, RSP, 8));
                a.e(cmp_imm(X13, 0));
                a.b_cond(Cond::Ge, stack);
                a.e(ldp_post(CUR, X13, RSP, 16));
                a.e(ldp_post(X14, CLO, RSP, 16));
                a.fp_decode(X14);
                a.e(br(LR));
                a.bind(stack);
                a.e(str_pre(RESULT, DSP, -8));
                a.pop_return_of(true);
            }
            "branch" | "branchf" => {
                let to = (i as i64 + 2 + o(0).as_fixnum()) as usize;
                if name == "branchf" {
                    a.value(X16, Value::FALSE);
                    a.e(cmp(RESULT, X16));
                    a.b_cond(Cond::Eq, labels[to]);
                } else {
                    if to <= i {
                        a.fuel();
                    }
                    a.b(labels[to]);
                }
            }
            other => return Err(format!("`{other}` in register code")),
        }
        i = next;
    }
    a.bind(labels[cells.len()]);
    // Out of the way of the code that runs: the traps, and a jump to the
    // machine's exit, which may be too far for a conditional branch.
    a.flush_stubs();
    a.bind(near_exit);
    a.b(far_exit);
    a.exit_common = far_exit;
    let [tc, ec] = [a.trap_common, a.exit_common];
    a.bind_at(tc, far[0]);
    a.bind_at(ec, far[1]);
    let _ = (far_exit, starts, REGS);
    Ok((a.finish(), resume))
}

/// The entry a stack-code caller takes into a word with register code: the
/// `n` arguments from its frame into registers, the frame dropped, and on
/// to the register word's entry, native slot `slot`.
pub fn assemble_adapter(n: usize, slot: usize) -> Vec<u32> {
    let mut a = Asm::new();
    for i in 0..n {
        a.e(ldur(reg(i + 1), FP, -8 * i as i64));
    }
    a.e(add_imm(DSP, FP, 8));
    a.e(mov(X11, CUR));
    a.e(ldur(CUR, X11, field_off(WORD_TWIN)));
    a.e(ldr(X16, TABLE, 8 * slot as u32));
    // No `blr` made this call: the link the callee keeps is a fixnum, 0.
    a.e(mov(LR, XZR));
    a.e(br(X16));
    a.finish()
}

impl NativeMachine {
    /// Compile `word`'s register code, if it has some and it is not yet
    /// compiled: the register word's code in a native slot of its own, and
    /// `word` entered through an adapter to it. Whether it did.
    pub fn compile_register_word(&mut self, heap: &mut Heap, word: Value) -> Result<bool, String> {
        let rw = heap.bloblet_slot(word, WORD_TWIN);
        if !heap.is_register_word(rw) || heap.bloblet_slot(rw, WORD_ENTRY).as_fixnum() != 0 {
            return Ok(false);
        }
        let (code, _) = assemble_register_word(heap, rw, [0, 0])?;
        let (at, far) = self.reserve(code.len())?;
        let (code, resume) = assemble_register_word(heap, rw, far)?;
        self.install(heap, rw, at, &code, &resume)?;
        let slot = heap.bloblet_slot(rw, WORD_ENTRY).as_fixnum() as usize;
        let n = heap.bloblet_slot(rw, WORD_CELL0 + 1).as_fixnum() as usize;
        let adapter = assemble_adapter(n, slot);
        let (at, _) = self.reserve(adapter.len())?;
        let cells = heap.bloblet_head(word).fields + 1 - WORD_CELL0;
        let mut starts = vec![-1i64; cells];
        starts[0] = 0;
        self.install(heap, word, at, &adapter, &starts)?;
        Ok(true)
    }
}
