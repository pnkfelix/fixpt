//! The cellular machine's routines as stencils: Rust functions, compiled by
//! the build script with the installed nightly, never linked. Their machine
//! code is copied into a code space as it is.
//!
//! Every routine has the same signature, so the machine lives in the eight
//! argument registers, and every one ends in `become`, a guaranteed tail
//! call, even at `-O0`. So a routine that *returns* returns from the whole
//! run, to the host that called the first one: trapping and finishing need no
//! epilogue.
//!
//! The build script requires that no stencil has a relocation: `NEXT` is
//! inlined into every routine, the routine table is in the state, and every
//! constant comes from `consts.rs`, which it generates from the layout table.
//! So copying a stencil is all it takes to place it. That holds at `-O0` too,
//! which is why the code below avoids anything that stays a call when not
//! optimised: `core`'s methods (the overflow intrinsics instead) and closures
//! (macros instead).
#![no_std]
#![feature(explicit_tail_calls, core_intrinsics)]
#![allow(incomplete_features, internal_features, clippy::missing_safety_doc)]

include!("state.rs");
include!("consts.rs");

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

type Routine = unsafe extern "C" fn(u64, u64, u64, u64, u64, *mut State, u64, u64) -> u64;

#[inline(always)]
unsafe fn rd(a: u64) -> u64 {
    unsafe { *(a as *const u64) }
}

#[inline(always)]
unsafe fn wr(a: u64, v: u64) {
    unsafe { *(a as *mut u64) = v }
}

#[inline(always)]
unsafe fn wr8(a: u64, v: u8) {
    unsafe { *(a as *mut u8) = v }
}

/// Routine `n8 / 8`: a fixnum's bits are already the table offset.
#[inline(always)]
unsafe fn routine(st: *mut State, n8: u64) -> Routine {
    unsafe { core::mem::transmute::<u64, Routine>(rd(&raw const (*st).routines as u64 + n8)) }
}

/// A field of the bloblet `v`, by negative offset.
#[inline(always)]
unsafe fn field(base: u64, v: u64, k: u64) -> u64 {
    unsafe { rd(base.wrapping_add(v).wrapping_sub(4 + 8 * k)) }
}

/// Run the next cell.
macro_rules! next {
    ($base:expr, $ip:expr, $cur:expr, $dsp:expr, $rsp:expr, $st:expr, $fp:expr) => {{
        let (base, ip, cur, dsp, rsp, st, fp) = ($base, $ip, $cur, $dsp, $rsp, $st, $fp);
        let c = unsafe { rd(ip) };
        let ip = ip.wrapping_sub(8);
        if c & TAG_MASK == 0 {
            become unsafe { routine(st, c) }(base, ip, cur, dsp, rsp, st, fp, c)
        } else {
            let e = unsafe { entry_of(base, c) };
            become unsafe { routine(st, e) }(base, ip, cur, dsp, rsp, st, fp, c)
        }
    }};
}

/// A word's entry, `8n`: a routine's, or `docol`'s for a word compiled to
/// machine code for the hand-encoded machine, whose cells run here.
#[inline(always)]
unsafe fn entry_of(base: u64, w: u64) -> u64 {
    let e = unsafe { field(base, w, WORD_ENTRY) };
    if e >= 8 * PRIMITIVES { 0 } else { e }
}

/// Store the machine into the state, the ip as `8k`.
#[inline(always)]
unsafe fn save(st: *mut State, base: u64, ip: u64, cur: u64, dsp: u64, rsp: u64, fp: u64) {
    unsafe {
        (*st).cur = cur;
        (*st).d = base.wrapping_add(cur).wrapping_sub(4).wrapping_sub(ip);
        (*st).dsp = dsp;
        (*st).rsp = rsp;
        (*st).fp = fp_encode(st, fp);
    }
}

/// The frame pointer as a return entry and the state keep it:
/// `ds_base - 8 - fp`, the bits of its fixnum index.
#[inline(always)]
unsafe fn fp_encode(st: *mut State, fp: u64) -> u64 {
    unsafe { (*st).ds_base.wrapping_sub(8).wrapping_sub(fp) }
}
#[inline(always)]
unsafe fn fp_decode(st: *mut State, enc: u64) -> u64 {
    unsafe { (*st).ds_base.wrapping_sub(8).wrapping_sub(enc) }
}

/// Stop with a trap.
#[inline(always)]
#[allow(clippy::too_many_arguments)]
unsafe fn trap(st: *mut State, code: u64, aux: u64, base: u64, ip: u64, cur: u64, dsp: u64, rsp: u64, fp: u64) -> u64 {
    unsafe {
        save(st, base, ip, cur, dsp, rsp, fp);
        // Volatile, so that two constants are not merged into one vector
        // store from a constant pool, which would be a relocation.
        core::intrinsics::volatile_store(&raw mut (*st).status, code);
        core::intrinsics::volatile_store(&raw mut (*st).aux, aux);
    }
    0
}

/// Check fp and the data stack's limit: where a word is entered and a
/// branch is taken.
macro_rules! checks {
    ($base:ident, $ip:ident, $cur:ident, $dsp:ident, $rsp:ident, $st:ident, $fp:ident) => {
        // Fuel is in the state: the argument registers are the frame's.
        let fuel = unsafe { (*$st).fuel }.wrapping_sub(1);
        unsafe { (*$st).fuel = fuel };
        if fuel == 0 {
            return unsafe { trap($st, TRAP_OUT_OF_FUEL, 0, $base, $ip, $cur, $dsp, $rsp, $fp) };
        }
        if $dsp < unsafe { (*$st).ds_limit } {
            return unsafe { trap($st, TRAP_STACK_OVERFLOW, 0, $base, $ip, $cur, $dsp, $rsp, $fp) };
        }
    };
}

macro_rules! routine {
    ($name:ident, |$base:ident, $ip:ident, $cur:ident, $dsp:ident, $rsp:ident, $st:ident, $fp:ident, $w:ident| $body:block) => {
        #[unsafe(no_mangle)]
        #[allow(unused_variables, unused_mut)]
        pub unsafe extern "C" fn $name(
            $base: u64,
            $ip: u64,
            $cur: u64,
            $dsp: u64,
            $rsp: u64,
            $st: *mut State,
            $fp: u64,
            $w: u64,
        ) -> u64 {
            $body
        }
    };
}

// Where the host starts: run the word in `w`.
routine!(st_start, |base, ip, cur, dsp, rsp, st, fp, w| {
    let e = unsafe { entry_of(base, w) };
    become unsafe { routine(st, e) }(base, ip, cur, dsp, rsp, st, fp, w)
});

/// Leave the machine for the Rust side of routine `r`, and carry on from
/// the state it leaves, unless it reports a trap.
macro_rules! callout {
    ($r:expr, $base:ident, $ip:ident, $cur:ident, $dsp:ident, $rsp:ident, $st:ident, $fp:ident) => {{
        unsafe { save($st, $base, $ip, $cur, $dsp, $rsp, $fp) };
        let f = unsafe { core::mem::transmute::<u64, unsafe extern "C" fn(*mut State, u64) -> u64>((*$st).callout) };
        if unsafe { f($st, $r) } != 0 {
            return 0;
        }
        let s = unsafe { &*$st };
        let (base, cur, dsp, rsp) = (s.base, s.cur, s.dsp, s.rsp);
        let ip = base.wrapping_add(cur).wrapping_sub(4).wrapping_sub(s.d);
        let fp = unsafe { fp_decode($st, s.fp) };
        next!(base, ip, cur, dsp, rsp, $st, fp)
    }};
}

/// Push a return entry `(cur, 8k, fp, closure)` for where this word is.
#[inline(always)]
unsafe fn push_return(st: *mut State, base: u64, ip: u64, cur: u64, rsp: u64, fp: u64) -> u64 {
    let rsp = rsp - 32;
    unsafe {
        wr(rsp, cur);
        wr(rsp + 8, base.wrapping_add(cur).wrapping_sub(4).wrapping_sub(ip));
        wr(rsp + 16, fp_encode(st, fp));
        wr(rsp + 24, (*st).clo);
    }
    rsp
}

/// Whether `v` is a cellular closure: a bloblet with a trailer, whose
/// header says so.
#[inline(always)]
unsafe fn is_closure(base: u64, v: u64) -> bool {
    if v & TAG_MASK != TAG_BLOBLET {
        return false;
    }
    let t = unsafe { field(base, v, 1) };
    if t & TAG_MASK != TAG_TRAILER {
        return false;
    }
    let header = unsafe { rd(base.wrapping_add(v).wrapping_sub(4 + 8 * ((t >> 3) + 1))) };
    (header >> 3) & 0xff == CLOSURE_KIND
}

routine!(st_docol, |base, ip, cur, dsp, rsp, st, fp, w| {
    checks!(base, ip, cur, dsp, rsp, st, fp);
    if rsp <= unsafe { (*st).rs_limit } {
        return unsafe { trap(st, TRAP_TOO_DEEP, 0, base, ip, cur, dsp, rsp, fp) };
    }
    let rsp = unsafe { push_return(st, base, ip, cur, rsp, fp) };
    let ip = base.wrapping_add(w).wrapping_sub(4 + 8 * WORD_CELL0);
    next!(base, ip, w, dsp, rsp, st, fp)
});

/// Return to the entry on top of the return stack, or leave the machine at
/// the bottom one (whose word is `#f`).
macro_rules! pop_return {
    ($base:ident, $ip:ident, $dsp:ident, $rsp:ident, $st:ident, $fp:ident) => {{
        // Past the prompts' and marks' entries, which are not returns.
        let mut rsp = $rsp;
        while matches!(unsafe { rd(rsp) }, PROMPT_MARK | MARK_MARK) {
            rsp += 32;
        }
        let (cur, d, enc, clo) = unsafe { (rd(rsp), rd(rsp + 8), rd(rsp + 16), rd(rsp + 24)) };
        let rsp = rsp + 32;
        if cur == FALSE {
            unsafe { save($st, $base, $ip, cur, $dsp, rsp, $fp) };
            return 0;
        }
        unsafe { (*$st).clo = clo };
        let fp = unsafe { fp_decode($st, enc) };
        let ip = $base.wrapping_add(cur).wrapping_sub(4).wrapping_sub(d);
        next!($base, ip, cur, $dsp, rsp, $st, fp)
    }};
}

routine!(st_exit, |base, ip, cur, dsp, rsp, st, fp, w| { pop_return!(base, ip, dsp, rsp, st, fp) });

// Code compiled from FX-26: frames on the data stack, flat closures,
// globals, calls; as `fixpt_engine::cellular` has them.

routine!(st_slot, |base, ip, cur, dsp, rsp, st, fp, w| {
    let i8 = unsafe { rd(ip) };
    let at = fp.wrapping_sub(i8);
    if at < dsp {
        return unsafe { trap(st, TRAP_FIELD, R_SLOT, base, ip, cur, dsp, rsp, fp) };
    }
    let dsp = dsp - 8;
    unsafe { wr(dsp, rd(at)) };
    next!(base, ip - 8, cur, dsp, rsp, st, fp)
});

routine!(st_slot_set, |base, ip, cur, dsp, rsp, st, fp, w| {
    let i8 = unsafe { rd(ip) };
    let at = fp.wrapping_sub(i8);
    let x = unsafe { rd(dsp) };
    let dsp = dsp + 8;
    if at < dsp {
        return unsafe { trap(st, TRAP_FIELD, R_SLOT_SET, base, ip, cur, dsp, rsp, fp) };
    }
    unsafe { wr(at, x) };
    next!(base, ip - 8, cur, dsp, rsp, st, fp)
});

routine!(st_free, |base, ip, cur, dsp, rsp, st, fp, w| {
    let i8 = unsafe { rd(ip) };
    let clo = unsafe { (*st).clo };
    if !unsafe { is_closure(base, clo) } {
        return unsafe { trap(st, TRAP_FIELD, R_FREE, base, ip, cur, dsp, rsp, fp) };
    }
    let k8 = i8 + 8 * CLOSURE_FREE0;
    let t = unsafe { field(base, clo, 1) };
    if k8 > t - TAG_TRAILER {
        return unsafe { trap(st, TRAP_FIELD, R_FREE, base, ip, cur, dsp, rsp, fp) };
    }
    let x = unsafe { rd(base.wrapping_add(clo).wrapping_sub(4).wrapping_sub(k8)) };
    let dsp = dsp - 8;
    unsafe { wr(dsp, x) };
    next!(base, ip - 8, cur, dsp, rsp, st, fp)
});

routine!(st_global, |base, ip, cur, dsp, rsp, st, fp, w| {
    let g = unsafe { rd(ip) };
    let dsp = dsp - 8;
    unsafe { wr(dsp, field(base, g, 2)) };
    next!(base, ip - 8, cur, dsp, rsp, st, fp)
});

routine!(st_global_set, |base, ip, cur, dsp, rsp, st, fp, w| {
    let g = unsafe { rd(ip) };
    let at = base.wrapping_add(g).wrapping_sub(4 + 16);
    unsafe { wr(at, rd(dsp)) };
    // The write barrier: the card of the word written marked.
    unsafe { wr8((*st).cards.wrapping_add(at >> 9), 1) };
    next!(base, ip - 8, cur, dsp + 8, rsp, st, fp)
});

/// `call` and `tailcall`: a cellular closure on top, over a frame of the n
/// values below it. Anything else goes the Rust machine's way.
macro_rules! call {
    ($tail:expr, $typed:expr, $r:expr, $base:ident, $ip:ident, $cur:ident, $dsp:ident, $rsp:ident, $st:ident, $fp:ident) => {{
        let c = unsafe { rd($dsp) };
        // A typed call's callee is a closure, by the checker: no test, no call-out.
        if !$typed && !unsafe { is_closure($base, c) } {
            callout!($r, $base, $ip, $cur, $dsp, $rsp, $st, $fp)
        }
        if $typed && $tail {
            // A typed tail call grows neither stack: only fuel is checked.
            let fuel = unsafe { (*$st).fuel }.wrapping_sub(1);
            unsafe { (*$st).fuel = fuel };
            if fuel == 0 {
                return unsafe { trap($st, TRAP_OUT_OF_FUEL, 0, $base, $ip, $cur, $dsp, $rsp, $fp) };
            }
        } else {
            checks!($base, $ip, $cur, $dsp, $rsp, $st, $fp);
        }
        if !($typed && $tail) && $rsp <= unsafe { (*$st).rs_limit } {
            return unsafe { trap($st, TRAP_TOO_DEEP, 0, $base, $ip, $cur, $dsp, $rsp, $fp) };
        }
        let n8 = unsafe { rd($ip) };
        let ip = $ip - 8;
        let dsp = $dsp + 8;
        let (dsp, rsp, fp) = if $tail {
            // Slide the n arguments down over this frame, deepest first.
            let mut from = dsp + n8 - 8;
            let mut to = $fp;
            let mut left = n8;
            while left > 0 {
                unsafe { wr(to, rd(from)) };
                from -= 8;
                to -= 8;
                left -= 8;
            }
            (to + 8, $rsp, $fp)
        } else {
            let rsp = unsafe { push_return($st, $base, ip, $cur, $rsp, $fp) };
            (dsp, rsp, dsp + n8 - 8)
        };
        unsafe { (*$st).clo = c };
        let cur = unsafe { field($base, c, CLOSURE_WORD) };
        let ip = $base.wrapping_add(cur).wrapping_sub(4 + 8 * WORD_CELL0);
        next!($base, ip, cur, dsp, rsp, $st, fp)
    }};
}

routine!(st_call, |base, ip, cur, dsp, rsp, st, fp, w| { call!(false, false, R_CALL, base, ip, cur, dsp, rsp, st, fp) });
routine!(st_tailcall, |base, ip, cur, dsp, rsp, st, fp, w| { call!(true, false, R_TAILCALL, base, ip, cur, dsp, rsp, st, fp) });
routine!(st_tcall, |base, ip, cur, dsp, rsp, st, fp, w| { call!(false, true, R_TCALL, base, ip, cur, dsp, rsp, st, fp) });
routine!(st_ttailcall, |base, ip, cur, dsp, rsp, st, fp, w| { call!(true, true, R_TTAILCALL, base, ip, cur, dsp, rsp, st, fp) });

routine!(st_return, |base, ip, cur, dsp, rsp, st, fp, w| {
    let x = unsafe { rd(dsp) };
    if dsp + 8 > fp + 8 {
        return unsafe { trap(st, TRAP_UNDERFLOW, R_RETURN, base, ip, cur, dsp, rsp, fp) };
    }
    let dsp = fp;
    unsafe { wr(dsp, x) };
    pop_return!(base, ip, dsp, rsp, st, fp)
});

// Any other routine: the Rust machine runs it on these stacks (the
// call-out's round trip). Reached through a cell, `w` is its number's
// fixnum; through a word, the word's entry is.
routine!(st_other, |base, ip, cur, dsp, rsp, st, fp, w| {
    let n8 = if w & TAG_MASK == 0 { w } else { unsafe { entry_of(base, w) } };
    callout!(n8 >> 3, base, ip, cur, dsp, rsp, st, fp)
});

routine!(st_halt, |base, ip, cur, dsp, rsp, st, fp, w| {
    unsafe { save(st, base, ip, cur, dsp, rsp, fp) };
    0
});

routine!(st_lit, |base, ip, cur, dsp, rsp, st, fp, w| {
    let x = unsafe { rd(ip) };
    let dsp = dsp - 8;
    unsafe { wr(dsp, x) };
    next!(base, ip - 8, cur, dsp, rsp, st, fp)
});

routine!(st_branch, |base, ip, cur, dsp, rsp, st, fp, w| {
    let off = unsafe { rd(ip) };
    let ip = ip.wrapping_sub(8).wrapping_sub(off);
    checks!(base, ip, cur, dsp, rsp, st, fp);
    next!(base, ip, cur, dsp, rsp, st, fp)
});

routine!(st_zbranch, |base, ip, cur, dsp, rsp, st, fp, w| {
    let flag = unsafe { rd(dsp) };
    let dsp = dsp + 8;
    let off = unsafe { rd(ip) };
    let ip = ip.wrapping_sub(8);
    if flag == FALSE {
        let ip = ip.wrapping_sub(off);
        checks!(base, ip, cur, dsp, rsp, st, fp);
        next!(base, ip, cur, dsp, rsp, st, fp)
    }
    next!(base, ip, cur, dsp, rsp, st, fp)
});

routine!(st_execute, |base, ip, cur, dsp, rsp, st, fp, w| {
    let w = unsafe { rd(dsp) };
    let dsp = dsp + 8;
    if w & TAG_MASK == 0 {
        if w == 0 || w >= 8 * PRIMITIVES {
            return unsafe { trap(st, TRAP_NO_ROUTINE, ((w as i64) >> 3) as u64, base, ip, cur, dsp, rsp, fp) };
        }
        become unsafe { routine(st, w) }(base, ip, cur, dsp, rsp, st, fp, w)
    }
    // A word: a bloblet with a trailer, whose header says it is one.
    macro_rules! not_a_word {
        () => {
            return unsafe { trap(st, TRAP_NOT_A_WORD, 0, base, ip, cur, dsp, rsp, fp) }
        };
    }
    if w & TAG_MASK != TAG_BLOBLET {
        not_a_word!();
    }
    let t = unsafe { field(base, w, 1) };
    if t & TAG_MASK != TAG_TRAILER {
        not_a_word!();
    }
    let fields = t >> 3;
    let header = unsafe { rd(base.wrapping_add(w).wrapping_sub(4 + 8 * (fields + 1))) };
    if (header >> 3) & 0xff != WORD_KIND {
        not_a_word!();
    }
    let e = unsafe { entry_of(base, w) };
    become unsafe { routine(st, e) }(base, ip, cur, dsp, rsp, st, fp, w)
});

routine!(st_dup, |base, ip, cur, dsp, rsp, st, fp, w| {
    let a = unsafe { rd(dsp) };
    let dsp = dsp - 8;
    unsafe { wr(dsp, a) };
    next!(base, ip, cur, dsp, rsp, st, fp)
});

routine!(st_drop, |base, ip, cur, dsp, rsp, st, fp, w| {
    next!(base, ip, cur, dsp + 8, rsp, st, fp)
});

routine!(st_swap, |base, ip, cur, dsp, rsp, st, fp, w| {
    unsafe {
        let (b, a) = (rd(dsp), rd(dsp + 8));
        wr(dsp, a);
        wr(dsp + 8, b);
    }
    next!(base, ip, cur, dsp, rsp, st, fp)
});

routine!(st_over, |base, ip, cur, dsp, rsp, st, fp, w| {
    let a = unsafe { rd(dsp + 8) };
    let dsp = dsp - 8;
    unsafe { wr(dsp, a) };
    next!(base, ip, cur, dsp, rsp, st, fp)
});

/// A binary operation on two fixnums, the result replacing them; `$op`
/// gives the result and whether it overflowed.
macro_rules! arith {
    ($name:ident, $r:expr, |$a:ident, $b:ident| $op:expr) => {
        routine!($name, |base, ip, cur, dsp, rsp, st, fp, w| {
            let ($b, $a) = unsafe { (rd(dsp), rd(dsp + 8)) };
            if ($a | $b) & TAG_MASK != 0 {
                return unsafe { trap(st, TRAP_TYPE, $r, base, ip, cur, dsp, rsp, fp) };
            }
            let (x, overflowed): (u64, bool) = $op;
            if overflowed {
                return unsafe { trap(st, TRAP_OVERFLOW, $r, base, ip, cur, dsp, rsp, fp) };
            }
            let dsp = dsp + 8;
            unsafe { wr(dsp, x) };
            next!(base, ip, cur, dsp, rsp, st, fp)
        });
    };
}

arith!(st_add, R_ADD, |a, b| {
    let (x, o) = core::intrinsics::add_with_overflow(a as i64, b as i64);
    (x as u64, o)
});
arith!(st_sub, R_SUB, |a, b| {
    let (x, o) = core::intrinsics::sub_with_overflow(a as i64, b as i64);
    (x as u64, o)
});
arith!(st_less, R_LESS, |a, b| (if (a as i64) < (b as i64) { TRUE } else { FALSE }, false));

routine!(st_eq, |base, ip, cur, dsp, rsp, st, fp, w| {
    let (b, a) = unsafe { (rd(dsp), rd(dsp + 8)) };
    let dsp = dsp + 8;
    unsafe { wr(dsp, if a == b { TRUE } else { FALSE }) };
    next!(base, ip, cur, dsp, rsp, st, fp)
});

macro_rules! pair_part {
    ($name:ident, $r:expr, $off:expr) => {
        routine!($name, |base, ip, cur, dsp, rsp, st, fp, w| {
            let p = unsafe { rd(dsp) };
            if p & TAG_MASK != TAG_PAIR {
                return unsafe { trap(st, TRAP_TYPE, $r, base, ip, cur, dsp, rsp, fp) };
            }
            unsafe { wr(dsp, rd(base.wrapping_add(p).wrapping_sub(1) + $off)) };
            next!(base, ip, cur, dsp, rsp, st, fp)
        });
    };
}

pair_part!(st_car, R_CAR, 0);
pair_part!(st_cdr, R_CDR, 8);


routine!(st_field_ref, |base, ip, cur, dsp, rsp, st, fp, w| {
    let (k, obj) = unsafe { (rd(dsp), rd(dsp + 8)) };
    if k & TAG_MASK != 0 || obj & TAG_MASK != TAG_BLOBLET {
        return unsafe { trap(st, TRAP_TYPE, R_FIELD_REF, base, ip, cur, dsp, rsp, fp) };
    }
    let t = unsafe { field(base, obj, 1) };
    if t & TAG_MASK != TAG_TRAILER {
        callout!(R_FIELD_REF, base, ip, cur, dsp, rsp, st, fp)
    }
    // 2 ≤ k ≤ F, as 8k against 8F.
    if (k as i64) < 16 || (k as i64) > (t - TAG_TRAILER) as i64 {
        return unsafe { trap(st, TRAP_FIELD, R_FIELD_REF, base, ip, cur, dsp, rsp, fp) };
    }
    let x = unsafe { rd(base.wrapping_add(obj).wrapping_sub(4).wrapping_sub(k)) };
    let dsp = dsp + 8;
    unsafe { wr(dsp, x) };
    next!(base, ip, cur, dsp, rsp, st, fp)
});

// Typed: the checker has proved the operands' types.
macro_rules! int_arith {
    ($name:ident, $r:expr, |$a:ident, $b:ident| $op:expr) => {
        routine!($name, |base, ip, cur, dsp, rsp, st, fp, w| {
            let ($b, $a) = unsafe { (rd(dsp), rd(dsp + 8)) };
            let (x, overflowed): (u64, bool) = $op;
            // A bignum, or a sum past a fixnum: the Rust side's, which
            // makes or compares bignums (PLAN.md, Q2).
            if overflowed || ($a | $b) & TAG_MASK != 0 {
                callout!($r, base, ip, cur, dsp, rsp, st, fp)
            }
            let dsp = dsp + 8;
            unsafe { wr(dsp, x) };
            next!(base, ip, cur, dsp, rsp, st, fp)
        });
    };
}

int_arith!(st_int_add, R_INT_ADD, |a, b| {
    let (x, o) = core::intrinsics::add_with_overflow(a as i64, b as i64);
    (x as u64, o)
});
int_arith!(st_int_sub, R_INT_SUB, |a, b| {
    let (x, o) = core::intrinsics::sub_with_overflow(a as i64, b as i64);
    (x as u64, o)
});
int_arith!(st_int_less, R_INT_LESS, |a, b| (if (a as i64) < (b as i64) { TRUE } else { FALSE }, false));
int_arith!(st_int_eq, R_INT_EQ, |a, b| (if a == b { TRUE } else { FALSE }, false));

// A list may be `nil`: `car` of it traps, as `car`'s does.
pair_part!(st_pair_car, R_PAIR_CAR, 0);
pair_part!(st_pair_cdr, R_PAIR_CDR, 8);

routine!(st_field, |base, ip, cur, dsp, rsp, st, fp, w| {
    let k = unsafe { rd(ip) };
    let ip = ip - 8;
    let obj = unsafe { rd(dsp) };
    unsafe { wr(dsp, rd(base.wrapping_add(obj).wrapping_sub(4).wrapping_sub(k))) };
    next!(base, ip, cur, dsp, rsp, st, fp)
});

routine!(st_field_set, |base, ip, cur, dsp, rsp, st, fp, w| {
    callout!(R_FIELD_SET, base, ip, cur, dsp, rsp, st, fp)
});

routine!(st_cons, |base, ip, cur, dsp, rsp, st, fp, w| {
    callout!(R_CONS, base, ip, cur, dsp, rsp, st, fp)
});
