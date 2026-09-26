//! The threaded machine's routines as stencils: Rust functions, compiled by
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
    ($base:expr, $ip:expr, $cur:expr, $dsp:expr, $rsp:expr, $st:expr, $fuel:expr) => {{
        let (base, ip, cur, dsp, rsp, st, fuel) = ($base, $ip, $cur, $dsp, $rsp, $st, $fuel);
        let c = unsafe { rd(ip) };
        let ip = ip.wrapping_sub(8);
        if c & TAG_MASK == 0 {
            become unsafe { routine(st, c) }(base, ip, cur, dsp, rsp, st, fuel, c)
        } else {
            let e = unsafe { field(base, c, WORD_ENTRY) };
            become unsafe { routine(st, e) }(base, ip, cur, dsp, rsp, st, fuel, c)
        }
    }};
}

/// Store the machine into the state, the ip as `8k`.
#[inline(always)]
unsafe fn save(st: *mut State, base: u64, ip: u64, cur: u64, dsp: u64, rsp: u64, fuel: u64) {
    unsafe {
        (*st).cur = cur;
        (*st).d = base.wrapping_add(cur).wrapping_sub(4).wrapping_sub(ip);
        (*st).dsp = dsp;
        (*st).rsp = rsp;
        (*st).fuel = fuel;
    }
}

/// Stop with a trap.
#[inline(always)]
#[allow(clippy::too_many_arguments)]
unsafe fn trap(st: *mut State, code: u64, aux: u64, base: u64, ip: u64, cur: u64, dsp: u64, rsp: u64, fuel: u64) -> u64 {
    unsafe {
        save(st, base, ip, cur, dsp, rsp, fuel);
        // Volatile, so that two constants are not merged into one vector
        // store from a constant pool, which would be a relocation.
        core::intrinsics::volatile_store(&raw mut (*st).status, code);
        core::intrinsics::volatile_store(&raw mut (*st).aux, aux);
    }
    0
}

/// Check fuel and the data stack's limit: where a word is entered and a
/// branch is taken.
macro_rules! checks {
    ($base:ident, $ip:ident, $cur:ident, $dsp:ident, $rsp:ident, $st:ident, $fuel:ident) => {
        let $fuel = $fuel.wrapping_sub(1);
        if $fuel == 0 {
            return unsafe { trap($st, TRAP_OUT_OF_FUEL, 0, $base, $ip, $cur, $dsp, $rsp, $fuel) };
        }
        if $dsp < unsafe { (*$st).ds_limit } {
            return unsafe { trap($st, TRAP_STACK_OVERFLOW, 0, $base, $ip, $cur, $dsp, $rsp, $fuel) };
        }
    };
}

macro_rules! routine {
    ($name:ident, |$base:ident, $ip:ident, $cur:ident, $dsp:ident, $rsp:ident, $st:ident, $fuel:ident, $w:ident| $body:block) => {
        #[unsafe(no_mangle)]
        #[allow(unused_variables, unused_mut)]
        pub unsafe extern "C" fn $name(
            $base: u64,
            $ip: u64,
            $cur: u64,
            $dsp: u64,
            $rsp: u64,
            $st: *mut State,
            $fuel: u64,
            $w: u64,
        ) -> u64 {
            $body
        }
    };
}

// Where the host starts: run the word in `w`.
routine!(st_start, |base, ip, cur, dsp, rsp, st, fuel, w| {
    let e = unsafe { field(base, w, WORD_ENTRY) };
    become unsafe { routine(st, e) }(base, ip, cur, dsp, rsp, st, fuel, w)
});

routine!(st_docol, |base, ip, cur, dsp, rsp, st, fuel, w| {
    checks!(base, ip, cur, dsp, rsp, st, fuel);
    if rsp <= unsafe { (*st).rs_limit } {
        return unsafe { trap(st, TRAP_TOO_DEEP, 0, base, ip, cur, dsp, rsp, fuel) };
    }
    let rsp = rsp - 16;
    unsafe {
        wr(rsp, cur);
        wr(rsp + 8, base.wrapping_add(cur).wrapping_sub(4).wrapping_sub(ip));
    }
    let ip = base.wrapping_add(w).wrapping_sub(4 + 8 * WORD_CELL0);
    next!(base, ip, w, dsp, rsp, st, fuel)
});

routine!(st_exit, |base, ip, cur, dsp, rsp, st, fuel, w| {
    let (cur, d) = unsafe { (rd(rsp), rd(rsp + 8)) };
    let rsp = rsp + 16;
    if cur == FALSE {
        unsafe { save(st, base, ip, cur, dsp, rsp, fuel) };
        return 0;
    }
    let ip = base.wrapping_add(cur).wrapping_sub(4).wrapping_sub(d);
    next!(base, ip, cur, dsp, rsp, st, fuel)
});

routine!(st_halt, |base, ip, cur, dsp, rsp, st, fuel, w| {
    unsafe { save(st, base, ip, cur, dsp, rsp, fuel) };
    0
});

routine!(st_lit, |base, ip, cur, dsp, rsp, st, fuel, w| {
    let x = unsafe { rd(ip) };
    let dsp = dsp - 8;
    unsafe { wr(dsp, x) };
    next!(base, ip - 8, cur, dsp, rsp, st, fuel)
});

routine!(st_branch, |base, ip, cur, dsp, rsp, st, fuel, w| {
    let off = unsafe { rd(ip) };
    let ip = ip.wrapping_sub(8).wrapping_sub(off);
    checks!(base, ip, cur, dsp, rsp, st, fuel);
    next!(base, ip, cur, dsp, rsp, st, fuel)
});

routine!(st_zbranch, |base, ip, cur, dsp, rsp, st, fuel, w| {
    let flag = unsafe { rd(dsp) };
    let dsp = dsp + 8;
    let off = unsafe { rd(ip) };
    let ip = ip.wrapping_sub(8);
    if flag == FALSE {
        let ip = ip.wrapping_sub(off);
        checks!(base, ip, cur, dsp, rsp, st, fuel);
        next!(base, ip, cur, dsp, rsp, st, fuel)
    }
    next!(base, ip, cur, dsp, rsp, st, fuel)
});

routine!(st_execute, |base, ip, cur, dsp, rsp, st, fuel, w| {
    let w = unsafe { rd(dsp) };
    let dsp = dsp + 8;
    if w & TAG_MASK == 0 {
        if w == 0 || w >= 8 * PRIMITIVES {
            return unsafe { trap(st, TRAP_NO_ROUTINE, ((w as i64) >> 3) as u64, base, ip, cur, dsp, rsp, fuel) };
        }
        become unsafe { routine(st, w) }(base, ip, cur, dsp, rsp, st, fuel, w)
    }
    // A word: a bloblet with a trailer, whose header says it is one.
    macro_rules! not_a_word {
        () => {
            return unsafe { trap(st, TRAP_NOT_A_WORD, 0, base, ip, cur, dsp, rsp, fuel) }
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
    let e = unsafe { field(base, w, WORD_ENTRY) };
    become unsafe { routine(st, e) }(base, ip, cur, dsp, rsp, st, fuel, w)
});

routine!(st_dup, |base, ip, cur, dsp, rsp, st, fuel, w| {
    let a = unsafe { rd(dsp) };
    let dsp = dsp - 8;
    unsafe { wr(dsp, a) };
    next!(base, ip, cur, dsp, rsp, st, fuel)
});

routine!(st_drop, |base, ip, cur, dsp, rsp, st, fuel, w| {
    next!(base, ip, cur, dsp + 8, rsp, st, fuel)
});

routine!(st_swap, |base, ip, cur, dsp, rsp, st, fuel, w| {
    unsafe {
        let (b, a) = (rd(dsp), rd(dsp + 8));
        wr(dsp, a);
        wr(dsp + 8, b);
    }
    next!(base, ip, cur, dsp, rsp, st, fuel)
});

routine!(st_over, |base, ip, cur, dsp, rsp, st, fuel, w| {
    let a = unsafe { rd(dsp + 8) };
    let dsp = dsp - 8;
    unsafe { wr(dsp, a) };
    next!(base, ip, cur, dsp, rsp, st, fuel)
});

/// A binary operation on two fixnums, the result replacing them; `$op`
/// gives the result and whether it overflowed.
macro_rules! arith {
    ($name:ident, $r:expr, |$a:ident, $b:ident| $op:expr) => {
        routine!($name, |base, ip, cur, dsp, rsp, st, fuel, w| {
            let ($b, $a) = unsafe { (rd(dsp), rd(dsp + 8)) };
            if ($a | $b) & TAG_MASK != 0 {
                return unsafe { trap(st, TRAP_TYPE, $r, base, ip, cur, dsp, rsp, fuel) };
            }
            let (x, overflowed): (u64, bool) = $op;
            if overflowed {
                return unsafe { trap(st, TRAP_OVERFLOW, $r, base, ip, cur, dsp, rsp, fuel) };
            }
            let dsp = dsp + 8;
            unsafe { wr(dsp, x) };
            next!(base, ip, cur, dsp, rsp, st, fuel)
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

routine!(st_eq, |base, ip, cur, dsp, rsp, st, fuel, w| {
    let (b, a) = unsafe { (rd(dsp), rd(dsp + 8)) };
    let dsp = dsp + 8;
    unsafe { wr(dsp, if a == b { TRUE } else { FALSE }) };
    next!(base, ip, cur, dsp, rsp, st, fuel)
});

macro_rules! pair_part {
    ($name:ident, $r:expr, $off:expr) => {
        routine!($name, |base, ip, cur, dsp, rsp, st, fuel, w| {
            let p = unsafe { rd(dsp) };
            if p & TAG_MASK != TAG_PAIR {
                return unsafe { trap(st, TRAP_TYPE, $r, base, ip, cur, dsp, rsp, fuel) };
            }
            unsafe { wr(dsp, rd(base.wrapping_add(p).wrapping_sub(1) + $off)) };
            next!(base, ip, cur, dsp, rsp, st, fuel)
        });
    };
}

pair_part!(st_car, R_CAR, 0);
pair_part!(st_cdr, R_CDR, 8);

/// Leave the machine for the Rust side of routine `r`, and carry on from
/// the state it leaves, unless it reports a trap.
macro_rules! callout {
    ($r:expr, $base:ident, $ip:ident, $cur:ident, $dsp:ident, $rsp:ident, $st:ident, $fuel:ident) => {{
        unsafe { save($st, $base, $ip, $cur, $dsp, $rsp, $fuel) };
        let f = unsafe { core::mem::transmute::<u64, unsafe extern "C" fn(*mut State, u64) -> u64>((*$st).callout) };
        if unsafe { f($st, $r) } != 0 {
            return 0;
        }
        let s = unsafe { &*$st };
        let (base, cur, dsp, rsp) = (s.base, s.cur, s.dsp, s.rsp);
        let ip = base.wrapping_add(cur).wrapping_sub(4).wrapping_sub(s.d);
        next!(base, ip, cur, dsp, rsp, $st, $fuel)
    }};
}

routine!(st_field_ref, |base, ip, cur, dsp, rsp, st, fuel, w| {
    let (k, obj) = unsafe { (rd(dsp), rd(dsp + 8)) };
    if k & TAG_MASK != 0 || obj & TAG_MASK != TAG_BLOBLET {
        return unsafe { trap(st, TRAP_TYPE, R_FIELD_REF, base, ip, cur, dsp, rsp, fuel) };
    }
    let t = unsafe { field(base, obj, 1) };
    if t & TAG_MASK != TAG_TRAILER {
        callout!(R_FIELD_REF, base, ip, cur, dsp, rsp, st, fuel)
    }
    // 2 ≤ k ≤ F, as 8k against 8F.
    if (k as i64) < 16 || (k as i64) > (t - TAG_TRAILER) as i64 {
        return unsafe { trap(st, TRAP_FIELD, R_FIELD_REF, base, ip, cur, dsp, rsp, fuel) };
    }
    let x = unsafe { rd(base.wrapping_add(obj).wrapping_sub(4).wrapping_sub(k)) };
    let dsp = dsp + 8;
    unsafe { wr(dsp, x) };
    next!(base, ip, cur, dsp, rsp, st, fuel)
});

routine!(st_field_set, |base, ip, cur, dsp, rsp, st, fuel, w| {
    callout!(R_FIELD_SET, base, ip, cur, dsp, rsp, st, fuel)
});

routine!(st_cons, |base, ip, cur, dsp, rsp, st, fuel, w| {
    callout!(R_CONS, base, ip, cur, dsp, rsp, st, fuel)
});
