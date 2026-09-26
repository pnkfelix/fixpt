//! Code written through one view and run through the other.
#![allow(unsafe_code)]

use fixpt_native::CodeSpace;
use fixpt_native::arm64::*;

fn routine(cs: &mut CodeSpace, code: &[u32]) -> usize {
    let at = cs.alloc(code.len() * 4, 16).expect("room");
    cs.write_code(at, code);
    cs.flush(at, code.len() * 4);
    at
}

#[test]
fn generated_code_runs() {
    let mut cs = CodeSpace::new(1).expect("maps");
    let at = routine(&mut cs, &[movz(0, 42, 0), ret()]);
    // SAFETY: `mov x0, #42; ret`.
    assert_eq!(unsafe { cs.call(at, [0; 4]) }, 42);
}

#[test]
fn arguments_arrive_in_registers() {
    let mut cs = CodeSpace::new(1).expect("maps");
    let at = routine(&mut cs, &[add(0, 0, 1), sub(0, 0, 2), add(0, 0, 3), ret()]);
    // SAFETY: arithmetic on x0–x3, then ret.
    assert_eq!(unsafe { cs.call(at, [100, 20, 3, 7]) }, 124);
}

#[test]
fn code_rewritten_in_place_runs_the_new_version() {
    let mut cs = CodeSpace::new(1).expect("maps");
    let at = routine(&mut cs, &[movz(0, 1, 0), ret()]);
    // SAFETY: `mov x0, #n; ret`, before and after.
    assert_eq!(unsafe { cs.call(at, [0; 4]) }, 1);
    cs.write_code(at, &[movz(0, 2, 0)]);
    cs.flush(at, 4);
    assert_eq!(unsafe { cs.call(at, [0; 4]) }, 2);
}

/// A code bloblet's shape: a field the code reads, beside the code. The
/// field changes through the writable view while the code stays executable,
/// with no flush and no change of protection.
#[test]
fn a_field_beside_code_is_writable_while_the_code_runs() {
    let mut cs = CodeSpace::new(1).expect("maps");
    let field = cs.alloc(8, 8).expect("room");
    cs.write_u64(field, 7);
    let code_at = cs.alloc(8, 4).expect("room");
    assert_eq!(code_at, field + 8);
    cs.write_code(code_at, &[ldr_lit(0, -2), ret()]);
    cs.flush(code_at, 8);
    // SAFETY: loads the word before it, then returns.
    assert_eq!(unsafe { cs.call(code_at, [0; 4]) }, 7);
    cs.write_u64(field, 99);
    assert_eq!(unsafe { cs.call(code_at, [0; 4]) }, 99);
}

#[test]
fn a_loop_counts() {
    // x0 = n; x1 = 0; loop: cbz x0 done; add x1,x1,x0; sub x0,x0,#1; b loop; done: mov x0,x1; ret
    let mut cs = CodeSpace::new(1).expect("maps");
    let at = routine(
        &mut cs,
        &[movz(1, 0, 0), cbz(0, 4), add(1, 1, 0), sub_imm(0, 0, 1), b(-3), mov(0, 1), ret()],
    );
    // SAFETY: a loop that terminates for any n, touching only registers.
    assert_eq!(unsafe { cs.call(at, [100, 0, 0, 0]) }, 5050);
}

#[test]
fn a_full_space_says_so() {
    let mut cs = CodeSpace::new(1).expect("maps");
    let size = cs.size();
    assert!(cs.alloc(size, 8).is_some());
    assert!(cs.alloc(8, 8).is_none());
    assert!(cs.offset_of(cs.exec_addr(0)).is_some());
    assert!(cs.offset_of(cs.data_addr(0)).is_none(), "the writable view is not code");
}
