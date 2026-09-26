//! The stencil machine: the threaded machine again, its routines written in
//! Rust (`stencils/threaded.rs`) with `become`, compiled by the build script
//! at several optimisation levels, and placed in a code space by copying.
//!
//! Beside the hand-encoded machine in `threaded.rs` it answers two
//! questions: whether Rust with guaranteed tail calls can express the inner
//! interpreter, and what that costs against code we encode ourselves. Both
//! run the same words on the same stacks and state, and are checked against
//! the Rust machine by the same tests.

use crate::codespace::{CodeSpace, Offset};
use crate::threaded::{ROUTINE_SLOTS, Stacks, State};
use fixpt_engine::threaded::Trap;
use fixpt_heap::layout::threaded::ROUTINES;
use fixpt_heap::{Heap, Value};

/// The stencils compiled at one optimisation level.
pub struct StencilSet {
    /// The `-C opt-level`.
    pub opt: &'static str,
    /// `(name, machine code)`: `start`, and one per routine.
    pub stencils: &'static [(&'static str, &'static [u8])],
}

include!(concat!(env!("OUT_DIR"), "/stencils.rs"));

/// The optimisation levels the stencils were compiled at: none, if the
/// build found no nightly compiler.
pub fn opt_levels() -> Vec<&'static str> {
    STENCIL_SETS.iter().map(|s| s.opt).collect()
}

/// The stencil name for a routine.
fn stencil_name(routine: &str) -> String {
    match routine {
        "+" => "add".into(),
        "-" => "sub".into(),
        "<" => "less".into(),
        "field@" => "field_ref".into(),
        "field!" => "field_set".into(),
        "0branch" => "zbranch".into(),
        n => n.into(),
    }
}

pub struct StencilMachine {
    space: CodeSpace,
    start: Offset,
    routines: [u64; ROUTINE_SLOTS],
    stacks: Stacks,
    /// Fuel left after the last run.
    pub fuel_left: u64,
    /// Bytes of machine code placed.
    pub code_bytes: usize,
}

impl StencilMachine {
    /// The machine from the stencils compiled at `-C opt-level=opt`, if
    /// there are any.
    pub fn new(opt: &str) -> Option<StencilMachine> {
        let set = STENCIL_SETS.iter().find(|s| s.opt == opt)?;
        let find = |name: &str| {
            set.stencils.iter().find(|s| s.0 == name).unwrap_or_else(|| panic!("no stencil st_{name}")).1
        };
        let total: usize = set.stencils.iter().map(|s| s.1.len().next_multiple_of(16)).sum();
        let mut space = CodeSpace::new(total).expect("a code space");
        let mut place = |code: &[u8]| {
            let at = space.alloc(code.len(), 16).expect("room");
            space.write(at, code);
            space.flush(at, code.len());
            at
        };
        let start = place(find("start"));
        let mut offsets = Vec::new();
        for (name, _) in ROUTINES {
            offsets.push(place(find(&stencil_name(name))));
        }
        let mut routines = [0u64; ROUTINE_SLOTS];
        for (i, at) in offsets.iter().enumerate() {
            routines[i] = space.exec_addr(*at) as u64;
        }
        let code_bytes = space.used();
        Some(StencilMachine { space, start, routines, stacks: Stacks::new(), fuel_left: 0, code_bytes })
    }

    /// As [`NativeMachine::run`](crate::threaded::NativeMachine::run).
    pub fn run(&mut self, heap: &mut Heap, word: Value, args: &[Value], fuel: u64) -> Result<Vec<Value>, Trap> {
        let mut st = self.stacks.start(heap, word, args, fuel);
        st.routines = self.routines;
        let ip = st.base.wrapping_add(st.cur).wrapping_sub(4);
        let stp = &mut st as *mut State as u64;
        // SAFETY: `start` is a stencil with the eight-argument signature,
        // placed whole with no relocations to patch (the build script
        // checked); the argument registers are the machine's registers, set
        // as `State` would have them. The rest is as for `NativeMachine`.
        unsafe {
            self.space.call8(self.start, [st.base, ip, st.cur, st.dsp, st.rsp, stp, st.fuel, word.raw()]);
        }
        self.fuel_left = st.fuel;
        self.stacks.finish(&st)
    }
}
