//! The stencil machine: the cellular machine again, its routines written in
//! Rust (`stencils/cellular.rs`) with `become`, compiled by the build script
//! at several optimisation levels, and placed in a code space by copying.
//!
//! Beside the hand-encoded machine in `cellular.rs` it answers two
//! questions: whether Rust with guaranteed tail calls can express the inner
//! interpreter, and what that costs against code we encode ourselves. Both
//! run the same words on the same stacks and state, and are checked against
//! the Rust machine by the same tests.

use crate::codespace::{CodeSpace, Offset};
use crate::cellular::{ROUTINE_SLOTS, Stacks, State};
use fixpt_engine::cellular::Trap;
use fixpt_heap::layout::cellular::ROUTINES;
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

/// Run `word` with `args` on the stencil machine at `-O2`, in `rt`: for the
/// runtime's `%run-word` (`Runtime::run_word`).
pub fn run_word(rt: &mut fixpt_runtime::Runtime, word: Value, args: &[Value]) -> Result<Value, String> {
    let mut m = StencilMachine::new("2").ok_or("no stencils: this build had no nightly compiler")?;
    let out = m.run_in_runtime(rt, word, args, u64::MAX).map_err(|t| format!("{t:?}"))?;
    out.last().copied().ok_or_else(|| "the word left nothing".to_string())
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
        // `local!` and the like: a Rust identifier has no `!`.
        n => n.replace('!', "_set").replace('-', "_"),
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
        // A routine with no stencil of its own is run by the Rust machine
        // (`st_other`, the call-out's round trip).
        let find = |name: &str| {
            let other = set.stencils.iter().find(|s| s.0 == "other").expect("st_other").1;
            set.stencils.iter().find(|s| s.0 == name).map_or(other, |s| s.1)
        };
        // Room for each routine's copy (the call-out's, for one with none of
        // its own), and `start`'s.
        let total: usize = ROUTINES.iter().map(|(name, _)| find(&stencil_name(name)).len().next_multiple_of(16)).sum::<usize>()
            + find("start").len().next_multiple_of(16);
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

    /// As [`NativeMachine::run`](crate::cellular::NativeMachine::run).
    pub fn run(&mut self, heap: &mut Heap, word: Value, args: &[Value], fuel: u64) -> Result<Vec<Value>, Trap> {
        let st = self.stacks.start(heap, word, args, fuel);
        self.go(st, word)
    }

    /// As [`NativeMachine::run_in_runtime`](crate::cellular::NativeMachine::run_in_runtime).
    pub fn run_in_runtime(
        &mut self,
        rt: &mut fixpt_runtime::Runtime,
        word: Value,
        args: &[Value],
        fuel: u64,
    ) -> Result<Vec<Value>, Trap> {
        let rt_ptr = rt as *mut fixpt_runtime::Runtime as u64;
        let mut st = self.stacks.start(&mut rt.heap, word, args, fuel);
        st.rt = rt_ptr;
        self.go(st, word)
    }

    fn go(&mut self, mut st: State, word: Value) -> Result<Vec<Value>, Trap> {
        st.routines = self.routines;
        let ip = st.base.wrapping_add(st.cur).wrapping_sub(4);
        let stp = &mut st as *mut State as u64;
        // SAFETY: `start` is a stencil with the eight-argument signature,
        // placed whole with no relocations to patch (the build script
        // checked); the argument registers are the machine's registers, set
        // as `State` would have them. The rest is as for `NativeMachine`.
        unsafe {
            let fp = st.ds_base - 8 - st.fp;
            self.space.call8(self.start, [st.base, ip, st.cur, st.dsp, st.rsp, stp, fp, word.raw()]);
        }
        self.fuel_left = st.fuel;
        self.stacks.finish(&st)
    }
}

/// The stencils' Rust source, as built into this binary: what a stencil
/// machine runs, shown instead of machine code (`,disassemble-asm`), since
/// it compiles no word and runs each cell through a fixed set of routines.
const STENCIL_SOURCE: &str = include_str!("../stencils/cellular.rs");

/// From `from`, which is at an opening bracket, to just past the one that
/// closes it.
fn balanced(src: &str, from: usize) -> &str {
    let (open, close) = match src.as_bytes()[from] {
        b'(' => (b'(', b')'),
        _ => (b'{', b'}'),
    };
    let mut depth = 0;
    for (i, c) in src.bytes().enumerate().skip(from) {
        if c == open {
            depth += 1;
        } else if c == close {
            depth -= 1;
            if depth == 0 {
                return &src[from..=i];
            }
        }
    }
    &src[from..]
}

/// Stencil `st_name`'s definition, `routine!(st_name, …);`, if there is one.
fn routine_source(name: &str) -> Option<String> {
    let at = STENCIL_SOURCE.find(&format!("routine!(st_{name},"))?;
    let open = at + "routine!".len();
    Some(format!("routine!{};", balanced(STENCIL_SOURCE, open)))
}

/// The macros defined in the stencils' source that `text` uses, each's
/// definition.
fn macros_used(text: &str, shown: &mut Vec<String>) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = STENCIL_SOURCE;
    while let Some(at) = rest.find("macro_rules! ") {
        let name_at = at + "macro_rules! ".len();
        let name: String = rest[name_at..].chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
        let open = name_at + rest[name_at..].find('{').unwrap_or(0);
        let def = balanced(rest, open);
        if name != "routine" && text.contains(&format!("{name}!(")) && !shown.contains(&name) {
            shown.push(name.clone());
            let def = format!("macro_rules! {name} {def}");
            // And the macros it uses in turn.
            let inner = macros_used(&def, shown);
            out.push(def);
            out.extend(inner);
        }
        rest = &rest[open + def.len()..];
    }
    out
}

/// For word `word`, the Rust source of each stencil its cells run, once
/// each, and of the stencils' macros those use: what the stencil machine
/// does for this word.
pub fn stencil_source_text(heap: &Heap, word: Value) -> Option<String> {
    use fixpt_heap::layout::cellular::{WORD_CELL0, operands};
    if !heap.is_cellular_word(word) {
        return None;
    }
    let fields = heap.bloblet_head(word).fields;
    let mut routines: Vec<&str> = Vec::new();
    let mut k = WORD_CELL0;
    while k <= fields {
        let cell = heap.bloblet_slot(word, k);
        let name = if cell.is_fixnum() { ROUTINES.get(cell.as_fixnum() as usize).map_or("?", |r| r.0) } else { "docol" };
        if !routines.contains(&name) {
            routines.push(name);
        }
        k += 1 + if cell.is_fixnum() { operands(name) } else { 0 };
    }
    let mut out = String::from("the stencils its cells run, as Rust (crates/fixpt-native/stencils/cellular.rs):\n");
    let mut shown = Vec::new();
    for r in routines {
        let stencil = stencil_name(r);
        match routine_source(&stencil) {
            Some(src) => {
                out.push_str(&format!("\n// `{r}`\n{src}\n"));
                for m in macros_used(&src, &mut shown) {
                    out.push_str(&format!("{m}\n"));
                }
            }
            None => out.push_str(&format!("\n// `{r}`: no stencil of its own; run by the Rust machine, through `st_other`\n")),
        }
    }
    Some(out)
}
