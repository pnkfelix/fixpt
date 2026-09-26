// The machine's state while it is out of machine code, shared by offset with
// the generated code. Included, not a module: the stencils (compiled apart,
// `no_std`, by the build script) include this same file, so the hand-encoded
// machine and the stencil machine cannot disagree about it.

/// Room for this many routines in [`State::routines`].
pub const ROUTINE_SLOTS: usize = 32;

#[repr(C)]
#[derive(Default)]
pub struct State {
    pub base: u64,
    pub cur: u64,
    /// The ip, saved as `8k`: bytes before the current word's suffix.
    pub d: u64,
    pub dsp: u64,
    pub rsp: u64,
    pub table: u64,
    pub fal: u64,
    pub tru: u64,
    pub fuel: u64,
    pub status: u64,
    pub aux: u64,
    pub callout: u64,
    pub start: u64,
    pub heap: u64,
    pub ds_base: u64,
    pub rs_base: u64,
    pub ds_limit: u64,
    pub rs_limit: u64,
    /// The routines' addresses, by number, for machines that find them
    /// through the state rather than a register.
    pub routines: [u64; ROUTINE_SLOTS],
}
