// The machine's state while it is out of machine code, shared by offset with
// the generated code. Included, not a module: the stencils (compiled apart,
// `no_std`, by the build script) include this same file, so the hand-encoded
// machine and the stencil machine cannot disagree about it.

/// Room for this many routines in [`State::routines`].
pub const ROUTINE_SLOTS: usize = 64;

#[repr(C)]
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
    /// The frame pointer, saved as `ds_base - 8 - fp`: the bits of the
    /// fixnum index of the frame's slot 0 (`fixpt_engine::threaded`).
    pub fp: u64,
    /// The closure running (a Value), or `#f`.
    pub clo: u64,
    /// The runtime (`*mut fixpt_runtime::Runtime`), or 0 when the machine
    /// runs on a bare heap, in which case the routines it has no machine
    /// code for cannot call the runtime's primitives.
    pub rt: u64,
    /// For each entry number, a word's table of where its machine code
    /// resumes at each cell, by `8k`, or 0 (`NativeMachine::compile_word`).
    pub resume: u64,
    /// Where the heap's `top` is, in words from the base, and how far
    /// machine code may take it before calling in to allocate
    /// (`Heap::top_address`, `Heap::inline_limit`).
    pub top: u64,
    pub alloc_limit: u64,
    /// The routines' addresses, by number, for machines that find them
    /// through the state rather than a register.
    pub routines: [u64; ROUTINE_SLOTS],
}
