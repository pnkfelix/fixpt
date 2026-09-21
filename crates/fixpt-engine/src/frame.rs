//! Control-stack frames.
//!
//! Frames hold **no `Value`s** — only node indices, counters and stack offsets.
//! Every live heap reference lives on the machine's value stack or in its
//! registers, so the collector's root set is two contiguous slices rather than
//! a walk over a `Vec` of enums. It is also what makes a captured continuation
//! serialisable: a frame is four machine words, so the whole control stack
//! encodes into a bytevector and travels in the heap like any other object.
//!
//! Frame convention: `env_slot` is where the frame saved the current
//! environment on the value stack. Anything else the frame needs sits at
//! `env_slot + 1`, `env_slot + 2`, … and collected values start after that.

use fixpt_core::ir::NodeId;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Frame {
    /// The value in the accumulator is the answer.
    Halt,
    /// `acc` is the test of an `if`.
    Branch { then: NodeId, els: NodeId, env_slot: u32 },
    /// `acc` is the value of element `index - 1` of a `begin`.
    SeqNext { seq: NodeId, index: u32, env_slot: u32 },
    /// `acc` is the operator (when `collected == 0`) or an operand.
    AppArg { app: NodeId, collected: u32, env_slot: u32 },
    /// `acc` is the value of initialiser `collected` of a `let`.
    LetInit { let_: NodeId, collected: u32, env_slot: u32 },
    /// `acc` is the value of initialiser `index` of a `letrec*`. Here
    /// `env_slot` holds the *new* environment, since `letrec*` initialisers run
    /// inside the scope they define.
    FixInit { fix: NodeId, index: u32, env_slot: u32 },
    /// `acc` is the value to assign.
    AssignLocal { node: NodeId, env_slot: u32 },
    AssignGlobal { slot: u32, env_slot: u32 },
    /// `acc` is the producer's result in `call-with-values`; the consumer is at
    /// `env_slot + 1`.
    Consume { env_slot: u32 },
}

const TAG_HALT: u64 = 0;
const TAG_BRANCH: u64 = 1;
const TAG_SEQ: u64 = 2;
const TAG_APP: u64 = 3;
const TAG_LET: u64 = 4;
const TAG_FIX: u64 = 5;
const TAG_ASSIGN_LOCAL: u64 = 6;
const TAG_ASSIGN_GLOBAL: u64 = 7;
const TAG_CONSUME: u64 = 8;

/// Words per encoded frame.
pub const FRAME_WORDS: usize = 4;

impl Frame {
    pub fn encode(self) -> [u64; FRAME_WORDS] {
        match self {
            Frame::Halt => [TAG_HALT, 0, 0, 0],
            Frame::Branch { then, els, env_slot } => {
                [TAG_BRANCH, then.0 as u64, els.0 as u64, env_slot as u64]
            }
            Frame::SeqNext { seq, index, env_slot } => {
                [TAG_SEQ, seq.0 as u64, index as u64, env_slot as u64]
            }
            Frame::AppArg { app, collected, env_slot } => {
                [TAG_APP, app.0 as u64, collected as u64, env_slot as u64]
            }
            Frame::LetInit { let_, collected, env_slot } => {
                [TAG_LET, let_.0 as u64, collected as u64, env_slot as u64]
            }
            Frame::FixInit { fix, index, env_slot } => {
                [TAG_FIX, fix.0 as u64, index as u64, env_slot as u64]
            }
            Frame::AssignLocal { node, env_slot } => {
                [TAG_ASSIGN_LOCAL, node.0 as u64, 0, env_slot as u64]
            }
            Frame::AssignGlobal { slot, env_slot } => {
                [TAG_ASSIGN_GLOBAL, slot as u64, 0, env_slot as u64]
            }
            Frame::Consume { env_slot } => [TAG_CONSUME, 0, 0, env_slot as u64],
        }
    }

    pub fn decode(w: [u64; FRAME_WORDS]) -> Option<Frame> {
        let a = w[1] as u32;
        let b = w[2] as u32;
        let e = w[3] as u32;
        Some(match w[0] {
            TAG_HALT => Frame::Halt,
            TAG_BRANCH => Frame::Branch { then: NodeId(a), els: NodeId(b), env_slot: e },
            TAG_SEQ => Frame::SeqNext { seq: NodeId(a), index: b, env_slot: e },
            TAG_APP => Frame::AppArg { app: NodeId(a), collected: b, env_slot: e },
            TAG_LET => Frame::LetInit { let_: NodeId(a), collected: b, env_slot: e },
            TAG_FIX => Frame::FixInit { fix: NodeId(a), index: b, env_slot: e },
            TAG_ASSIGN_LOCAL => Frame::AssignLocal { node: NodeId(a), env_slot: e },
            TAG_ASSIGN_GLOBAL => Frame::AssignGlobal { slot: a, env_slot: e },
            TAG_CONSUME => Frame::Consume { env_slot: e },
            _ => return None,
        })
    }

    /// Where this frame saved the environment, for restoring on resume.
    pub fn env_slot(self) -> Option<u32> {
        Some(match self {
            Frame::Halt => return None,
            Frame::Branch { env_slot, .. }
            | Frame::SeqNext { env_slot, .. }
            | Frame::AppArg { env_slot, .. }
            | Frame::LetInit { env_slot, .. }
            | Frame::FixInit { env_slot, .. }
            | Frame::AssignLocal { env_slot, .. }
            | Frame::AssignGlobal { env_slot, .. }
            | Frame::Consume { env_slot } => env_slot,
        })
    }
}
