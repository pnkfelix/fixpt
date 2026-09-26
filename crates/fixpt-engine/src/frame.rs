//! Control-stack frames.
//!
//! Frames hold **no `Value`s** — only node offsets, counters and stack slots.
//! With the Core IR in the heap that invariant takes a little more care than it
//! used to: a node is reached through the *current `Code` object*, which is a
//! heap reference and does move. So a frame stores the node's offset within its
//! code, and the code itself is saved on the value stack, which is traced like
//! everything else there.
//!
//! The payoff is unchanged and worth the care: the collector's root set stays
//! two contiguous slices, and a captured continuation encodes to plain words.
//!
//! Frame convention: `saved` is a slot pair on the value stack holding the
//! environment at `saved` and the code object at `saved + 1`. Collected values
//! start at `saved + 2`.

/// Slots each frame saves on the value stack: the environment and the code.
pub const SAVED_SLOTS: usize = 2;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Frame {
    /// The value in the accumulator is the answer.
    Halt,
    /// `acc` is the test of an `if`.
    Branch { then: u32, els: u32, saved: u32 },
    /// `acc` is the value of element `index - 1` of a `begin`.
    SeqNext { seq: u32, index: u32, saved: u32 },
    /// `acc` is the operator (when `collected == 0`) or an operand.
    AppArg { app: u32, collected: u32, saved: u32 },
    /// `acc` is the value of initialiser `collected` of a `let`.
    LetInit { let_: u32, collected: u32, saved: u32 },
    /// `acc` is the value of initialiser `index` of a `letrec*`. Here `saved`
    /// holds the *new* environment, since `letrec*` initialisers run inside the
    /// scope they define.
    FixInit { fix: u32, index: u32, saved: u32 },
    /// `acc` is the value to assign.
    AssignLocal { node: u32, saved: u32 },
    AssignGlobal { slot: u32, saved: u32 },
    /// `acc` is the producer's result in `call-with-values`; the consumer is at
    /// `saved + 2`.
    Consume { saved: u32 },
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
            Frame::Branch { then, els, saved } => {
                [TAG_BRANCH, then as u64, els as u64, saved as u64]
            }
            Frame::SeqNext { seq, index, saved } => {
                [TAG_SEQ, seq as u64, index as u64, saved as u64]
            }
            Frame::AppArg { app, collected, saved } => {
                [TAG_APP, app as u64, collected as u64, saved as u64]
            }
            Frame::LetInit { let_, collected, saved } => {
                [TAG_LET, let_ as u64, collected as u64, saved as u64]
            }
            Frame::FixInit { fix, index, saved } => {
                [TAG_FIX, fix as u64, index as u64, saved as u64]
            }
            Frame::AssignLocal { node, saved } => {
                [TAG_ASSIGN_LOCAL, node as u64, 0, saved as u64]
            }
            Frame::AssignGlobal { slot, saved } => {
                [TAG_ASSIGN_GLOBAL, slot as u64, 0, saved as u64]
            }
            Frame::Consume { saved } => [TAG_CONSUME, 0, 0, saved as u64],
        }
    }

    /// The same frame with its stack position moved from a segment based at
    /// `from` to one based at `to`. A composable continuation is stored
    /// relative to its own bottom (`from` = its prompt's height, `to` = 0) and
    /// reinstated wherever it is called (`from` = 0, `to` = the call's height).
    /// Every frame but `Halt` keeps that position in the last word.
    pub fn rebase(self, from: u32, to: u32) -> Frame {
        if matches!(self, Frame::Halt) {
            return self;
        }
        let mut w = self.encode();
        w[3] = w[3] - from as u64 + to as u64;
        Frame::decode(w).expect("rebasing keeps the tag")
    }

    pub fn decode(w: [u64; FRAME_WORDS]) -> Option<Frame> {
        let a = w[1] as u32;
        let b = w[2] as u32;
        let s = w[3] as u32;
        Some(match w[0] {
            TAG_HALT => Frame::Halt,
            TAG_BRANCH => Frame::Branch { then: a, els: b, saved: s },
            TAG_SEQ => Frame::SeqNext { seq: a, index: b, saved: s },
            TAG_APP => Frame::AppArg { app: a, collected: b, saved: s },
            TAG_LET => Frame::LetInit { let_: a, collected: b, saved: s },
            TAG_FIX => Frame::FixInit { fix: a, index: b, saved: s },
            TAG_ASSIGN_LOCAL => Frame::AssignLocal { node: a, saved: s },
            TAG_ASSIGN_GLOBAL => Frame::AssignGlobal { slot: a, saved: s },
            TAG_CONSUME => Frame::Consume { saved: s },
            _ => return None,
        })
    }

    /// Where this frame saved the environment and code, for restoring on
    /// resume.
    pub fn saved(self) -> Option<u32> {
        Some(match self {
            Frame::Halt => return None,
            Frame::Branch { saved, .. }
            | Frame::SeqNext { saved, .. }
            | Frame::AppArg { saved, .. }
            | Frame::LetInit { saved, .. }
            | Frame::FixInit { saved, .. }
            | Frame::AssignLocal { saved, .. }
            | Frame::AssignGlobal { saved, .. }
            | Frame::Consume { saved } => saved,
        })
    }
}
