//! Continuation marks, prompts and winders: the part of a continuation that is
//! not frames.
//!
//! Racket's design (Clements & Felleisen, TOPLAS 2004; Flatt & Dybvig, PLDI
//! 2020), specified for Scheme by SRFI 226. A *mark* is a key/value pair
//! attached to one continuation frame; `with-continuation-mark` in tail
//! position replaces the frame's mark for that key rather than adding one,
//! which is what keeps marks compatible with proper tail calls.
//!
//! Frames here hold no `Value`s, so marks cannot live in them. They live in a
//! separate stack beside the frames — Flatt & Dybvig's *attachments* — where
//! each entry records the continuation it belongs to as a frame **depth**: the
//! length of the frame stack whose top frame will receive the marked
//! expression's value. An entry is live exactly while that many frames are;
//! every engine trims the stack when it pops a frame.
//!
//! Each entry also records a stack **height**: where the value stack stood for
//! that continuation. Depth and height together are enough to *cut* the machine
//! back to an entry — which is how an abort reaches a prompt — and to relocate a
//! captured segment onto a different stack, which is how a composable
//! continuation is reinstated.
//!
//! Two other things are entries rather than marks, flagged by `kind`:
//!
//! * a **prompt** delimits a continuation: `key` is its tag, `val` its handler;
//! * a **winder** is one `dynamic-wind` extent: `val` is `(before . after)`.
//!
//! Keeping them in the same stack is what makes them part of the continuation:
//! captured with it, reinstated with it, and discarded with it when control
//! leaves. The last of those is the point — nothing about the dynamic
//! environment lives in a global that an abandoned computation can leave set.

use fixpt_heap::{Heap, ObjType, Value};

pub const KIND_MARK: u32 = 0;
pub const KIND_PROMPT: u32 = 1;
pub const KIND_WINDER: u32 = 2;

/// Where an entry belongs. No `Value`s, so it encodes to plain words.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Meta {
    pub depth: u32,
    pub height: u32,
    pub kind: u32,
}

/// The engine-side stack of marks, prompts and winders.
///
/// `vals` holds `key, val` pairs flattened, so it is one contiguous slice the
/// collector can trace as a root, exactly like the value stack.
#[derive(Default)]
pub struct Marks {
    pub meta: Vec<Meta>,
    pub vals: Vec<Value>,
}

impl Marks {
    pub fn clear(&mut self) {
        self.meta.clear();
        self.vals.clear();
    }

    pub fn len(&self) -> usize {
        self.meta.len()
    }

    pub fn is_empty(&self) -> bool {
        self.meta.is_empty()
    }

    pub fn key(&self, i: usize) -> Value {
        self.vals[2 * i]
    }

    pub fn val(&self, i: usize) -> Value {
        self.vals[2 * i + 1]
    }

    pub fn truncate(&mut self, n: usize) {
        self.meta.truncate(n);
        self.vals.truncate(2 * n);
    }

    fn push(&mut self, meta: Meta, key: Value, val: Value) {
        self.meta.push(meta);
        self.vals.push(key);
        self.vals.push(val);
    }

    /// Drop every entry whose continuation has returned.
    #[inline]
    pub fn trim(&mut self, frames: usize) {
        while let Some(m) = self.meta.last() {
            if m.depth as usize > frames {
                self.meta.pop();
                self.vals.truncate(self.vals.len() - 2);
            } else {
                break;
            }
        }
    }

    /// Attach a mark to the continuation at `depth`.
    ///
    /// If that continuation already has a mark for `key`, it is replaced: a
    /// `with-continuation-mark` in tail position is the *same* frame, and
    /// replacing is what makes a marked loop run in constant space. The search
    /// stops at a prompt or winder, since those begin a new extent even when
    /// they share the frame.
    pub fn set_mark(&mut self, depth: u32, height: u32, key: Value, val: Value) {
        for i in (0..self.len()).rev() {
            let m = self.meta[i];
            if m.depth != depth || m.kind != KIND_MARK {
                break;
            }
            if self.key(i) == key {
                self.vals[2 * i + 1] = val;
                return;
            }
        }
        self.push(Meta { depth, height, kind: KIND_MARK }, key, val);
    }

    pub fn push_prompt(&mut self, depth: u32, height: u32, tag: Value, handler: Value) {
        self.push(Meta { depth, height, kind: KIND_PROMPT }, tag, handler);
    }

    pub fn push_winder(&mut self, depth: u32, height: u32, winder: Value) {
        self.push(Meta { depth, height, kind: KIND_WINDER }, Value::FALSE, winder);
    }

    /// The innermost prompt with this tag.
    pub fn find_prompt(&self, tag: Value) -> Option<usize> {
        (0..self.len())
            .rev()
            .find(|&i| self.meta[i].kind == KIND_PROMPT && self.key(i) == tag)
    }

    /// The innermost winder above entry `floor`.
    pub fn innermost_winder_above(&self, floor: usize) -> Option<usize> {
        (floor + 1..self.len())
            .rev()
            .find(|&i| self.meta[i].kind == KIND_WINDER)
    }

    /// The index of the first entry visible from the top when marks are
    /// delimited by `tag` — just above that prompt, or the bottom when there is
    /// no such prompt or no tag was given.
    pub fn visible_from(&self, tag: Value) -> usize {
        if tag.is_false() {
            return 0;
        }
        self.find_prompt(tag).map_or(0, |i| i + 1)
    }

    /// Marks from `from` to the top as a list of `(key . val)`, innermost
    /// first. Prompts and winders are not marks and are not listed.
    pub fn mark_list(&self, heap: &mut Heap, from: usize) -> Value {
        let mut list = Value::NULL;
        for i in from..self.len() {
            if self.meta[i].kind == KIND_MARK {
                let pair = heap.cons(self.key(i), self.val(i));
                list = heap.cons(pair, list);
            }
        }
        list
    }

    /// The first value for `key` from the top down to `from`.
    pub fn first(&self, from: usize, key: Value) -> Option<Value> {
        (from..self.len())
            .rev()
            .find(|&i| self.meta[i].kind == KIND_MARK && self.key(i) == key)
            .map(|i| self.val(i))
    }

    /// Every winder, innermost first, as a list of `(before . after)`.
    pub fn winder_list(&self, heap: &mut Heap) -> Value {
        let mut list = Value::NULL;
        for i in 0..self.len() {
            if self.meta[i].kind == KIND_WINDER {
                list = heap.cons(self.val(i), list);
            }
        }
        list
    }

    // ------------------------------------------------------------ capture
    /// Encode entries `from..` for a continuation object, rebasing depth and
    /// height by the given amounts. A full continuation passes zeros; a
    /// composable one passes its prompt's position, so the segment is stored
    /// relative to its own bottom and can be reinstated anywhere.
    pub fn encode(&self, heap: &mut Heap, from: usize, depth0: u32, height0: u32) -> (Value, Value) {
        let vals = heap.vector_from(&self.vals[2 * from..]);
        let mut bytes = Vec::with_capacity((self.len() - from) * 12);
        for m in &self.meta[from..] {
            for w in [m.depth - depth0, m.height - height0, m.kind] {
                bytes.extend_from_slice(&w.to_le_bytes());
            }
        }
        (vals, heap.make_bytevector(&bytes))
    }

    /// Append encoded entries, rebasing them onto `depth0` / `height0`.
    pub fn append_encoded(&mut self, heap: &Heap, vals: Value, meta: Value, depth0: u32, height0: u32) {
        for (i, m) in decode_meta(heap, meta).into_iter().enumerate() {
            self.push(
                Meta {
                    depth: m.depth + depth0,
                    height: m.height + height0,
                    kind: m.kind,
                },
                heap.obj_ref(vals, 2 * i),
                heap.obj_ref(vals, 2 * i + 1),
            );
        }
    }
}

pub fn decode_meta(heap: &Heap, meta: Value) -> Vec<Meta> {
    heap.bytevector_to_vec(meta)
        .chunks_exact(12)
        .map(|c| {
            let w = |i: usize| u32::from_le_bytes(c[4 * i..4 * i + 4].try_into().expect("4 bytes"));
            Meta { depth: w(0), height: w(1), kind: w(2) }
        })
        .collect()
}

// ------------------------------------------------ continuation objects
//
// `[stack, frames, mark-vals, mark-meta, flags]`. `stack` and `frames` are the
// engine's own encoding; the marks are this module's, and are the same for
// both engines, which is what lets `continuation-marks` be a plain primitive.

pub const K_STACK: usize = 0;
pub const K_FRAMES: usize = 1;
pub const K_MARK_VALS: usize = 2;
pub const K_MARK_META: usize = 3;
pub const K_FLAGS: usize = 4;
pub const K_FIELDS: usize = 5;

/// A composable continuation is a segment, stored relative to its own bottom
/// and reinstated *on top of* the current continuation. A full one replaces it.
pub const K_COMPOSABLE: i64 = 1;

pub fn make_continuation(
    heap: &mut Heap,
    stack: Value,
    frames: Value,
    marks: (Value, Value),
    composable: bool,
) -> Value {
    let k = heap.alloc(ObjType::Continuation, K_FIELDS, Value::UNSPECIFIED);
    heap.obj_set(k, K_STACK, stack);
    heap.obj_set(k, K_FRAMES, frames);
    heap.obj_set(k, K_MARK_VALS, marks.0);
    heap.obj_set(k, K_MARK_META, marks.1);
    heap.obj_set(k, K_FLAGS, Value::fixnum(if composable { K_COMPOSABLE } else { 0 }));
    k
}

pub fn is_composable(heap: &Heap, k: Value) -> bool {
    heap.obj_ref(k, K_FLAGS).as_fixnum() & K_COMPOSABLE != 0
}

/// A captured continuation's marks, innermost first, delimited by `tag`.
pub fn continuation_mark_list(heap: &mut Heap, k: Value, tag: Value) -> Value {
    let marks = continuation_entries(heap, k);
    let from = marks.visible_from(tag);
    marks.mark_list(heap, from)
}

/// A captured continuation's winders, innermost first.
pub fn continuation_winder_list(heap: &mut Heap, k: Value) -> Value {
    let marks = continuation_entries(heap, k);
    marks.winder_list(heap)
}

fn continuation_entries(heap: &Heap, k: Value) -> Marks {
    let mut marks = Marks::default();
    let vals = heap.obj_ref(k, K_MARK_VALS);
    let meta = heap.obj_ref(k, K_MARK_META);
    marks.append_encoded(heap, vals, meta, 0, 0);
    marks
}

/// What a `,help` hole hands the top level: `#(tag k report position total)`.
///
/// Recognised by its first element, the top level's own prompt tag, which no
/// ordinary value carries. `k` is the composable continuation of the hole —
/// the rest of the form — so the top level can resume it with a value.
pub fn make_hole(heap: &mut Heap, tag: Value, k: Value, report: &str, position: Value, total: Value) -> Value {
    let text = heap.make_string(report);
    heap.vector_from(&[tag, k, text, position, total])
}
