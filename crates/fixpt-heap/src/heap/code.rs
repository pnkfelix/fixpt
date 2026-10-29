//! The code area (`docs/object-model.md`, "A collected code area"):
//! bloblets that never move, past the regions' areas, for code, which is
//! pointed into by raw addresses and so must stay where it is put. The
//! collector traces them as it meets them, marking instead of copying, and
//! sweeps the rest into a free list after, so code no longer reachable is
//! reclaimed.
//!
//! Two parts (`docs/research/code-stubs.md`): the lower holds what native
//! code calls that is not native code, each bloblet's suffix a stub that
//! enters the `foreign` routine (cellular words, and the stub the other
//! kinds of procedure share); the upper, from `code-lo`, holds native code.
//! So every procedure's code runs, and one comparison with `code-lo` still
//! tells native code from the rest.
//!
//! Each part is always walkable from its start, header to header: a free
//! block is written as a raw bloblet whose suffix covers it. Allocation is
//! first fit from the part's free list, else from the end of what has been
//! walked.

use super::{CODE_BASE, CODE_WORDS, Heap, find_main, read_head};
use crate::layout;
use crate::value::{TAG_MASK, TAG_TRAILER, Value, is_extension, is_header, make_header};
use std::collections::HashSet;

/// The code area's parts: what native code calls through a stub, and
/// native code.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CodePart {
    Stubbed = 0,
    Native = 1,
}

/// Where the native part starts: half way.
pub(super) const NATIVE_BASE: usize = CODE_BASE + CODE_WORDS / 2;

/// One part of the area.
pub(super) struct Part {
    /// Where it starts.
    pub(super) base: usize,
    /// Where its walkable part ends: every word from `base` up to here is
    /// part of an object or of a free block.
    pub(super) top: usize,
    /// Free blocks, `(start, words)`, in address order.
    pub(super) free: Vec<(usize, usize)>,
    /// Where each object starts, in address order: so that a minor
    /// collection finds the objects on a dirty card without walking it.
    pub(super) starts: Vec<usize>,
    /// Words in objects: all that is not free.
    pub(super) used: usize,
}

impl Part {
    fn new(base: usize) -> Part {
        Part { base, top: base, free: Vec::new(), starts: Vec::new(), used: 0 }
    }

    pub(super) fn limit(&self) -> usize {
        self.base + CODE_WORDS / 2
    }
}

pub(super) struct CodeArea {
    pub(super) parts: [Part; 2],
    /// Whether anything was ever allocated: the execute view is made then.
    pub(super) started: bool,
    /// Words allocated since the last collection, which counts toward the
    /// next as a semispace's allocation does.
    pub(super) taken: usize,
    /// Words allocated since the heap was made.
    pub(super) allocated: u64,
    /// The stub every procedure that is no word shares, once made
    /// (`Heap::foreign_stub`); `#f` before.
    pub(super) stub: Value,
}

impl Default for CodeArea {
    fn default() -> CodeArea {
        CodeArea { parts: [Part::new(CODE_BASE), Part::new(NATIVE_BASE)], started: false, taken: 0, allocated: 0, stub: Value::FALSE }
    }
}

impl CodeArea {
    /// Words in objects, both parts.
    pub(super) fn used(&self) -> usize {
        self.parts.iter().map(|p| p.used).sum()
    }
}

/// Whether word `i` of the heap's memory is in the code area.
#[inline(always)]
pub(super) fn in_code_area(i: usize) -> bool {
    (CODE_BASE..CODE_BASE + CODE_WORDS).contains(&i)
}

/// A free block of `len` words at `at`: a raw bloblet, all suffix.
fn put_free(mem: &mut [u64], at: usize, len: usize) {
    mem[at] = make_header(const { layout::kind("bloblet") }, 0, (len - 1) * 8);
}

impl Heap {
    /// A bloblet in the code area's native part, as
    /// [`make_bloblet`](Heap::make_bloblet) makes one in the heap: fields
    /// zero, suffix zero. It never moves, and lives while something the
    /// collector traces refers to it. Only ordinary headers.
    pub fn make_code_bloblet(&mut self, kind: u8, fields: usize, bytes: usize, trailer: bool) -> Value {
        self.make_code_bloblet_in(CodePart::Native, kind, fields, bytes, trailer)
    }

    /// The same, in `part`.
    pub fn make_code_bloblet_in(&mut self, part: CodePart, kind: u8, fields: usize, bytes: usize, trailer: bool) -> Value {
        let total = fields + trailer as usize;
        assert!(total as u64 <= layout::H_FIELDS.max(), "a code bloblet has an ordinary header");
        assert!(bytes as u64 <= layout::H_BYTES.max(), "a bloblet's suffix is limited to 4 GiB");
        let size = 1 + total + bytes.div_ceil(8);
        let at = self.code_alloc(part, size);
        self.set_word(at, make_header(kind, total, bytes));
        for i in 1..size {
            self.set_word(at + i, 0);
        }
        if trailer {
            self.set_word(at + total, Self::trailer_word(total));
        }
        self.blob_v(at + 1 + total)
    }

    /// A bloblet in the code area's stubbed part, whose suffix is the stub
    /// that enters `foreign` (`layout::stub`), frozen and runnable: what
    /// native code calls that is not native code. Fields zero.
    pub fn make_stubbed_bloblet(&mut self, kind: u8, fields: usize, trailer: bool) -> Value {
        let stub = layout::stub::BYTES;
        let v = self.make_code_bloblet_in(CodePart::Stubbed, kind, fields, stub.len(), trailer);
        for (i, w) in stub.chunks(8).enumerate() {
            let mut b = [0u8; 8];
            b[..w.len()].copy_from_slice(w);
            self.set_word(self.ix(v) + i, u64::from_le_bytes(b));
        }
        self.freeze_bloblet(v, false, true);
        if self.code_exec.is_ok() {
            self.flush_code(v);
        }
        v
    }

    /// The stub the procedures that are not words share (`docs/research/
    /// code-stubs.md`): a plain bloblet of no fields in the stubbed part,
    /// made once, which a VM closure, primitive or continuation, and a
    /// cellular continuation, holds as its field 2. It lives as the heap
    /// does.
    pub fn foreign_stub(&mut self) -> Value {
        if self.code.stub == Value::FALSE {
            let s = self.make_stubbed_bloblet(const { layout::kind("bloblet") }, 0, false);
            let sym = self.intern("%fx26-foreign-stub");
            let slot = self.symbol_global_slot(sym);
            self.globals[slot] = s;
            self.code.stub = s;
        }
        self.code.stub
    }

    /// A copy of bloblet `v` in the code area, sealed (`TODO.md` §97): its
    /// kind, fields, trailer and suffix as `v`'s, the suffix frozen and
    /// flushed, so that it is machine code that may run at
    /// [`code_exec_address`](Heap::code_exec_address). Its fields stay as
    /// `v`'s are, frozen or not. Only ordinary headers.
    pub fn seal_code_copy(&mut self, v: Value) -> Value {
        let head = self.bloblet_head(v);
        let trailer = head.fields > 0 && self.word(self.ix(v) - 1) & TAG_MASK == TAG_TRAILER;
        let fields = head.fields - trailer as usize;
        let c = self.make_code_bloblet(head.kind, fields, head.bytes, trailer);
        for k in 1 + trailer as usize..=head.fields {
            let x = self.bloblet_slot(v, k);
            self.set_bloblet_slot(c, k, x);
        }
        for i in 0..head.bytes.div_ceil(8) {
            let w = self.word(self.ix(v) + i);
            self.set_word(self.ix(c) + i, w);
        }
        self.freeze_bloblet(c, head.fields_frozen, true);
        self.flush_code(c);
        c
    }

    /// Before anything is written there: the view replaces the area's pages
    /// with shared ones, zero, as they were.
    pub(super) fn start_code_area(&mut self) {
        if !self.code.started {
            self.code.started = true;
            self.code_exec = self.mem.exec_view(CODE_BASE..CODE_BASE + CODE_WORDS).map_err(|e| e.to_string());
        }
    }

    /// `n` words of the code area's `part`: first fit, else past what is
    /// walkable.
    fn code_alloc(&mut self, part: CodePart, n: usize) -> usize {
        self.start_code_area();
        self.code.taken += n;
        self.code.allocated += n as u64;
        let p = &mut self.code.parts[part as usize];
        p.used += n;
        if let Some(k) = p.free.iter().position(|&(_, len)| len >= n) {
            let (start, len) = p.free[k];
            if len > n {
                put_free(self.mem.words_mut(), start + n, len - n);
                p.free[k] = (start + n, len - n);
            } else {
                p.free.remove(k);
            }
            let k = p.starts.partition_point(|&s| s < start);
            p.starts.insert(k, start);
            return start;
        }
        let at = p.top;
        assert!(at + n <= p.limit(), "the code area is full: {n} words more, past {} in use", p.used - n);
        p.top = at + n;
        p.starts.push(at);
        at
    }

    /// Where a code bloblet's suffix, its code, runs from: its address in
    /// the code area's read+execute view. Its fields are at the same
    /// distances before it there, so its code reaches them PC-relatively.
    pub fn code_exec_address(&self, v: Value) -> usize {
        assert!(self.is_code_bloblet(v), "{v:?} is not in the code area");
        let view = self.code_exec.as_ref().unwrap_or_else(|e| panic!("the code area has no execute view: {e}"));
        view.exec_address(v.index() * 8)
    }

    /// After a code bloblet's suffix is written with instructions: make them
    /// runnable at [`code_exec_address`](Heap::code_exec_address). Writing
    /// its fields needs none of this.
    pub fn flush_code(&self, v: Value) {
        assert!(self.is_code_bloblet(v), "{v:?} is not in the code area");
        let bytes = self.bloblet_head(v).bytes;
        let view = self.code_exec.as_ref().unwrap_or_else(|e| panic!("the code area has no execute view: {e}"));
        view.flush(v.index() * 8, bytes.max(1));
    }

    /// The address of the code area's native part: every reference to
    /// native code is at or above this, and every other reference below
    /// (a stubbed bloblet's too), so machine code tells native code from
    /// the rest with one comparison (the state's `code-lo`).
    pub fn native_code_address(&self) -> usize {
        self.words_address() as usize + 8 * NATIVE_BASE
    }

    /// Whether `v` refers into the code area.
    pub fn is_code_bloblet(&self, v: Value) -> bool {
        v.is_bloblet() && in_code_area(self.ix(v))
    }

    /// Which part of the code area `v` is in, if it is in it.
    pub fn code_part(&self, v: Value) -> Option<CodePart> {
        self.is_code_bloblet(v).then(|| if self.ix(v) >= NATIVE_BASE { CodePart::Native } else { CodePart::Stubbed })
    }

    /// Words in the objects of the code area's native part, and words its
    /// walkable part spans (objects and free blocks): for reports and tests.
    pub fn code_words(&self) -> (usize, usize) {
        self.code_words_in(CodePart::Native)
    }

    /// The same, of `part`.
    pub fn code_words_in(&self, part: CodePart) -> (usize, usize) {
        let p = &self.code.parts[part as usize];
        (p.used, p.top - p.base)
    }

    /// After a collection: every object not in `marks` (by main header) is
    /// freed, adjacent free space coalesced, and free space at the end
    /// given back to the walkable part's end. Pages wholly inside a free
    /// block are given back to the system.
    pub(super) fn sweep_code(&mut self, marks: &HashSet<usize>) {
        // Never used: nothing to sweep, and nothing to start (the first use
        // makes the area's execute view, before anything is in it).
        if !self.code.started {
            return;
        }
        for part in 0..2 {
            let (base, top) = (self.code.parts[part].base, self.code.parts[part].top);
            let (mut at, mut free, mut starts, mut used, mut run) = (base, Vec::new(), Vec::new(), 0, None);
            while at < top {
                let w = self.word(at);
                debug_assert!(is_header(w), "the code area is walkable: no header at {at}");
                let main = at + is_extension(w) as usize;
                let size = read_head(self.mem.words(), main).size();
                if marks.contains(&main) {
                    if let Some(start) = run.take() {
                        free.push((start, at - start));
                    }
                    starts.push(at);
                    used += size;
                } else if run.is_none() {
                    run = Some(at);
                }
                at += size;
            }
            for &(start, len) in &free {
                put_free(self.mem.words_mut(), start, len);
                self.mem.release(start + 1..start + len);
            }
            if let Some(start) = run {
                self.mem.release(start..top);
            }
            let p = &mut self.code.parts[part];
            p.top = run.unwrap_or(top);
            (p.free, p.starts, p.used) = (free, starts, used);
        }
        self.code.taken = 0;
    }

    /// Each part's words, from its start to its walkable end, and its free
    /// blocks: what an image carries of the code area.
    pub(super) fn code_image(&self) -> [(Vec<u64>, Vec<(usize, usize)>); 2] {
        self.code.parts.each_ref().map(|p| (self.mem.words()[p.base..p.top].to_vec(), p.free.iter().map(|&(s, n)| (s - p.base, n)).collect()))
    }

    /// The code area as an image carries it (`code_image`), its references
    /// relocated already, its free blocks in order and within it: put back,
    /// the objects' starts found by walking it, and made runnable.
    pub(super) fn code_from_image(&mut self, parts: [(Vec<u64>, Vec<(usize, usize)>); 2]) -> Result<(), String> {
        if parts.iter().all(|(w, _)| w.is_empty()) {
            return Ok(());
        }
        self.start_code_area();
        for (k, (words, free)) in parts.into_iter().enumerate() {
            let base = self.code.parts[k].base;
            self.mem.words_mut()[base..base + words.len()].copy_from_slice(&words);
            let free: Vec<(usize, usize)> = free.into_iter().map(|(s, n)| (base + s, n)).collect();
            let (mut at, mut starts, mut f) = (base, Vec::new(), free.iter().peekable());
            while at < base + words.len() {
                if f.peek().is_some_and(|&&(s, _)| s == at) {
                    at += f.next().expect("peeked").1;
                    continue;
                }
                let end = base + words.len();
                let w = self.word(at);
                if !is_header(w) || (is_extension(w) && (at + 1 >= end || !is_header(self.word(at + 1)))) {
                    return Err(format!("no header at word {} of the code area's part {k}", at - base));
                }
                let main = at + is_extension(w) as usize;
                starts.push(at);
                at += read_head(self.mem.words(), main).size();
                if at > end || f.peek().is_some_and(|&&(s, _)| s < at) {
                    return Err(format!("an object past its place in the code area's part {k}"));
                }
            }
            let p = &mut self.code.parts[k];
            p.used = words.len() - free.iter().map(|&(_, n)| n).sum::<usize>();
            (p.top, p.free, p.starts) = (base + words.len(), free, starts);
        }
        if let Ok(view) = &self.code_exec {
            for p in &self.code.parts {
                if p.top > p.base {
                    view.flush((self.base + p.base) * 8, (p.top - p.base) * 8);
                }
            }
        }
        // The shared stub, if the image has it, found again by its global.
        let sym = self.intern("%fx26-foreign-stub");
        let slot = self.symbol_global_slot(sym);
        if self.is_code_bloblet(self.globals[slot]) {
            self.code.stub = self.globals[slot];
        }
        Ok(())
    }
}

/// In the collector: `v`, a reference into the code area, marks its
/// bloblet, queuing it to be scanned the first time. It stays where it is.
#[inline]
pub(super) fn mark_code(mem: &[u64], i: usize, marks: &mut HashSet<usize>, gray: &mut Vec<usize>) {
    if let Ok(main) = find_main(mem, i)
        && marks.insert(main)
    {
        gray.push(main);
    }
}
