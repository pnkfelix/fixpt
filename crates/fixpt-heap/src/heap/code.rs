//! The code area (`docs/object-model.md`, "A collected code area"):
//! bloblets that never move, past the regions' areas, for code, which is
//! pointed into by raw addresses and so must stay where it is put. The
//! collector traces them as it meets them, marking instead of copying, and
//! sweeps the rest into a free list after, so code no longer reachable is
//! reclaimed.
//!
//! The area is always walkable from its start, header to header: a free
//! block is written as a raw bloblet whose suffix covers it. Allocation is
//! first fit from the free list, else from the end of what has been walked.

use super::{CODE_BASE, CODE_WORDS, Heap, find_main, read_head};
use crate::layout;
use crate::value::{Value, is_extension, is_header, make_header};
use std::collections::HashSet;

#[derive(Default)]
pub(super) struct CodeArea {
    /// Where the walkable part ends: every word from `CODE_BASE` up to here
    /// is part of an object or of a free block.
    pub(super) top: usize,
    /// Free blocks, `(start, words)`, in address order.
    pub(super) free: Vec<(usize, usize)>,
    /// Words in objects: all that is not free.
    pub(super) used: usize,
    /// Words allocated since the last collection, which counts toward the
    /// next as a semispace's allocation does.
    pub(super) taken: usize,
}

/// Whether word `i` of the heap's memory is in the code area.
#[inline(always)]
pub(super) fn in_code_area(i: usize) -> bool {
    (CODE_BASE..CODE_BASE + CODE_WORDS).contains(&i)
}

/// A free block of `len` words at `at`: a raw bloblet, all suffix.
fn put_free(mem: &mut [u64], at: usize, len: usize) {
    mem[at] = make_header(layout::kind("bloblet"), 0, (len - 1) * 8);
}

impl Heap {
    /// A bloblet in the code area, as [`make_bloblet`](Heap::make_bloblet)
    /// makes one in the heap: fields zero, suffix zero. It never moves, and
    /// lives while something the collector traces refers to it. Only
    /// ordinary headers.
    pub fn make_code_bloblet(&mut self, kind: u8, fields: usize, bytes: usize, trailer: bool) -> Value {
        let total = fields + trailer as usize;
        assert!(total as u64 <= layout::H_FIELDS.max(), "a code bloblet has an ordinary header");
        assert!(bytes as u64 <= layout::H_BYTES.max(), "a bloblet's suffix is limited to 4 GiB");
        let size = 1 + total + bytes.div_ceil(8);
        let at = self.code_alloc(size);
        self.set_word(at, make_header(kind, total, bytes));
        for i in 1..size {
            self.set_word(at + i, 0);
        }
        if trailer {
            self.set_word(at + total, Self::trailer_word(total));
        }
        self.blob_v(at + 1 + total)
    }

    /// `n` words of the code area: first fit, else past what is walkable.
    fn code_alloc(&mut self, n: usize) -> usize {
        if self.code.top == 0 {
            self.code.top = CODE_BASE;
            // Before anything is written there: the view replaces the
            // area's pages with shared ones, zero, as they were.
            self.code_exec = self.mem.exec_view(CODE_BASE..CODE_BASE + CODE_WORDS).ok();
        }
        self.code.used += n;
        self.code.taken += n;
        if let Some(k) = self.code.free.iter().position(|&(_, len)| len >= n) {
            let (start, len) = self.code.free[k];
            if len > n {
                put_free(self.mem.words_mut(), start + n, len - n);
                self.code.free[k] = (start + n, len - n);
            } else {
                self.code.free.remove(k);
            }
            return start;
        }
        let at = self.code.top;
        assert!(at + n <= CODE_BASE + CODE_WORDS, "the code area is full: {n} words more, past {} in use", self.code.used - n);
        self.code.top = at + n;
        at
    }

    /// Where a code bloblet's suffix, its code, runs from: its address in
    /// the code area's read+execute view. Its fields are at the same
    /// distances before it there, so its code reaches them PC-relatively.
    pub fn code_exec_address(&self, v: Value) -> usize {
        assert!(self.is_code_bloblet(v), "{v:?} is not in the code area");
        let view = self.code_exec.as_ref().expect("the code area has an execute view");
        view.exec_address(v.index() * 8)
    }

    /// After a code bloblet's suffix is written with instructions: make them
    /// runnable at [`code_exec_address`](Heap::code_exec_address). Writing
    /// its fields needs none of this.
    pub fn flush_code(&self, v: Value) {
        assert!(self.is_code_bloblet(v), "{v:?} is not in the code area");
        let bytes = self.bloblet_head(v).bytes;
        let view = self.code_exec.as_ref().expect("the code area has an execute view");
        view.flush(v.index() * 8, bytes.max(1));
    }

    /// Whether `v` refers into the code area.
    pub fn is_code_bloblet(&self, v: Value) -> bool {
        v.is_bloblet() && in_code_area(self.ix(v))
    }

    /// Words in the code area's objects, and words its walkable part spans
    /// (objects and free blocks): for reports and tests.
    pub fn code_words(&self) -> (usize, usize) {
        (self.code.used, self.code.top.saturating_sub(CODE_BASE))
    }

    /// After a collection: every object not in `marks` (by main header) is
    /// freed, adjacent free space coalesced, and free space at the end
    /// given back to the walkable part's end. Pages wholly inside a free
    /// block are given back to the system.
    pub(super) fn sweep_code(&mut self, marks: &HashSet<usize>) {
        let (mut at, top) = (CODE_BASE, self.code.top);
        let mut free = Vec::new();
        let mut used = 0;
        let mut run: Option<usize> = None;
        while at < top {
            let w = self.word(at);
            debug_assert!(is_header(w), "the code area is walkable: no header at {at}");
            let main = at + is_extension(w) as usize;
            let size = read_head(self.mem.words(), main).size();
            if marks.contains(&main) {
                if let Some(start) = run.take() {
                    free.push((start, at - start));
                }
                used += size;
            } else if run.is_none() {
                run = Some(at);
            }
            at += size;
        }
        self.code.top = run.unwrap_or(top).max(CODE_BASE);
        for &(start, len) in &free {
            put_free(self.mem.words_mut(), start, len);
            self.mem.release(start + 1..start + len);
        }
        if let Some(start) = run {
            self.mem.release(start..top);
        }
        self.code.free = free;
        self.code.used = used;
        self.code.taken = 0;
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
