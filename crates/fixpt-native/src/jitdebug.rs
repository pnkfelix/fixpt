//! The machine code we make, told to `gdb` and `lldb` through the GDB JIT
//! interface: each piece of code placed (`crate::symbols::note`) is
//! described by a small ELF object made in memory and linked into the list
//! rooted at `__jit_debug_descriptor`, and the empty function
//! `__jit_debug_register_code`, on which a debugger keeps a breakpoint, is
//! called after each change. A debugger attached later reads the whole
//! list. An object has, for each piece, a `.text.k` section at the code's
//! own address (no bytes: the debugger reads them from the process) and a
//! symbol naming it; where the code's frames are known, a `.debug_frame` saying how to
//! unwind each instruction (`crate::cfi`).
//!
//! Names cost little; frames, read from every instruction, cost some 7% of
//! loading kayak's compiler, so they are made only once a debugger is
//! here: when it is, it keeps a breakpoint (`int3`) at the start of
//! `__jit_debug_register_code` while the program runs, which a flush (at
//! each run, compile and time slice's end) reads, and every object is
//! then made again with its frames. A debugger attached while native code
//! loops has them once it lets the program go on (to its next time slice).
//! `FIXPT_JIT_DEBUG`: `0` registers nothing; `names` never frames;
//! `frames` makes them from the start.
//!
//! Code is collected and its room used again, and the cellular machine's
//! code space is replaced by a copying collection: a piece placed where an
//! older one was replaces it, and a code space unmapped forgets the pieces
//! in it ([`forget`]).
//!
//! `docs/research/debugging.md` says what this gives and what it does not.

use std::collections::BTreeMap;
use std::sync::Mutex;

/// One entry of the list a debugger reads (the GDB JIT interface's
/// `jit_code_entry`).
#[repr(C)]
struct CodeEntry {
    next: *mut CodeEntry,
    prev: *mut CodeEntry,
    symfile: *const u8,
    size: u64,
}

/// The list's root (`jit_descriptor`): its version, what the last change
/// was, the entry it was of, and the first entry.
#[repr(C)]
pub struct Descriptor {
    version: u32,
    action: u32,
    relevant: *mut CodeEntry,
    first: *mut CodeEntry,
}

const NOACTION: u32 = 0;
const REGISTER: u32 = 1;
const UNREGISTER: u32 = 2;

/// The root a debugger finds by this name.
#[unsafe(no_mangle)]
pub static mut __jit_debug_descriptor: Descriptor =
    Descriptor { version: 1, action: NOACTION, relevant: std::ptr::null_mut(), first: std::ptr::null_mut() };

/// Called after each change to the list; a debugger breaks here to read
/// it. Never inlined, and never empty to the optimizer.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn __jit_debug_register_code() {
    // SAFETY: an empty instruction sequence, with no effect; it only keeps
    // the call from being removed.
    unsafe { std::arch::asm!("") }
}

/// An object registered: its entry, the object it points at, and the
/// pieces it describes, kept here for as long as the entry is listed.
struct Registered {
    entry: Box<CodeEntry>,
    _elf: Vec<u8>,
    pieces: Vec<Owned>,
}

// The raw pointers are into this value's own boxes, and are touched only
// under the registry's lock.
unsafe impl Send for Registered {}

/// A piece, kept: where it is, its name, whether a call enters it (so
/// that its frames can be known, `crate::cfi`), and its frames, once made.
#[derive(Clone)]
struct Owned {
    start: usize,
    len: usize,
    name: String,
    called: bool,
    frame: Option<Vec<u8>>,
}

impl Owned {
    /// Its frames made, if they can be and are not yet.
    fn framed(&mut self) {
        if self.called && self.frame.is_none() {
            // SAFETY: a piece registered is code placed in memory still
            // mapped: a code space unmapped forgets its pieces first.
            let code = unsafe { std::slice::from_raw_parts(self.start as *const u8, self.len) };
            self.frame = crate::cfi::frame_of(code);
        }
    }
}

/// What is registered: each object by its number; each piece's range and
/// object, by its first address (no two overlap); and the pieces noted
/// since the last [`flush`].
struct Registry {
    objects: BTreeMap<u64, Registered>,
    pieces: BTreeMap<usize, (usize, u64)>,
    pending: Vec<Owned>,
    next: u64,
}

static REGISTRY: Mutex<Registry> = Mutex::new(Registry { objects: BTreeMap::new(), pieces: BTreeMap::new(), pending: Vec::new(), next: 0 });

/// Pieces noted wait for a [`flush`], so that a debugger reads one object
/// for many; past this many, they are flushed anyway.
const MOST_PENDING: usize = 512;

/// Whether any piece waits for a flush: for [`flush`] to cost a load where
/// none does, as before each run.
static PENDING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// `FIXPT_JIT_DEBUG`: `0` nothing registered; `names` only names; `frames`
/// names and frames from the start; else frames once a debugger is here.
fn mode() -> u8 {
    static MODE: std::sync::OnceLock<u8> = std::sync::OnceLock::new();
    *MODE.get_or_init(|| match std::env::var("FIXPT_JIT_DEBUG").as_deref() {
        Ok("0") => 0,
        Ok("names") => 1,
        Ok("frames") => 3,
        _ => 2,
    })
}

/// Whether code is registered.
pub fn enabled() -> bool {
    mode() > 0
}

/// Whether frames are made: from the start, or since a debugger came.
static FRAMES: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

fn frames() -> bool {
    mode() == 3 || FRAMES.load(std::sync::atomic::Ordering::Relaxed)
}

/// Whether a debugger is here: a breakpoint at the start of
/// `__jit_debug_register_code`, before its return.
fn debugger_here() -> bool {
    let f = __jit_debug_register_code as *const u8;
    for k in 0..8 {
        // SAFETY: the function's own code, a few bytes of it, up to its
        // `ret`; code is readable.
        match unsafe { f.add(k).read_volatile() } {
            0xCC => return true,
            0xC3 => return false,
            _ => {}
        }
    }
    false
}

/// A piece of code, as a debugger is told of it.
pub struct Piece<'a> {
    pub start: usize,
    pub len: usize,
    /// Its name, as `crate::symbols` has it ([`debugger_name`] makes the
    /// debugger's).
    pub name: &'a str,
    /// Whether it is entered by a call, its return address on the stack's
    /// top, so that its frames can be known (`crate::cfi`).
    pub called: bool,
}

/// `piece` to be registered at the next [`flush`], in place of every
/// piece it overlaps.
pub fn register(piece: &Piece) {
    let mut r = lock();
    PENDING.store(true, std::sync::atomic::Ordering::Relaxed);
    let called = piece.called && mode() > 1;
    r.pending.push(Owned { start: piece.start, len: piece.len.max(1), name: debugger_name(piece.name), called, frame: None });
    if r.pending.len() >= MOST_PENDING {
        r.flush();
    }
}

/// The pieces noted since the last flush, told to a debugger, as one
/// object: called once code is placed and before it runs.
pub fn flush() {
    use std::sync::atomic::Ordering::Relaxed;
    if mode() == 2 && !FRAMES.load(Relaxed) && debugger_here() {
        FRAMES.store(true, Relaxed);
        lock().refresh();
    }
    if PENDING.load(Relaxed) {
        lock().flush();
    }
}

/// Every piece within `start..end` unregistered: code there is gone.
pub fn forget(start: usize, end: usize) {
    if enabled() {
        let mut r = lock();
        r.pending.retain(|p| p.start + p.len <= start || p.start >= end);
        r.drop_overlapping(start, end);
    }
}

fn lock() -> std::sync::MutexGuard<'static, Registry> {
    REGISTRY.lock().unwrap_or_else(|e| e.into_inner())
}

impl Registry {
    fn flush(&mut self) {
        PENDING.store(false, std::sync::atomic::Ordering::Relaxed);
        let mut new = std::mem::take(&mut self.pending);
        if new.is_empty() {
            return;
        }
        // A later piece where an earlier one was replaces it.
        let mut kept: Vec<Owned> = Vec::new();
        for p in new.drain(..).rev() {
            if kept.iter().all(|q| q.start + q.len <= p.start || q.start >= p.start + p.len) {
                kept.push(p);
            }
        }
        kept.sort_by_key(|p| p.start);
        for p in &kept {
            self.drop_overlapping(p.start, p.start + p.len);
        }
        self.add(kept);
    }

    /// Every object made again, with its frames: a debugger has come,
    /// which stops at each change, so in few objects.
    fn refresh(&mut self) {
        let ids: Vec<u64> = self.objects.keys().copied().collect();
        let mut all: Vec<Owned> = ids.into_iter().flat_map(|id| self.remove(id)).collect();
        all.sort_by_key(|p| p.start);
        while !all.is_empty() {
            let rest = all.split_off(all.len().min(4096));
            self.add(std::mem::replace(&mut all, rest));
        }
    }

    /// `pieces`, none overlapping a registered one, registered as one object.
    fn add(&mut self, mut pieces: Vec<Owned>) {
        if pieces.is_empty() {
            return;
        }
        if frames() {
            pieces.iter_mut().for_each(Owned::framed);
        }
        let id = self.next;
        self.next += 1;
        let elf = object(&pieces);
        let mut entry = Box::new(CodeEntry { next: std::ptr::null_mut(), prev: std::ptr::null_mut(), symfile: elf.as_ptr(), size: elf.len() as u64 });
        // SAFETY: the descriptor is changed only under the registry's lock;
        // the entry and its object stay where they are until unregistered.
        unsafe {
            let d = &raw mut __jit_debug_descriptor;
            entry.next = (*d).first;
            let e: *mut CodeEntry = &mut *entry;
            if !(*d).first.is_null() {
                (*(*d).first).prev = e;
            }
            (*d).first = e;
            (*d).relevant = e;
            (*d).action = REGISTER;
            __jit_debug_register_code();
            (*d).relevant = std::ptr::null_mut();
            (*d).action = NOACTION;
        }
        for p in &pieces {
            self.pieces.insert(p.start, (p.start + p.len, id));
        }
        self.objects.insert(id, Registered { entry, _elf: elf, pieces });
    }

    /// Every registered piece overlapping `start..end` gone: each object
    /// one is in unregistered, and made again of its other pieces.
    fn drop_overlapping(&mut self, start: usize, end: usize) {
        let gone: Vec<(usize, u64)> = self.pieces.range(..end).rev().take_while(|(_, (e, _))| *e > start).map(|(&s, &(_, id))| (s, id)).collect();
        let mut ids: Vec<u64> = gone.iter().map(|g| g.1).collect();
        ids.sort();
        ids.dedup();
        for id in ids {
            let pieces = self.remove(id);
            let rest: Vec<Owned> = pieces.into_iter().filter(|p| p.start + p.len <= start || p.start >= end).collect();
            self.add(rest);
        }
    }

    /// Object `id` unregistered and gone; its pieces.
    fn remove(&mut self, id: u64) -> Vec<Owned> {
        let Some(mut r) = self.objects.remove(&id) else { return Vec::new() };
        // SAFETY: as in `add`; the entry is in the list until here.
        unsafe {
            let d = &raw mut __jit_debug_descriptor;
            let e: *mut CodeEntry = &mut *r.entry;
            if r.entry.prev.is_null() {
                (*d).first = r.entry.next;
            } else {
                (*r.entry.prev).next = r.entry.next;
            }
            if !r.entry.next.is_null() {
                (*r.entry.next).prev = r.entry.prev;
            }
            (*d).relevant = e;
            (*d).action = UNREGISTER;
            __jit_debug_register_code();
            (*d).relevant = std::ptr::null_mut();
            (*d).action = NOACTION;
        }
        for p in &r.pieces {
            self.pieces.remove(&p.start);
        }
        std::mem::take(&mut r.pieces)
    }
}

/// The name a debugger shows for a piece `crate::symbols` names `what`: a
/// native procedure by its own name, as one would break on it (`b go`);
/// register and cellular words, and the machines' own code, marked.
pub fn debugger_name(what: &str) -> String {
    let name = if let Some(n) = what.strip_prefix("native convention: ") {
        format!("fixpt:{n}")
    } else if let Some(n) = what.strip_prefix("cellular machine: ") {
        format!("cells:{n}")
    } else if let Some(n) = what.strip_prefix("native ") {
        n.to_string()
    } else if let Some(n) = what.strip_prefix("register word ") {
        format!("regs:{n}")
    } else if let Some(n) = what.strip_prefix("word ") {
        format!("cells:{n}")
    } else {
        what.to_string()
    };
    name.replace(' ', "-")
}

// The ELF object: a header, the sections' contents, and their headers.

const SHT_PROGBITS: u32 = 1;
const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_NOBITS: u32 = 8;
const SHF_ALLOC: u64 = 2;
const SHF_EXECINSTR: u64 = 4;

struct Section {
    name: String,
    kind: u32,
    flags: u64,
    addr: u64,
    data: Vec<u8>,
    /// For `SHT_NOBITS`, its size.
    size: u64,
    link: u32,
    info: u32,
    align: u64,
    entsize: u64,
}

fn section(name: &str, kind: u32, data: Vec<u8>) -> Section {
    Section { name: name.to_string(), kind, flags: 0, addr: 0, size: data.len() as u64, data, link: 0, info: 0, align: 1, entsize: 0 }
}

/// The object describing `pieces`: for each, a `.text.k` section at its
/// address (sections 1 to n, in order) and a global function symbol; and
/// a `.debug_frame` of those whose frames are known.
fn object(pieces: &[Owned]) -> Vec<u8> {
    let n = pieces.len() as u32;
    let mut strtab = vec![0u8];
    let mut symtab = vec![0u8; 24];
    for (k, p) in pieces.iter().enumerate() {
        symtab.extend_from_slice(&(strtab.len() as u32).to_le_bytes()); // st_name
        strtab.extend_from_slice(p.name.as_bytes());
        strtab.push(0);
        symtab.push(0x12); // STB_GLOBAL, STT_FUNC
        symtab.push(0); // STV_DEFAULT
        symtab.extend_from_slice(&(k as u16 + 1).to_le_bytes()); // its .text
        symtab.extend_from_slice(&0u64.to_le_bytes()); // at its start
        symtab.extend_from_slice(&(p.len as u64).to_le_bytes());
    }
    let mut sections: Vec<Section> = pieces
        .iter()
        .enumerate()
        .map(|(k, p)| Section { flags: SHF_ALLOC | SHF_EXECINSTR, addr: p.start as u64, size: p.len as u64, ..section(&format!(".text.{k}"), SHT_NOBITS, Vec::new()) })
        .collect();
    sections.push(Section { link: n + 2, info: 1, align: 8, entsize: 24, ..section(".symtab", SHT_SYMTAB, symtab) });
    sections.push(section(".strtab", SHT_STRTAB, strtab));
    let framed: Vec<(u64, u64, &[u8])> = pieces.iter().filter_map(|p| Some((p.start as u64, p.len as u64, p.frame.as_deref()?))).collect();
    if !framed.is_empty() {
        sections.push(Section { align: 8, ..section(".debug_frame", SHT_PROGBITS, crate::cfi::debug_frame(&framed)) });
    }
    elf(sections)
}

fn elf(mut sections: Vec<Section>) -> Vec<u8> {
    // The section names, last.
    let mut shstrtab = vec![0u8];
    let mut names = Vec::new();
    for s in sections.iter().map(|s| s.name.as_str()).chain([".shstrtab"]) {
        names.push(shstrtab.len() as u32);
        shstrtab.extend_from_slice(s.as_bytes());
        shstrtab.push(0);
    }
    sections.push(section(".shstrtab", SHT_STRTAB, shstrtab));
    let machine: u16 = if cfg!(target_arch = "aarch64") { 183 } else { 62 };
    let mut out = vec![0u8; 64];
    let mut offsets = Vec::new();
    for s in &sections {
        while !out.len().is_multiple_of(s.align.max(1) as usize) {
            out.push(0);
        }
        offsets.push(out.len() as u64);
        out.extend_from_slice(&s.data);
    }
    while !out.len().is_multiple_of(8) {
        out.push(0);
    }
    let shoff = out.len() as u64;
    out.extend_from_slice(&[0u8; 64]); // section 0, none
    for (k, s) in sections.iter().enumerate() {
        out.extend_from_slice(&names[k].to_le_bytes());
        out.extend_from_slice(&s.kind.to_le_bytes());
        out.extend_from_slice(&s.flags.to_le_bytes());
        out.extend_from_slice(&s.addr.to_le_bytes());
        out.extend_from_slice(&(if s.kind == SHT_NOBITS { 0 } else { offsets[k] }).to_le_bytes());
        out.extend_from_slice(&s.size.to_le_bytes());
        out.extend_from_slice(&s.link.to_le_bytes());
        out.extend_from_slice(&s.info.to_le_bytes());
        out.extend_from_slice(&s.align.to_le_bytes());
        out.extend_from_slice(&s.entsize.to_le_bytes());
    }
    let h = &mut out[..64];
    h[..4].copy_from_slice(b"\x7fELF");
    h[4] = 2; // 64 bits
    h[5] = 1; // little-endian
    h[6] = 1; // version
    h[16..18].copy_from_slice(&1u16.to_le_bytes()); // ET_REL
    h[18..20].copy_from_slice(&machine.to_le_bytes());
    h[20..24].copy_from_slice(&1u32.to_le_bytes());
    h[40..48].copy_from_slice(&shoff.to_le_bytes());
    h[52..54].copy_from_slice(&64u16.to_le_bytes()); // e_ehsize
    h[58..60].copy_from_slice(&64u16.to_le_bytes()); // e_shentsize
    h[60..62].copy_from_slice(&(sections.len() as u16 + 1).to_le_bytes());
    h[62..64].copy_from_slice(&(sections.len() as u16).to_le_bytes()); // .shstrtab, last
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn piece(start: usize, len: usize, name: &str) -> Owned {
        Owned { start, len, name: name.into(), called: false, frame: None }
    }

    /// An object of two pieces: an ELF header, a `.text.k` section for each
    /// at its address, and their names in the string table.
    #[test]
    fn an_object_of_two_pieces() {
        let o = object(&[piece(0x1000, 16, "go"), piece(0x2000, 32, "deep")]);
        assert_eq!(&o[..4], b"\x7fELF");
        let shnum = u16::from_le_bytes([o[60], o[61]]);
        assert_eq!(shnum, 6, "none, two .text, .symtab, .strtab, .shstrtab");
        let shoff = u64::from_le_bytes(o[40..48].try_into().unwrap()) as usize;
        let addr = |k: usize| u64::from_le_bytes(o[shoff + 64 * k + 16..shoff + 64 * k + 24].try_into().unwrap());
        assert_eq!((addr(1), addr(2)), (0x1000, 0x2000));
        let text = String::from_utf8_lossy(&o);
        assert!(text.contains("go\0deep\0") && text.contains(".text.1"));
    }

    /// Pieces flushed are listed; a piece placed over one replaces it, the
    /// rest of its object kept; a range forgotten is gone.
    #[test]
    fn the_list_follows_the_code() {
        let listed = || {
            let mut n = Vec::new();
            let r = lock();
            for o in r.objects.values() {
                n.extend(o.pieces.iter().map(|p| p.name.clone()));
            }
            n.sort();
            n
        };
        let base = 0x7000_0000_0000;
        for (k, name) in ["a", "b", "c"].iter().enumerate() {
            register(&Piece { start: base + 64 * k, len: 64, name, called: false });
        }
        flush();
        assert!(["a", "b", "c"].iter().all(|n| listed().contains(&n.to_string())));
        register(&Piece { start: base + 64, len: 64, name: "b2", called: false });
        flush();
        let l = listed();
        assert!(l.contains(&"b2".into()) && !l.contains(&"b".into()) && l.contains(&"a".into()) && l.contains(&"c".into()));
        forget(base, base + 192);
        let l = listed();
        assert!(!l.iter().any(|n| ["a", "b2", "c"].contains(&n.as_str())));
    }
}
