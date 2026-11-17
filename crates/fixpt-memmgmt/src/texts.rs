//! Text stored once for the process (the user's, 2026-11-17; `TODO.md`
//! §292): UTF-8, each text once, never changed, moved or freed. A text is
//! known by its number, which a heap's `Text` value carries, and which the
//! Rust side holds where it would hold a `String`: what it reads is a
//! `&'static str` of the text where it is kept, nothing copied, nothing
//! lent.
//!
//! What makes the view of a text as a `str` sound is here alone: the bytes
//! are in memory of this module's own, which nothing else is given a way to
//! write; a text's bytes are copied from a `&str`, so are UTF-8; and a
//! text's bytes, and where it ends, are written before the count that makes
//! it readable is (`Release`, read by `Acquire`), and never after. A number
//! past the count is no text ([`get`] says none), so a number from
//! anywhere, a heap's word that a fault changed, an image's, reads a text
//! or nothing.
//!
//! Each text once: [`intern`] gives a text's number, the same for equal
//! texts, so equal numbers are equal texts. The numbers depend on what the
//! process made before; nothing written, compared for order or hashed into
//! a name may use one (an image carries its texts and where their numbers
//! are, `fixpt-heap`'s `image`). Nothing is freed, so what is kept here is
//! only what lived as long as the process already: an interned symbol's
//! name, never a string, nor an uninterned symbol's (a gensym's, a hygienic
//! rename's), which a program makes as it runs. No primitive makes a text
//! of a program's string.

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{OnceLock, RwLock};

/// The most bytes of text, and the most texts, the process may keep:
/// address space reserved once, pages committed by the system as they are
/// first written.
const BYTES_MAX: usize = 1 << 32;
const COUNT_MAX: usize = 1 << 28;

struct Store {
    /// The texts' bytes, one after another.
    bytes: *mut u8,
    /// Where text `i` ends in `bytes`; it starts where text `i - 1` ends.
    ends: *mut u64,
    /// How many texts are readable: each below it is written whole.
    count: AtomicU32,
    /// Each text's number, by the text, and how many bytes are written:
    /// what a text is made under, one at a time.
    index: RwLock<Index>,
}

struct Index {
    numbers: std::collections::HashMap<&'static str, u32, std::hash::BuildHasherDefault<TextHasher>>,
    used: usize,
}

// SAFETY: the store's memory is written only under `index`'s write lock,
// and only past what `count` makes readable; what is readable is never
// written again. So a reader on any thread, which reads only below the
// count it loaded (`Acquire`, after the writer's `Release`), sees bytes no
// one writes.
unsafe impl Sync for Store {}
// SAFETY: the same: the store is plain memory, the process's.
unsafe impl Send for Store {}

static STORE: OnceLock<Store> = OnceLock::new();

fn store() -> &'static Store {
    STORE.get_or_init(|| Store {
        bytes: map(BYTES_MAX),
        ends: map(COUNT_MAX * 8) as *mut u64,
        count: AtomicU32::new(0),
        index: RwLock::new(Index { numbers: Default::default(), used: 0 }),
    })
}

/// `len` bytes of address space, readable and writable, zero, never given
/// back; the process stops if the system refuses them.
fn map(len: usize) -> *mut u8 {
    #[cfg(target_os = "linux")]
    let flags = libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_NORESERVE;
    #[cfg(not(target_os = "linux"))]
    let flags = libc::MAP_PRIVATE | libc::MAP_ANON;
    // SAFETY: an anonymous mapping, used only through the store.
    let p = unsafe { libc::mmap(std::ptr::null_mut(), len, libc::PROT_READ | libc::PROT_WRITE, flags, -1, 0) };
    assert!(p != libc::MAP_FAILED, "no address space for the process's texts ({len} bytes)");
    p as *mut u8
}

/// Text `n`, if there is one.
#[inline]
pub fn get(n: u32) -> Option<&'static str> {
    let s = store();
    if n >= s.count.load(Ordering::Acquire) {
        return None;
    }
    let i = n as usize;
    // SAFETY: `i` and `i - 1` are below the count loaded, so their ends
    // were written before it was, and are never written again; they are
    // within `ends`, which holds `COUNT_MAX`.
    let (start, end) = unsafe { (if i == 0 { 0 } else { *s.ends.add(i - 1) as usize }, *s.ends.add(i) as usize) };
    // SAFETY: the bytes from `start` to `end` are text `i`'s, copied from
    // a `str` before the count was published, never written after, within
    // `bytes`; so they are UTF-8 and stay as they are for the process's
    // life.
    Some(unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(s.bytes.add(start), end - start)) })
}

/// The number of text `text`, if it has one; making none.
pub fn find(text: &str) -> Option<u32> {
    store().index.read().unwrap_or_else(|e| e.into_inner()).numbers.get(text).copied()
}

/// The number of text `text`: its own, made now if it had none.
pub fn intern(text: &str) -> u32 {
    let s = store();
    if let Some(&n) = s.index.read().unwrap_or_else(|e| e.into_inner()).numbers.get(text) {
        return n;
    }
    // A poisoned lock is as good as any: what a panic left half done is
    // past the count, unread, and written over by the next text.
    let mut ix = s.index.write().unwrap_or_else(|e| e.into_inner());
    if let Some(&n) = ix.numbers.get(text) {
        return n;
    }
    let n = s.count.load(Ordering::Relaxed) as usize;
    let end = ix.used + text.len();
    assert!(n < COUNT_MAX && end <= BYTES_MAX, "the process's texts are full ({n} texts, {} bytes)", ix.used);
    // SAFETY: past every byte and end readable (`used`, `n`), and within
    // the store; the write lock held, so no one else writes.
    unsafe {
        std::ptr::copy_nonoverlapping(text.as_ptr(), s.bytes.add(ix.used), text.len());
        *s.ends.add(n) = end as u64;
    }
    s.count.store(n as u32 + 1, Ordering::Release);
    ix.used = end;
    let kept = get(n as u32).expect("readable now");
    ix.numbers.insert(kept, n as u32);
    n as u32
}

/// How many texts there are: each number below it is one.
pub fn count() -> u32 {
    store().count.load(Ordering::Acquire)
}

/// A hasher for the texts' index: a multiply a word, as `fixpt-heap`'s
/// `WordHasher` (its keys names, none an adversary's).
#[derive(Default)]
struct TextHasher(u64);

impl std::hash::Hasher for TextHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        let mut words = bytes.chunks_exact(8);
        for w in &mut words {
            self.write_u64(u64::from_le_bytes(w.try_into().expect("8 bytes")));
        }
        let rest = words.remainder();
        if !rest.is_empty() {
            let mut last = [0u8; 8];
            last[..rest.len()].copy_from_slice(rest);
            self.write_u64(u64::from_le_bytes(last) ^ (rest.len() as u64) << 59);
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0 ^ x).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_text_is_kept_once_and_read_where_it_is() {
        let a = intern("texts-test:car");
        let b = intern("texts-test:λx");
        assert_ne!(a, b);
        assert_eq!(intern("texts-test:car"), a);
        assert_eq!(get(a), Some("texts-test:car"));
        assert_eq!(get(b), Some("texts-test:λx"));
        assert_eq!(find("texts-test:λx"), Some(b));
        assert_eq!(find("texts-test:none"), None);
        let e = intern("");
        assert_eq!(get(e), Some(""));
        // The same bytes each time: kept, not copied.
        assert!(std::ptr::eq(get(a).unwrap(), get(a).unwrap()));
    }

    #[test]
    fn a_number_past_the_texts_is_none() {
        assert_eq!(get(u32::MAX), None);
        assert_eq!(get(count()), None);
    }

    #[test]
    fn threads_intern_alike() {
        let names: Vec<String> = (0..500).map(|i| format!("texts-test:thread-{i}")).collect();
        let runs: Vec<Vec<u32>> = std::thread::scope(|sc| {
            let hs: Vec<_> = (0..8)
                .map(|t| {
                    let names = &names;
                    sc.spawn(move || {
                        // Each thread in its own order, reading as it goes.
                        let mut out = vec![0; names.len()];
                        for k in 0..names.len() {
                            let n = names.len();
                            let i = if t % 2 == 0 { (k + t * 61) % n } else { n - 1 - (k + t * 61) % n };
                            out[i] = intern(&names[i]);
                            assert_eq!(get(out[i]), Some(names[i].as_str()));
                        }
                        out
                    })
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        assert!(runs.windows(2).all(|w| w[0] == w[1]));
    }
}
