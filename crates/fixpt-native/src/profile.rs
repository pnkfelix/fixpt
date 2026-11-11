//! Calls counted in compiled register code, with `FIXPT_PROFILE_CALLS`
//! set (`TODO.md` §236): each call by its site (the calling word and the
//! cell of its `invoke`) and the word entered, so that a profile of native
//! code (`perf`, which names our words but cannot walk their stacks) has
//! who calls whom, and how often. The x86_64 machine's register words,
//! assembled with it set, note their site at each call and count at their
//! entry (`cellular::x64::regcode`); nothing else is counted. Off, no code
//! of it is assembled.

use crate::cellular::State;
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

/// Whether calls are counted: `FIXPT_PROFILE_CALLS` set, read once.
pub fn on() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("FIXPT_PROFILE_CALLS").is_some())
}

#[derive(Default)]
struct Counts {
    /// Each word's name, by its id; and each id, by its name.
    words: Vec<String>,
    ids: HashMap<String, u32>,
    /// Each call site, by its id (from 1; 0 is none): its word's id and
    /// the cell of its call.
    sites: Vec<(u32, usize)>,
    /// Calls, by site and the word entered.
    edges: HashMap<(u32, u32), u64>,
}

fn counts() -> std::sync::MutexGuard<'static, Counts> {
    static COUNTS: OnceLock<Mutex<Counts>> = OnceLock::new();
    COUNTS.get_or_init(|| Mutex::new(Counts { sites: vec![(0, 0)], ..Default::default() })).lock().unwrap_or_else(|e| e.into_inner())
}

/// The id of the word named `name`, made if it has none.
pub fn word_id(name: &str) -> u32 {
    let mut c = counts();
    if let Some(&k) = c.ids.get(name) {
        return k;
    }
    let k = c.words.len() as u32;
    c.words.push(name.to_string());
    c.ids.insert(name.to_string(), k);
    k
}

/// The id of the call at cell `cell` of the word of id `word`.
pub fn site_id(word: u32, cell: usize) -> u32 {
    let mut c = counts();
    c.sites.push((word, cell));
    (c.sites.len() - 1) as u32
}

/// Called by a register word's entry, word `word` entered: the call
/// counted from the site its caller noted (`State::prof_site`), which is
/// cleared, so that an entry no noted call made counts from none.
///
/// # Safety
/// `st` is the running machine's state.
pub unsafe extern "C" fn enter(st: *mut State, word: u32) {
    let site = unsafe { (*st).prof_site } as u32;
    unsafe { (*st).prof_site = 0 };
    *counts().edges.entry((site, word)).or_insert(0) += 1;
}

/// The counts so far: the `n` words entered most, each with its calls and
/// its callers that called it most, by site.
pub fn report(n: usize) -> String {
    let c = counts();
    let mut calls: HashMap<u32, u64> = HashMap::new();
    for (&(_, w), &k) in &c.edges {
        *calls.entry(w).or_default() += k;
    }
    let mut top: Vec<(u32, u64)> = calls.into_iter().collect();
    top.sort_by(|a, b| b.1.cmp(&a.1));
    let total: u64 = top.iter().map(|(_, k)| k).sum();
    let mut out = format!("{total} calls counted, into {} words\n", top.len());
    for (w, k) in top.iter().take(n) {
        out.push_str(&format!("{k:>12}  {}\n", c.words[*w as usize]));
        let mut from: Vec<(u32, u64)> = c.edges.iter().filter(|((_, x), _)| x == w).map(|(&(s, _), &k)| (s, k)).collect();
        from.sort_by(|a, b| b.1.cmp(&a.1));
        for (s, k) in from.iter().take(4) {
            let (cw, cell) = c.sites[*s as usize];
            let caller = if *s == 0 { "(no noted call)".to_string() } else { format!("{} cell {cell}", c.words[cw as usize]) };
            out.push_str(&format!("{k:>16}  from {caller}\n"));
        }
    }
    out
}
