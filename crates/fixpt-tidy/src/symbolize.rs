//! Names for our machine code in macOS `sample`'s output. `sample` shows a
//! frame in code we made as `???  (in <unknown binary>)  [0x…]`; with
//! `FIXPT_SYMBOLS=FILE` set, `fixpt` writes where each piece of its machine
//! code is and what it is (`fixpt_native::symbols`), and [`symbolize`]
//! rewrites those frames with the names. It also adds what `sample`'s own
//! "Sort by top of stack" cannot give for our code, which it counts as one
//! `???`: the samples at the top of the stack, by name, ours named.

/// Where each piece of our code was, from `FIXPT_SYMBOLS` files: `START LEN
/// NAME` lines, START in hex. In file order, so later is newer.
pub struct Symbols {
    /// `(start, end, name, line)`, sorted by start; `line` its place in
    /// the files, so the greatest is the newest.
    pieces: Vec<(u64, u64, String, usize)>,
    /// The longest piece, to bound the search back from an address.
    longest: u64,
}

impl Symbols {
    /// The pieces in `text`, a `FIXPT_SYMBOLS` file's contents; lines that
    /// are not `START LEN NAME` are passed over.
    pub fn parse(text: &str) -> Symbols {
        let mut pieces = Vec::new();
        for (i, line) in text.lines().enumerate() {
            let mut parts = line.splitn(3, ' ');
            let (Some(start), Some(len), Some(name)) = (parts.next(), parts.next(), parts.next()) else { continue };
            let (Ok(start), Ok(len)) = (u64::from_str_radix(start, 16), len.parse::<u64>()) else { continue };
            pieces.push((start, start + len, name.to_string(), i));
        }
        pieces.sort_by_key(|p| p.0);
        let longest = pieces.iter().map(|(s, e, _, _)| e - s).max().unwrap_or(0);
        Symbols { pieces, longest }
    }

    /// The name of the code at `addr`, and its offset in bytes there: the
    /// last piece placed there; if others had that room before, their
    /// names too, after "or".
    pub fn name(&self, addr: u64) -> Option<(String, u64)> {
        let upto = self.pieces.partition_point(|p| p.0 <= addr);
        let mut found: Vec<&(u64, u64, String, usize)> = Vec::new();
        for p in self.pieces[..upto].iter().rev() {
            if addr.saturating_sub(p.0) > self.longest {
                break;
            }
            if addr < p.1 {
                found.push(p);
            }
        }
        // The newest is the one placed last: the latest in the files.
        found.sort_by_key(|p| std::cmp::Reverse(p.3));
        let (newest, others) = found.split_first()?;
        let mut name = newest.2.clone();
        let mut also: Vec<&str> = others.iter().map(|p| p.2.as_str()).filter(|n| *n != newest.2).collect();
        also.sort();
        also.dedup();
        if !also.is_empty() {
            name.push_str(&format!(" (or {})", also.join(", ")));
        }
        Some((name, addr - newest.0))
    }
}

const UNKNOWN: &str = "???  (in <unknown binary>)";

/// Frames where a thread waits, rather than works.
const WAITS: &[&str] = &["__ulock_wait", "semaphore_wait_trap", "__psynch_cvwait", "__wait4", "mach_msg2_trap", "kevent", "__select", "__workq_kernreturn"];

/// `sample`'s output, `text`, with each frame in our code named, and a
/// summary of the samples at the top of the stack by name.
pub fn symbolize(symbols: &Symbols, text: &str) -> String {
    let mut out = String::new();
    let mut tops: Vec<(String, u64)> = Vec::new();
    let lines: Vec<&str> = text.lines().collect();
    let mut in_graph = false;
    for (i, line) in lines.iter().enumerate() {
        if line.starts_with("Call graph:") {
            in_graph = true;
        } else if in_graph && line.trim().is_empty() {
            in_graph = false;
        }
        let named = name_frame(symbols, line);
        let shown = named.as_deref().unwrap_or(line);
        out.push_str(shown);
        out.push('\n');
        // A frame with nothing deeper below it is the top of its stacks.
        if in_graph
            && let Some((depth, count, frame)) = graph_line(shown)
            && lines.get(i + 1).and_then(|l| graph_line(l)).is_none_or(|(d, _, _)| d <= depth)
        {
            match tops.iter_mut().find(|(f, _)| *f == frame) {
                Some((_, n)) => *n += count,
                None => tops.push((frame, count)),
            }
        }
    }
    // A thread waiting is not work: said apart, not in the shares.
    let (idle, mut tops): (Vec<_>, Vec<_>) = tops.into_iter().partition(|(f, _)| WAITS.contains(&f.as_str()));
    tops.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let total: u64 = tops.iter().map(|t| t.1).sum();
    out.push_str("\nTop of stack, by name, our code named (fixpt-symbolize):\n");
    out.push_str(&format!("{:>9}  samples waiting ({}), not counted below\n", idle.iter().map(|t| t.1).sum::<u64>(), WAITS.join(", ")));
    for (frame, n) in tops.iter().take(40) {
        out.push_str(&format!("{n:>9}  {:>5.1}%  {frame}\n", 100.0 * *n as f64 / total.max(1) as f64));
    }
    out
}

/// `line` with its frame named, if it is a frame in our code that
/// `symbols` names.
fn name_frame(symbols: &Symbols, line: &str) -> Option<String> {
    let at = line.find(UNKNOWN)?;
    let rest = &line[at + UNKNOWN.len()..];
    let open = rest.find("[0x")?;
    let digits: String = rest[open + 3..].chars().take_while(|c| c.is_ascii_hexdigit()).collect();
    let addr = u64::from_str_radix(&digits, 16).ok()?;
    let (name, offset) = symbols.name(addr)?;
    Some(format!("{}{name}  (in fixpt code) + {offset}  {}", &line[..at], &rest[open..]))
}

/// A call graph line: its depth (where its count starts), its count, and
/// its frame (without where it is in its binary).
fn graph_line(line: &str) -> Option<(usize, u64, String)> {
    let depth = line.find(|c: char| c.is_ascii_digit())?;
    if !line[..depth].chars().all(|c| " +!:|".contains(c)) {
        return None;
    }
    let rest = &line[depth..];
    let digits = rest.find(' ')?;
    let count = rest[..digits].parse().ok()?;
    let frame = rest[digits..].trim_start();
    let frame = frame.split("  (in ").next().unwrap_or(frame).trim_end();
    Some((depth, count, without_hash(frame).to_string()))
}

/// A Rust symbol without its `::h…` hash, which only tells copies apart.
fn without_hash(frame: &str) -> &str {
    match frame.rsplit_once("::h") {
        Some((name, hash)) if hash.len() == 16 && hash.chars().all(|c| c.is_ascii_hexdigit()) => name,
        _ => frame,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAP: &str = "1000 16 cellular machine: docol\n2004 8 native k-old\n2000 32 native k-check\n2000 8 native k-new\n";

    #[test]
    fn an_address_is_named_by_the_piece_it_is_in_newest_first() {
        let s = Symbols::parse(MAP);
        assert_eq!(s.name(0x1004), Some(("cellular machine: docol".into(), 4)));
        assert_eq!(s.name(0x1010), None);
        assert_eq!(s.name(0x2004), Some(("native k-new (or native k-check, native k-old)".into(), 4)));
        assert_eq!(s.name(0x2010), Some(("native k-check".into(), 16)));
    }

    #[test]
    fn frames_are_named_and_tops_counted() {
        let sample = "Call graph:\n    5 main  (in fixpt) + 4  [0x10]\n    + 3 ???  (in <unknown binary>)  [0x2010]\n    + 2 ???  (in <unknown binary>)  [0x1004,0x1008,...]\n\nTotal\n";
        let out = symbolize(&Symbols::parse(MAP), sample);
        assert!(out.contains("    + 3 native k-check  (in fixpt code) + 16  [0x2010]"), "{out}");
        assert!(out.contains("    + 2 cellular machine: docol  (in fixpt code) + 4  [0x1004,0x1008,...]"), "{out}");
        assert!(out.contains("        3   60.0%  native k-check\n        2   40.0%  cellular machine: docol\n"), "{out}");
    }
}
