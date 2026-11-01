//! A rep's readable form (`heap-types.md`, "Serialization"), for people:
//! messages, tests, and debugging a binary form. Not the type syntax
//! programs are written in (each checker prints a type so, after importing
//! a rep), but the rep itself, every node and operand as it is:
//!
//! ```text
//! #0=(poly {r} (subr <t type 00000000deadbeef> #0.0 ?0:e (base int) -3 #t))
//! ```
//!
//! - `(head {b …} operand …)`: a node; `{…}`, its binders' names, if any.
//!   `(&head operand …)`: a set node, its operands' order none of it.
//! - `#n=` before a node: its label, its index; `#n#`, that node again (a
//!   node used twice, or a cycle). A node a bound variable names is
//!   labelled too.
//! - `#n.p`: the variable bound at place `p` of node `n`.
//! - `?i:name`: hole `i`.
//! - `<name kind key>`: a constant, its key in hex.
//! - a name, bare, or `|…|` if it would read as something else; an
//!   integer; `#t`, `#f`.

use crate::{Arg, Builder, Const, Rep};
use std::collections::HashMap;
use std::fmt::Write;

/// Rep `rep`, readable.
pub fn write(rep: &Rep) -> String {
    let n = rep.nodes.len();
    let mut uses = vec![0usize; n];
    let mut labelled = vec![false; n];
    uses[0] += 1;
    for node in &rep.nodes {
        for a in &node.args {
            match *a {
                Arg::Node(i) => uses[i as usize] += 1,
                Arg::Bound { binder, .. } => labelled[binder as usize] = true,
                _ => {}
            }
        }
    }
    for k in 0..n {
        labelled[k] |= uses[k] > 1;
    }
    let mut out = String::new();
    let mut done = vec![false; n];
    node(rep, 0, &labelled, &mut done, &mut out);
    out
}

fn node(rep: &Rep, k: usize, labelled: &[bool], done: &mut [bool], out: &mut String) {
    if labelled[k] && done[k] {
        let _ = write!(out, "#{k}#");
        return;
    }
    done[k] = true;
    if labelled[k] {
        let _ = write!(out, "#{k}=");
    }
    let nd = &rep.nodes[k];
    out.push('(');
    if nd.set {
        out.push('&');
    }
    out.push_str(&quoted(rep.name(nd.head)));
    if !nd.binders.is_empty() {
        let names: Vec<String> = nd.binders.iter().map(|&b| quoted(rep.name(b))).collect();
        let _ = write!(out, " {{{}}}", names.join(" "));
    }
    for a in &nd.args {
        out.push(' ');
        match *a {
            Arg::Node(i) => node(rep, i as usize, labelled, done, out),
            Arg::Bound { binder, pos } => {
                let _ = write!(out, "#{binder}.{pos}");
            }
            Arg::Hole(i) => {
                let _ = write!(out, "?{i}:{}", quoted(&rep.holes[i as usize]));
            }
            Arg::Const(i) => {
                let c = &rep.consts[i as usize];
                let _ = write!(out, "<{} {} {:016x}>", quoted(&c.name), quoted(&c.kind), c.key);
            }
            Arg::Sym(i) => out.push_str(&quoted(rep.name(i))),
            Arg::Int(v) => {
                let _ = write!(out, "{v}");
            }
            Arg::Flag(b) => out.push_str(if b { "#t" } else { "#f" }),
        }
    }
    out.push(')');
}

/// Name `s`, bare if it reads back as a name, else between bars.
fn quoted(s: &str) -> String {
    let plain = !s.is_empty()
        && !s.chars().any(|c| c.is_whitespace() || "(){}<>|#?\"".contains(c))
        && !s.starts_with('&')
        && s.parse::<i64>().is_err();
    if plain {
        s.to_string()
    } else {
        format!("|{}|", s.replace('\\', "\\\\").replace('|', "\\|"))
    }
}

/// The rep `text` writes ([`write`]'s form), canonical; or why not.
pub fn read(text: &str) -> Result<Rep, String> {
    let mut p = Parser { s: text.as_bytes(), at: 0, b: Builder::new(), labels: HashMap::new(), holes: HashMap::new() };
    p.space();
    let root = p.node()?;
    p.space();
    if p.at != p.s.len() {
        return Err(format!("text after the rep, at {}", p.at));
    }
    p.b.finish(root).map(|f| f.rep)
}

struct Parser<'a> {
    s: &'a [u8],
    at: usize,
    b: Builder,
    /// Each label's slot.
    labels: HashMap<u64, u32>,
    /// Each hole's number written, the builder's.
    holes: HashMap<u64, Arg>,
}

impl Parser<'_> {
    fn peek(&self) -> Option<u8> {
        self.s.get(self.at).copied()
    }
    fn space(&mut self) {
        while self.peek().is_some_and(|c| c.is_ascii_whitespace()) {
            self.at += 1;
        }
    }
    fn expect(&mut self, c: u8) -> Result<(), String> {
        if self.peek() == Some(c) {
            self.at += 1;
            Ok(())
        } else {
            Err(format!("`{}` expected at {}", c as char, self.at))
        }
    }
    fn number(&mut self) -> Result<u64, String> {
        let start = self.at;
        while self.peek().is_some_and(|c| c.is_ascii_digit()) {
            self.at += 1;
        }
        std::str::from_utf8(&self.s[start..self.at]).ok().and_then(|t| t.parse().ok()).ok_or(format!("a number expected at {start}"))
    }
    /// A name, bare or between bars.
    fn name(&mut self) -> Result<String, String> {
        if self.peek() == Some(b'|') {
            self.at += 1;
            let mut out = Vec::new();
            loop {
                match self.peek() {
                    None => return Err("a `|` name not ended".into()),
                    Some(b'|') => {
                        self.at += 1;
                        break;
                    }
                    Some(b'\\') => {
                        out.push(*self.s.get(self.at + 1).ok_or("a `\\` at the end")?);
                        self.at += 2;
                    }
                    Some(c) => {
                        out.push(c);
                        self.at += 1;
                    }
                }
            }
            return String::from_utf8(out).map_err(|_| "a name not UTF-8".into());
        }
        let start = self.at;
        while self.peek().is_some_and(|c| !c.is_ascii_whitespace() && !b"(){}<>|#?\"".contains(&c)) {
            self.at += 1;
        }
        if start == self.at {
            return Err(format!("a name expected at {start}"));
        }
        Ok(String::from_utf8_lossy(&self.s[start..self.at]).into_owned())
    }
    /// A node, `#n=` labelled or not; its slot.
    fn node(&mut self) -> Result<u32, String> {
        let slot = self.b.reserve();
        if self.peek() == Some(b'#') {
            self.at += 1;
            let n = self.number()?;
            self.expect(b'=')?;
            self.labels.insert(n, slot);
        }
        self.expect(b'(')?;
        let set = self.peek() == Some(b'&');
        if set {
            self.at += 1;
        }
        let head = self.name()?;
        self.space();
        let mut binders = Vec::new();
        if self.peek() == Some(b'{') {
            self.at += 1;
            loop {
                self.space();
                if self.peek() == Some(b'}') {
                    self.at += 1;
                    break;
                }
                binders.push(self.name()?);
            }
        }
        let mut args = Vec::new();
        loop {
            self.space();
            match self.peek() {
                Some(b')') => {
                    self.at += 1;
                    break;
                }
                None => return Err("a node not ended".into()),
                _ => args.push(self.arg()?),
            }
        }
        let refs: Vec<&str> = binders.iter().map(String::as_str).collect();
        if set {
            self.b.fill_set(slot, &head, args);
        } else {
            self.b.fill(slot, &head, &refs, args);
        }
        Ok(slot)
    }
    fn arg(&mut self) -> Result<Arg, String> {
        match self.peek() {
            Some(b'(') => self.node().map(Arg::Node),
            Some(b'#') => match self.s.get(self.at + 1) {
                Some(b't') => {
                    self.at += 2;
                    Ok(Arg::Flag(true))
                }
                Some(b'f') => {
                    self.at += 2;
                    Ok(Arg::Flag(false))
                }
                _ => {
                    let save = self.at;
                    self.at += 1;
                    let n = self.number()?;
                    match self.peek() {
                        Some(b'#') => {
                            self.at += 1;
                            self.labels.get(&n).map(|&s| Arg::Node(s)).ok_or(format!("label {n} not defined before"))
                        }
                        Some(b'.') => {
                            self.at += 1;
                            let pos = self.number()? as u32;
                            self.labels.get(&n).map(|&s| Arg::Bound { binder: s, pos }).ok_or(format!("binder {n} not defined before"))
                        }
                        Some(b'=') => {
                            self.at = save;
                            self.node().map(Arg::Node)
                        }
                        _ => Err(format!("`#`, `.` or `=` expected at {}", self.at)),
                    }
                }
            },
            Some(b'?') => {
                self.at += 1;
                let n = self.number()?;
                self.expect(b':')?;
                let name = self.name()?;
                if let Some(&h) = self.holes.get(&n) {
                    return Ok(h);
                }
                let h = self.b.hole(&name);
                self.holes.insert(n, h);
                Ok(h)
            }
            Some(b'<') => {
                self.at += 1;
                self.space();
                let name = self.name()?;
                self.space();
                let kind = self.name()?;
                self.space();
                let start = self.at;
                while self.peek().is_some_and(|c| c.is_ascii_hexdigit()) {
                    self.at += 1;
                }
                let key = u64::from_str_radix(std::str::from_utf8(&self.s[start..self.at]).unwrap_or(""), 16).map_err(|_| format!("a key expected at {start}"))?;
                self.space();
                self.expect(b'>')?;
                Ok(self.b.konst(Const { key, name, kind }))
            }
            Some(c) if c.is_ascii_digit() || (c == b'-' && self.s.get(self.at + 1).is_some_and(|d| d.is_ascii_digit())) => {
                let neg = c == b'-';
                if neg {
                    self.at += 1;
                }
                let v = self.number()? as i64;
                Ok(Arg::Int(if neg { -v } else { v }))
            }
            _ => {
                let s = self.name()?;
                Ok(Arg::Sym(self.b.name(&s)))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_rep_written_reads_back_as_itself() {
        let text = "#0=(poly {r} (subr <t type 00000000deadbeef> #0.0 ?0:e (base int) -3 #t |a b|))";
        let rep = read(text).expect("reads");
        assert_eq!(write(&rep), text);
        assert_eq!(read(&write(&rep)).expect("reads"), rep);
    }

    #[test]
    fn a_cycle_is_written_with_a_label() {
        let rep = read("#5=(pairof (base int) #5#)").expect("reads");
        assert_eq!(write(&rep), "#0=(pairof (base int) #0#)");
    }

    #[test]
    fn a_variable_outside_its_binder_is_refused() {
        assert!(read("(pairof #1=(poly {r} (base int)) (ref #1.0))").is_err());
    }
}
