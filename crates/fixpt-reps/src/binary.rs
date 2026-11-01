//! A rep's binary form (`heap-types.md`, "Serialization"): what a `.fasl`'s
//! header, a cache, or a stream between processes holds. A rep's tables as
//! they are, counts and indices as variable-length integers, so that
//! reading one is reading integers:
//!
//! ```text
//! "FXR1"
//! names:  count, how many of them the nodes' (the rest the holes' and
//!         the constants'), each its length and bytes (UTF-8)
//! holes:  count, each a name's index
//! consts: count, each its key (8 bytes, little-endian), a name's index, a kind's index
//! nodes:  count, each its head's index; a byte, 1 if it is a set; its
//!         binders: count, each a name's index; its operands: count, each a
//!         tag byte and its value
//! ```
//!
//! The operands' tags: 0 a node, 1 a bound variable (binder, place), 2 a
//! hole, 3 a constant, 4 a name, 5 an integer (zigzag), 6 a flag (0 or 1).

use crate::{Arg, Const, Node, Rep};

const MAGIC: &[u8; 4] = b"FXR1";

/// Rep `rep`, in its binary form.
pub fn encode(rep: &Rep) -> Vec<u8> {
    let mut out = MAGIC.to_vec();
    let mut names: Vec<&str> = rep.names.iter().map(String::as_str).collect();
    // A constant's kind is a name too, kept with the rest.
    let mut kind_ids = Vec::new();
    for c in &rep.consts {
        let i = names.iter().position(|n| *n == c.kind).unwrap_or_else(|| {
            names.push(&c.kind);
            names.len() - 1
        });
        kind_ids.push(i);
    }
    let mut const_names = Vec::new();
    for c in &rep.consts {
        let i = names.iter().position(|n| *n == c.name).unwrap_or_else(|| {
            names.push(&c.name);
            names.len() - 1
        });
        const_names.push(i);
    }
    let mut hole_names = Vec::new();
    for h in &rep.holes {
        let i = names.iter().position(|n| *n == h).unwrap_or_else(|| {
            names.push(h);
            names.len() - 1
        });
        hole_names.push(i);
    }
    uint(&mut out, names.len() as u64);
    uint(&mut out, rep.names.len() as u64);
    for n in &names {
        uint(&mut out, n.len() as u64);
        out.extend_from_slice(n.as_bytes());
    }
    uint(&mut out, hole_names.len() as u64);
    hole_names.iter().for_each(|&i| uint(&mut out, i as u64));
    uint(&mut out, rep.consts.len() as u64);
    for (k, c) in rep.consts.iter().enumerate() {
        out.extend_from_slice(&c.key.to_le_bytes());
        uint(&mut out, const_names[k] as u64);
        uint(&mut out, kind_ids[k] as u64);
    }
    uint(&mut out, rep.nodes.len() as u64);
    for node in &rep.nodes {
        uint(&mut out, node.head as u64);
        out.push(node.set as u8);
        uint(&mut out, node.binders.len() as u64);
        node.binders.iter().for_each(|&b| uint(&mut out, b as u64));
        uint(&mut out, node.args.len() as u64);
        for a in &node.args {
            match *a {
                Arg::Node(i) => tagged(&mut out, 0, i as u64),
                Arg::Bound { binder, pos } => {
                    tagged(&mut out, 1, binder as u64);
                    uint(&mut out, pos as u64);
                }
                Arg::Hole(i) => tagged(&mut out, 2, i as u64),
                Arg::Const(i) => tagged(&mut out, 3, i as u64),
                Arg::Sym(i) => tagged(&mut out, 4, i as u64),
                Arg::Int(k) => tagged(&mut out, 5, ((k << 1) ^ (k >> 63)) as u64),
                Arg::Flag(b) => tagged(&mut out, 6, b as u64),
            }
        }
    }
    out
}

/// The rep in `bytes`, its binary form; or why not. Validated whether or not
/// `validate` is asked (a rep is read whole, and its indices must be in
/// range for it to be a value at all); `validate` also checks that every
/// bound variable is under its binder ([`Rep::validate`]), which a rep from
/// the trusted pieces is by construction.
pub fn decode(bytes: &[u8], validate: bool) -> Result<Rep, String> {
    let mut r = Reader { bytes, at: 0 };
    if r.take(4)? != MAGIC {
        return Err("not a rep (no `FXR1`)".into());
    }
    let count = |r: &mut Reader| -> Result<usize, String> {
        let n = r.uint()? as usize;
        // No count larger than what is left, at a byte an item at least.
        if n > r.bytes.len() - r.at {
            return Err("a count past the end".into());
        }
        Ok(n)
    };
    let nnames = count(&mut r)?;
    let own = r.uint()? as usize;
    if own > nnames {
        return Err("more of the nodes' names than names".into());
    }
    let mut names = Vec::with_capacity(nnames);
    for _ in 0..nnames {
        let len = count(&mut r)?;
        names.push(std::str::from_utf8(r.take(len)?).map_err(|_| "a name not UTF-8")?.to_string());
    }
    let name = |i: u64| -> Result<String, String> { names.get(i as usize).cloned().ok_or_else(|| format!("name {i} out of range")) };
    let nholes = count(&mut r)?;
    let mut holes = Vec::with_capacity(nholes);
    for _ in 0..nholes {
        holes.push(name(r.uint()?)?);
    }
    let nconsts = count(&mut r)?;
    let mut consts = Vec::with_capacity(nconsts);
    for _ in 0..nconsts {
        let key = u64::from_le_bytes(r.take(8)?.try_into().expect("8 bytes"));
        let (n, k) = (name(r.uint()?)?, name(r.uint()?)?);
        consts.push(Const { key, name: n, kind: k });
    }
    let nnodes = count(&mut r)?;
    let mut nodes = Vec::with_capacity(nnodes);
    for _ in 0..nnodes {
        let head = r.uint()? as u32;
        let set = match r.take(1)?[0] {
            0 => false,
            1 => true,
            b => return Err(format!("a node's set byte {b}")),
        };
        let nb = count(&mut r)?;
        let binders = (0..nb).map(|_| r.uint().map(|b| b as u32)).collect::<Result<_, _>>()?;
        let na = count(&mut r)?;
        let mut args = Vec::with_capacity(na);
        for _ in 0..na {
            let tag = r.take(1)?[0];
            let v = r.uint()?;
            args.push(match tag {
                0 => Arg::Node(v as u32),
                1 => Arg::Bound { binder: v as u32, pos: r.uint()? as u32 },
                2 => Arg::Hole(v as u32),
                3 => Arg::Const(v as u32),
                4 => Arg::Sym(v as u32),
                5 => Arg::Int(((v >> 1) as i64) ^ -((v & 1) as i64)),
                6 => Arg::Flag(v != 0),
                t => return Err(format!("an operand's tag {t}")),
            });
        }
        nodes.push(Node { head, binders, args, set });
    }
    if r.at != bytes.len() {
        return Err("bytes past the rep".into());
    }
    names.truncate(own);
    let rep = Rep { nodes, names, holes, consts };
    // Indices in range always; the binders' scopes if asked.
    match (rep.validate(), validate) {
        (Ok(()), _) => Ok(rep),
        (Err(e), true) => Err(e),
        (Err(e), false) if e.contains("out of range") || e.contains("no nodes") => Err(e),
        (Err(_), false) => Ok(rep),
    }
}

fn uint(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

fn tagged(out: &mut Vec<u8>, tag: u8, v: u64) {
    out.push(tag);
    uint(out, v);
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn take(&mut self, n: usize) -> Result<&[u8], String> {
        let end = self.at.checked_add(n).filter(|&e| e <= self.bytes.len()).ok_or("the rep ends early")?;
        let s = &self.bytes[self.at..end];
        self.at = end;
        Ok(s)
    }
    fn uint(&mut self) -> Result<u64, String> {
        let mut v = 0u64;
        for shift in (0..64).step_by(7) {
            let b = self.take(1)?[0];
            v |= ((b & 0x7f) as u64) << shift;
            if b & 0x80 == 0 {
                return Ok(v);
            }
        }
        Err("an integer too long".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Builder;

    #[test]
    fn a_rep_reads_back_as_itself() {
        let mut b = Builder::new();
        let int = b.name("int");
        let base = b.add("base", &[], vec![Arg::Sym(int)]);
        let h = b.hole("e");
        let c = b.konst(Const { key: 0xdead_beef, name: "t".into(), kind: "type".into() });
        let poly = b.reserve();
        let f = b.add("subr", &[], vec![h, Arg::Node(base), c, Arg::Bound { binder: poly, pos: 0 }, Arg::Int(-3), Arg::Flag(true)]);
        b.fill(poly, "poly", &["r"], vec![Arg::Node(f)]);
        let rep = b.finish(poly).expect("finishes").rep;
        let bytes = encode(&rep);
        assert_eq!(decode(&bytes, true).expect("decodes"), rep);
    }

    #[test]
    fn what_is_no_rep_is_refused() {
        assert!(decode(b"FXR1\x05", true).is_err());
        assert!(decode(b"nope", true).is_err());
    }
}
