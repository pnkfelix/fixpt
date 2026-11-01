//! A lint: a bloblet's field named by a number, not by its layout (the
//! user's, 2026-11-01; `TODO.md` §205).
//!
//! A bloblet's fields are counted back from its suffix, from 1, and the
//! trailer, where there is one, is field 1; its *values*, as
//! `make_frozen` takes them, are counted from 0, after the trailer. So value
//! `i` is field `i + 2` of an FX-26 sum or product, and field `i + 1` of a
//! bloblet without a trailer. Crossing that by hand went wrong more than
//! once (a product's fields read one off; a rep's tag read from the
//! trailer). Code over values says what it means instead: `bloblet_value`,
//! `bloblet_len`, `product_field`, `sum_tag`, `sum_payload`
//! (`fixpt_heap::Heap`).
//!
//! What is left to the field accessors (`bloblet_slot`, `set_bloblet_slot`,
//! `bloblet_field`, `set_bloblet_field`) is the fixed layouts, each field
//! named by a constant of its layout (`CLOSURE_WORD`, `GLOBAL_NAME`), with
//! an offset from one if need be (`CLOSURE_FREE0 + i`). So the lint: the
//! index such a call is given starts with a constant's name, an
//! upper-case identifier, perhaps by its path; a number, a variable or
//! arithmetic on them is a finding. And a field count compared or
//! offset by a number (`bloblet_head(v).fields == 7`), which `bloblet_len`
//! says.
//!
//! A field by number on purpose (an instruction's operand, which the
//! compilers make a field's number; a primitive given one by a program)
//! says so where it is written: its line, or the line before, carries
//! `// fields:` and why. Files whose whole business is fields (the heap's
//! own) are listed, with why, in `raw-fields-allowed.txt`.

/// A call that names a field by number.
#[derive(Clone, Debug, PartialEq)]
pub struct Finding {
    pub line: usize,
    /// What was written: the accessor and its index.
    pub what: String,
}

/// What marks a field by number kept on purpose.
pub const KEEP: &str = "// fields:";

/// The accessors, each with where its index is among its arguments.
const ACCESSORS: [(&str, usize); 5] =
    [("set_bloblet_slot", 1), ("bloblet_slot", 1), ("set_bloblet_field", 1), ("bloblet_field", 1), ("raw_field", 0)];

/// The findings in Rust source `src`. Lines that are comments are skipped,
/// and lines kept on purpose ([`KEEP`]).
pub fn findings(src: &str) -> Vec<Finding> {
    let mut out = Vec::new();
    let lines: Vec<&str> = src.lines().collect();
    for (n, &line) in lines.iter().enumerate() {
        let before = if n > 0 { lines[n - 1].trim_start() } else { "" };
        if line.trim_start().starts_with("//") || line.contains(KEEP) || before.starts_with(KEEP) {
            continue;
        }
        let code = line.split(" // ").next().unwrap_or(line);
        let mut at = 0;
        while let Some(k) = code[at..].find('.') {
            let dot = at + k;
            at = dot + 1;
            let rest = &code[dot + 1..];
            let Some(&(name, at_arg)) = ACCESSORS.iter().find(|(a, _)| rest.starts_with(&format!("{a}("))) else {
                if rest.starts_with("fields") && counted(&rest["fields".len()..]) && code[..dot].ends_with(')') {
                    out.push(Finding { line: n + 1, what: format!(".fields{}", first_token(&rest["fields".len()..])) });
                }
                continue;
            };
            let args = &rest[name.len() + 1..];
            if let Some(index) = argument(args, at_arg) {
                if !named(index) {
                    out.push(Finding { line: n + 1, what: format!("{name}(…, {index})") });
                }
            }
        }
    }
    out
}

/// Argument `n` (from 0) of those that start `args` (just after the open
/// parenthesis), if they close on this line.
fn argument(args: &str, n: usize) -> Option<&str> {
    let (mut depth, mut start, mut at) = (0i32, 0, 0);
    for (i, c) in args.char_indices() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' if depth == 0 => return (at == n).then(|| args[start..i].trim()),
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                if at == n {
                    return Some(args[start..i].trim());
                }
                (at, start) = (at + 1, i + 1);
            }
            _ => {}
        }
    }
    None
}

/// Whether `index` starts with a constant's name: an upper-case identifier,
/// perhaps after a path (`layout::cellular::CLOSURE_WORD`), and then
/// nothing, or an offset (`+ i`, `- 1`).
fn named(index: &str) -> bool {
    let mut s = index;
    while let Some(k) = s.find("::") {
        if !s[..k].chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_') {
            break;
        }
        s = &s[k + 2..];
    }
    let end = s.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(s.len());
    let (ident, after) = (&s[..end], s[end..].trim_start());
    ident.starts_with(|c: char| c.is_ascii_uppercase())
        && ident.chars().all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
        && (after.is_empty() || after.starts_with('+') || after.starts_with('-'))
}

/// Whether what follows `.fields` compares it with a number or offsets it
/// by one: `== 7`, `- 1`, `>= 2`.
fn counted(after: &str) -> bool {
    let s = after.trim_start();
    let op = ["==", "!=", ">=", "<=", "-", "+", ">", "<"].iter().find(|o| s.starts_with(**o));
    op.is_some_and(|o| s[o.len()..].trim_start().starts_with(|c: char| c.is_ascii_digit()))
}

fn first_token(after: &str) -> String {
    let s = after.trim_start();
    let end = s.find(|c: char| c == ')' || c == ';' || c == ',' || c == '&' || c == '|').unwrap_or(s.len());
    format!(" {}", s[..end].trim())
}

/// The allowed files: each line a path from the repository's root (a
/// directory's, ending in `/`, allows all under it), then ` — ` and why;
/// `#` begins a comment.
pub fn parse_allowed(text: &str) -> Vec<String> {
    text.lines()
        .map(|l| l.split('#').next().unwrap_or("").trim())
        .filter(|l| !l.is_empty())
        .map(|l| l.split(" — ").next().unwrap_or(l).trim().to_string())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn whats(src: &str) -> Vec<String> {
        findings(src).into_iter().map(|f| f.what).collect()
    }

    #[test]
    fn a_number_or_a_variable_is_a_finding() {
        assert_eq!(whats("let x = h.bloblet_slot(v, 2);"), ["bloblet_slot(…, 2)"]);
        assert_eq!(whats("h.set_bloblet_slot(b, i + 2, *v);"), ["set_bloblet_slot(…, i + 2)"]);
        assert_eq!(whats("rt.heap.bloblet_field(o, k)"), ["bloblet_field(…, k)"]);
        assert_eq!(whats("v.get(r).raw_field(2).and_then(f)"), ["raw_field(…, 2)"]);
    }

    #[test]
    fn a_layout_constant_is_not() {
        assert!(whats("h.bloblet_slot(c, CLOSURE_WORD)").is_empty());
        assert!(whats("h.set_bloblet_slot(c, CLOSURE_FREE0 + i, *v);").is_empty());
        assert!(whats("h.bloblet_slot(a, crate::sched::ICELL_FULL)").is_empty());
        assert!(whats("h.bloblet_slot(a, fixpt_heap::layout::cellular::WORD_NAME)").is_empty());
    }

    #[test]
    fn a_count_by_number_is_a_finding() {
        assert_eq!(whats("h.bloblet_head(v).fields == 7 &&"), [".fields == 7"]);
        assert_eq!(whats("let n = h.bloblet_head(b).fields - 1;"), [".fields - 1"]);
        assert!(whats("h.bloblet_head(v).fields < GLOBAL_FIELDS").is_empty());
        assert!(whats("Head { fields: 2 }").is_empty());
    }

    #[test]
    fn a_field_kept_on_purpose_says_so() {
        assert!(whats("h.bloblet_slot(code, k) // fields: the instruction's operand").is_empty());
        assert!(whats("// fields: the instruction's operand\nh.bloblet_slot(code, k)").is_empty());
        assert_eq!(whats("// why\nh.bloblet_slot(code, k)").len(), 1);
    }

    #[test]
    fn comments_and_definitions_are_not_calls() {
        assert!(whats("    /// `h.bloblet_slot(v, 2)` reads the tag").is_empty());
        assert!(whats("pub fn bloblet_slot(&self, v: Value, k: usize) -> Value {").is_empty());
    }
}
