//! Checks on the repository itself, run as ordinary tests (`tests/`).
//!
//! Two checks. **FX program files stay small** ([`fx_size`]). And **a Scheme or FX program longer than a few lines does not
//! live inside a Rust string literal.** A short snippet inline is the clearest
//! way to write a test — the program and what it should do side by side — but
//! past a few lines the string loses everything a source file has: an editor
//! mode, a way to load it into the REPL, and indentation that belongs to the
//! program rather than to the Rust around it. So a snippet longer than
//! [`MAX_LINES`] lines or [`MAX_CHARS`] characters, whichever comes first,
//! moves to a file beside its test and comes back with `include_str!`.
//!
//! The limit applies to the snippet as it would stand in that file: blank
//! lines at either end dropped, and the indentation it shares with the Rust
//! around it removed. So moving code between Rust nesting depths never moves
//! it across the limit.
//!
//! What counts as a snippet is a string literal whose first non-blank
//! character opens a datum — `(`, `[`, `#`, `'`, `` ` `` — or a comment, `;`.
//! That is a guess about intent, not a parse: a long printed value such as
//! `#<closure …>` counts too, which is intended.

pub mod fx_size;
pub mod recursion;
pub mod sexp_edit;

use std::path::{Path, PathBuf};

/// A snippet longer than this many lines belongs in a file.
pub const MAX_LINES: usize = 4;

/// A snippet longer than this many characters belongs in a file.
pub const MAX_CHARS: usize = 240;

/// A string literal in Rust source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Literal {
    /// 1-based line of the opening quote.
    pub line: usize,
    /// 0-based column, in characters, where the contents start.
    pub column: usize,
    /// The contents, escapes decoded.
    pub text: String,
}

/// Every string literal in `src`, skipping comments and character literals.
pub fn literals(src: &str) -> Vec<Literal> {
    let cs: Vec<char> = src.chars().collect();
    let at = |k: usize| cs.get(k).copied().unwrap_or('\0');
    let ident = |k: usize| k > 0 && (cs[k - 1].is_alphanumeric() || cs[k - 1] == '_');
    let mut out = Vec::new();
    let (mut i, mut line, mut line_start) = (0, 1, 0);
    // Step over one character, keeping `line` and `line_start` current.
    macro_rules! bump {
        () => {{
            if cs[i] == '\n' {
                line += 1;
                line_start = i + 1;
            }
            i += 1;
        }};
    }
    while i < cs.len() {
        let c = cs[i];
        if c == '/' && at(i + 1) == '/' {
            while i < cs.len() && cs[i] != '\n' {
                i += 1;
            }
        } else if c == '/' && at(i + 1) == '*' {
            let mut depth = 0;
            loop {
                if i >= cs.len() {
                    break;
                } else if cs[i] == '/' && at(i + 1) == '*' {
                    depth += 1;
                    i += 2;
                } else if cs[i] == '*' && at(i + 1) == '/' {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    bump!();
                }
            }
        } else if c == '\'' {
            // A character literal, or else a lifetime or label.
            if at(i + 1) == '\\' {
                i += 2;
                while i < cs.len() && cs[i] != '\'' {
                    i += 1;
                }
                i += 1;
            } else if at(i + 2) == '\'' {
                i += 3;
            } else {
                i += 1;
            }
        } else if let Some(hashes) = raw_prefix(&cs, i).filter(|_| !ident(i)) {
            // `r"…"`, `r#"…"#`, `br"…"`: no escapes, ends at `"` plus hashes.
            let (open_line, mut j) = (line, i);
            while cs[j] != '"' {
                j += 1;
            }
            i = j + 1;
            let column = i - line_start;
            let start = i;
            while i < cs.len() && !(cs[i] == '"' && (1..=hashes).all(|h| at(i + h) == '#')) {
                bump!();
            }
            out.push(Literal { line: open_line, column, text: cs[start..i].iter().collect() });
            i += 1 + hashes;
        } else if c == '"' || ((c == 'b' || c == 'c') && at(i + 1) == '"' && !ident(i)) {
            let open_line = line;
            i += if c == '"' { 1 } else { 2 };
            let mut column = i - line_start;
            let mut text = String::new();
            while i < cs.len() && cs[i] != '"' {
                if cs[i] != '\\' {
                    text.push(cs[i]);
                    bump!();
                    continue;
                }
                let e = at(i + 1);
                i += 2;
                match e {
                    // A line continuation swallows the newline and the
                    // indentation after it.
                    '\n' => {
                        line += 1;
                        line_start = i;
                        while i < cs.len() && cs[i].is_whitespace() {
                            bump!();
                        }
                        // `"\` then a newline: the text starts on this line.
                        if text.is_empty() {
                            column = i - line_start;
                        }
                    }
                    'n' => text.push('\n'),
                    't' => text.push('\t'),
                    'r' => text.push('\r'),
                    '0' => text.push('\0'),
                    'x' => {
                        let hex: String = cs[i..i + 2].iter().collect();
                        text.push(u8::from_str_radix(&hex, 16).map_or('?', char::from));
                        i += 2;
                    }
                    'u' => {
                        let close = (i..cs.len()).find(|&k| cs[k] == '}').unwrap_or(i);
                        let hex: String = cs[i + 1..close].iter().collect();
                        text.push(u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32).unwrap_or('?'));
                        i = close + 1;
                    }
                    other => text.push(other),
                }
            }
            i += 1;
            out.push(Literal { line: open_line, column, text });
        } else {
            bump!();
        }
    }
    out
}

/// At `i`, the start of a raw string: the number of `#`s it uses.
fn raw_prefix(cs: &[char], i: usize) -> Option<usize> {
    let mut j = i;
    if matches!(cs.get(j), Some('b' | 'c')) {
        j += 1;
    }
    if cs.get(j) != Some(&'r') {
        return None;
    }
    j += 1;
    let hashes = cs[j..].iter().take_while(|&&c| c == '#').count();
    (cs.get(j + hashes) == Some(&'"')).then_some(hashes)
}

/// The snippet a literal holds, as it would stand in a file of its own: `None`
/// when the literal does not look like code.
pub fn snippet(lit: &Literal) -> Option<String> {
    let first = lit.text.trim_start().chars().next()?;
    if !"([#'`;".contains(first) {
        return None;
    }
    // Put the first line back at the column it starts at, so that it dedents
    // together with the lines under it.
    let placed = format!("{}{}", " ".repeat(lit.column), lit.text);
    let mut lines: Vec<&str> = placed.lines().map(str::trim_end).collect();
    while lines.first().is_some_and(|l| l.is_empty()) {
        lines.remove(0);
    }
    while lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    let indent = |l: &&str| l.len() - l.trim_start().len();
    let common = lines.iter().filter(|l| !l.is_empty()).map(indent).min().unwrap_or(0);
    let dedented: Vec<&str> = lines.iter().map(|l| l.get(common..).unwrap_or("")).collect();
    Some(dedented.join("\n"))
}

/// A snippet over the limit.
#[derive(Debug)]
pub struct Violation {
    pub file: PathBuf,
    pub line: usize,
    pub lines: usize,
    pub chars: usize,
}

impl std::fmt::Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}: a {}-line, {}-character snippet (the limit is {MAX_LINES} lines or \
             {MAX_CHARS} characters)",
            self.file.display(),
            self.line,
            self.lines,
            self.chars
        )
    }
}

/// The over-long snippets in one file's source.
pub fn check_source(file: &Path, src: &str) -> Vec<Violation> {
    literals(src)
        .iter()
        .filter_map(|lit| {
            let s = snippet(lit)?;
            let (lines, chars) = (s.lines().count(), s.chars().count());
            (lines > MAX_LINES || chars > MAX_CHARS).then(|| Violation {
                file: file.to_path_buf(),
                line: lit.line,
                lines,
                chars,
            })
        })
        .collect()
}

/// Every `.rs` file under `dir`, skipping build output.
pub fn rust_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else { continue };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                if path.file_name().is_some_and(|n| n != "target") {
                    stack.push(path);
                }
            } else if path.extension().is_some_and(|e| e == "rs") {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn texts(src: &str) -> Vec<String> {
        literals(src).into_iter().map(|l| l.text).collect()
    }

    #[test]
    fn comments_chars_and_lifetimes_are_not_strings() {
        let src = "// \"no\"\n/* \"no\" /* \"nested\" */ */ fn f<'a>(c: char) { '\"'; \"yes\" }";
        assert_eq!(texts(src), ["yes"]);
    }

    #[test]
    fn escapes_and_raw_strings_decode() {
        assert_eq!(texts(r####"x("a\"b\\n\n", r#"(c "d")"#, b"e")"####), ["a\"b\\n\n", "(c \"d\")", "e"]);
        assert_eq!(texts("\"a\\\n     b\""), ["ab"]);
    }

    #[test]
    fn a_snippet_is_dedented_against_its_first_line() {
        let src = "    f(\"(define x\n         1)\n       (g x)\")";
        let lit = &literals(src)[0];
        assert_eq!(snippet(lit).as_deref(), Some("(define x\n  1)\n(g x)"));
        assert_eq!(literals(src)[0].line, 1);
        // A leading line continuation puts the text at its own column.
        let lit = &literals("    f(\"\\\n(a\n (b))\")")[0];
        assert_eq!(snippet(lit).as_deref(), Some("(a\n (b))"));
    }

    #[test]
    fn prose_is_not_a_snippet() {
        let lit = &literals("f(\"no rule of `m` matches\")")[0];
        assert_eq!(snippet(lit), None);
    }

    #[test]
    fn the_limit_is_lines_or_characters_whichever_comes_first() {
        let five = format!("\"{}\"", ["(a)"; 5].join("\n"));
        assert_eq!(check_source(Path::new("t.rs"), &five).len(), 1);
        let four = format!("\"{}\"", ["(a)"; 4].join("\n"));
        assert!(check_source(Path::new("t.rs"), &four).is_empty());
        let wide = format!("\"({})\"", "x".repeat(MAX_CHARS));
        assert_eq!(check_source(Path::new("t.rs"), &wide).len(), 1);
    }
}
