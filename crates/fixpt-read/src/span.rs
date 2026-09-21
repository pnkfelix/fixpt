//! Source positions.
//!
//! The front ends work on Rust-side [`Syntax`](crate::Syntax) values carrying
//! spans, not on heap data. That costs a second s-expression representation,
//! and buys two things worth more: error messages that point at real source
//! text, and a compiler that never touches the collector — so no front-end code
//! can hold a stale `Value`.

use std::fmt;
use std::sync::Arc;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct FileId(pub u32);

/// A half-open byte range within one source file.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub const fn new(file: FileId, start: u32, end: u32) -> Span {
        Span { file, start, end }
    }
    /// For data built by a desugarer rather than read from a file: keeps the
    /// originating span so errors still point somewhere useful.
    pub const fn synthetic(from: Span) -> Span {
        Span { file: from.file, start: from.start, end: from.start }
    }
    pub fn join(self, other: Span) -> Span {
        debug_assert_eq!(self.file, other.file);
        Span { file: self.file, start: self.start.min(other.start), end: self.end.max(other.end) }
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}..{}", self.file.0, self.start, self.end)
    }
}

struct SourceFile {
    name: String,
    text: Arc<str>,
    /// Byte offset of the start of each line.
    line_starts: Vec<u32>,
}

/// Owns every source text the session has read, so a [`Span`] can be resolved
/// back to a file, line, column and the line's text.
#[derive(Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    pub fn new() -> SourceMap {
        SourceMap::default()
    }

    pub fn add(&mut self, name: impl Into<String>, text: impl Into<Arc<str>>) -> FileId {
        let text: Arc<str> = text.into();
        let mut line_starts = vec![0u32];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i as u32 + 1);
            }
        }
        self.files.push(SourceFile { name: name.into(), text, line_starts });
        FileId(self.files.len() as u32 - 1)
    }

    pub fn name(&self, file: FileId) -> &str {
        &self.files[file.0 as usize].name
    }
    pub fn text(&self, file: FileId) -> &str {
        &self.files[file.0 as usize].text
    }

    /// One-based line and column of a byte offset.
    pub fn line_col(&self, file: FileId, offset: u32) -> (u32, u32) {
        let f = &self.files[file.0 as usize];
        let line = match f.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let col = f.text[f.line_starts[line] as usize..offset as usize].chars().count() as u32;
        (line as u32 + 1, col + 1)
    }

    pub fn snippet(&self, span: Span) -> &str {
        let f = &self.files[span.file.0 as usize];
        &f.text[span.start as usize..span.end as usize]
    }

    /// The full source line containing `offset`, without its newline.
    pub fn line_text(&self, file: FileId, offset: u32) -> &str {
        let f = &self.files[file.0 as usize];
        let (line, _) = self.line_col(file, offset);
        let start = f.line_starts[line as usize - 1] as usize;
        let end = f
            .line_starts
            .get(line as usize)
            .map(|e| *e as usize - 1)
            .unwrap_or(f.text.len());
        &f.text[start..end.max(start)]
    }

    /// `file:line:col` — the form editors and terminals make clickable.
    pub fn describe(&self, span: Span) -> String {
        let (line, col) = self.line_col(span.file, span.start);
        format!("{}:{}:{}", self.name(span.file), line, col)
    }
}
