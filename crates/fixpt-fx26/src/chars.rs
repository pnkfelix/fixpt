//! Places in characters, against texts in UTF-8. The FX-26 front end
//! counts a text's places as FX-26 does, its strings UTF-32: a span the
//! Rust checker says is in characters, as `syn`'s places are
//! (`docs/research/heap-syntax.md`), and nothing converts it but what
//! holds the text it is in: a message's line and column, a piece cut out.

use fixpt_read::Span;

/// The byte where character `ch` of `text` starts; its end, if `ch` is
/// past its last.
pub fn byte_at(text: &str, ch: usize) -> usize {
    if text.is_ascii() {
        return ch.min(text.len());
    }
    text.char_indices().nth(ch).map_or(text.len(), |(b, _)| b)
}

/// How many characters of `text` are before byte `byte` (a character
/// that it is inside of counted).
pub fn char_at(text: &str, byte: usize) -> usize {
    let byte = byte.min(text.len());
    if text.is_ascii() {
        return byte;
    }
    text.char_indices().take_while(|(b, _)| *b < byte).count()
}

/// Span `span`, of `text`, its piece: by its characters.
pub fn slice(text: &str, span: Span) -> &str {
    let start = byte_at(text, span.start as usize);
    let end = byte_at(text, (span.end as usize).max(span.start as usize));
    &text[start..end]
}

/// The line and column, each from 1, of character `ch` of `text`.
pub fn line_col(text: &str, ch: usize) -> (usize, usize) {
    let before = &text[..byte_at(text, ch)];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    (line, col)
}

/// Span `span`, of bytes of `text` (the Rust reader's, an error's), in
/// its characters.
pub fn of_bytes(text: &str, span: Span) -> Span {
    Span { start: char_at(text, span.start as usize) as u32, end: char_at(text, span.end as usize) as u32, ..span }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn characters_are_not_bytes() {
        let t = "(λ x)\n(ü y)";
        assert_eq!(byte_at(t, 2), 3);
        assert_eq!(char_at(t, 3), 2);
        let s = Span { file: fixpt_read::FileId(0), start: 7, end: 12, expansion: 0 };
        assert_eq!(slice(t, s), "ü y)");
        assert_eq!(line_col(t, 8), (2, 3));
        assert_eq!(of_bytes(t, Span { start: 9, end: 14, ..s }), Span { start: 8, end: 11, ..s });
    }
}
