//! Errors, in the reference's own words.
//!
//! `desc-of-exp` reports every checking failure the same way — `uerror
//! "Cannot type-check" (unparse-node node)` — so the message is the unparsed
//! form and nothing else. The goldens record exactly that string, which makes
//! matching it a conformance requirement rather than a courtesy.

use fixpt_read::Span;

#[derive(Clone, Debug)]
pub struct FxError {
    pub span: Span,
    pub message: String,
    /// A `#static-error` in the goldens, as opposed to something going wrong
    /// in the checker itself.
    pub user: bool,
}

impl FxError {
    /// What the reference says when a form does not type-check.
    pub fn cannot_type_check(span: Span, unparsed: &str) -> FxError {
        FxError { span, message: format!("Cannot type-check {unparsed}"), user: true }
    }

    pub fn syntax(span: Span, message: impl Into<String>) -> FxError {
        FxError { span, message: message.into(), user: true }
    }

    pub fn internal(span: Span, message: impl Into<String>) -> FxError {
        FxError { span, message: message.into(), user: false }
    }
}

impl std::fmt::Display for FxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for FxError {}

pub type R<T> = Result<T, FxError>;
