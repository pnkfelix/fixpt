//! Errors from the FX-91 front end.

use fixpt_read::Span;

#[derive(Clone, Debug)]
pub struct FxError {
    pub span: Span,
    pub message: String,
    pub kind: ErrorKind,
}

/// Which of the reference's two error classes this is.
///
/// `utils.scm` distinguishes `user` (a program is wrong; recoverable, returns
/// to the top level) from `fatal` (the implementation is wrong; a bug). Keeping
/// them apart matters for conformance: the goldens record a `#static-error`
/// only for the first kind.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ErrorKind {
    User,
    Fatal,
}

impl FxError {
    pub fn user(span: Span, message: impl Into<String>) -> FxError {
        FxError { span, message: message.into(), kind: ErrorKind::User }
    }
    pub fn fatal(span: Span, message: impl Into<String>) -> FxError {
        FxError { span, message: message.into(), kind: ErrorKind::Fatal }
    }
}

impl std::fmt::Display for FxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tag = match self.kind {
            ErrorKind::User => "USER ERROR",
            ErrorKind::Fatal => "FATAL ERROR",
        };
        write!(f, "{tag}: {}", self.message)
    }
}

impl std::error::Error for FxError {}

pub type R<T> = Result<T, FxError>;
