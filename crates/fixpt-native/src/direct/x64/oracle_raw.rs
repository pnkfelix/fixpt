//! The Rust compiler's raw pieces by name, for `super::oracle`.

use super::*;

/// The bytes piece `name` emits given `args`, and the call-outs it numbers;
/// none for a name this does not know.
pub(super) fn oracle(name: &str, args: &[i64]) -> Option<(Vec<u8>, Vec<i64>)> {
    let _ = (name, args);
    None
}
