//! The heap's fast paths of `direct.rs` by name (`fx_arm64::oracle`), for
//! `native-direct-arm64-flat.fx` to be checked against.

#[allow(unused_imports)]
use super::super::*;

pub(super) fn oracle(_name: &str, _args: &[i64]) -> Option<(Vec<u8>, Vec<i64>)> {
    None
}
