//! The entries of the front end written in FX-26, called from Rust
//! (`TODO.md` §252): `fx26-native:NAME`, the FX-26 procedure, entered as
//! `%run-front-end` enters it (`fixpt_runtime::prim::enter_front_end`), with
//! no Scheme between. Before, each was called through a Scheme wrapper,
//! `fx26-reader:NAME`, which each session defined by evaluating its text, a
//! quarter of a debug build's start. Where the front end is lowered (no
//! `fx26-native:` entries: `FIXPT_FRONT_END_LOWERED`, the lowered reader's own),
//! `fx26-reader:NAME` is called, as before.

use crate::session::READER_PREFIX;
use crate::front::Front;
use fixpt_scheme::{Handle, SessionError};

/// Entry `name` of the front end called with `args`.
pub fn call(s: &mut Front, name: &str, args: &[Handle]) -> Result<Handle, SessionError> {
    let _phase = fixpt_memmgmt::phases::enter_named("fx:", name);
    if let Some(r) = s.call_global_with(&format!("fx26-native:{name}"), args, fixpt_runtime::prim::enter_front_end) {
        return r.map_err(SessionError::Raised);
    }
    // Lowered: loaded only by lowered code, so only where a Scheme session
    // was made (`Front::lowered`).
    let reader = format!("{READER_PREFIX}{name}");
    match s.scheme_made() {
        Some(scheme) => scheme.call_global(&reader, args),
        None => panic!("`{reader}` is not defined"),
    }
}

/// Whether entry `name` of the front end is loaded, either way.
pub fn bound(s: &Front, name: &str) -> bool {
    s.is_bound(&format!("fx26-native:{name}")) || s.is_bound(&format!("{READER_PREFIX}{name}"))
}
