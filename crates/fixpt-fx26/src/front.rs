//! What an FX-26 session runs on (`TODO.md` §252): a host
//! (`fixpt_runtime::host::Host`: the runtime, its handles and globals), and,
//! only once lowered code is to run, a Scheme session made on that same
//! host ([`Front::lowered`]), kept from then on. The front end written in
//! FX-26 is entered from Rust (`crate::entries`), and what it compiles is
//! run by the runtime's machines, so a session that runs no lowered code
//! makes no Scheme engine and evaluates no Scheme. `Front` has no way to
//! evaluate Scheme itself: only `lowered` gives a Scheme session, and it
//! gives one ready (`session::scheme_ready`), so that no path can evaluate
//! Scheme without the prelude and FX-26's runtime in it.

use fixpt_engine::Backend;
use fixpt_runtime::host::{Handle, Host};
use fixpt_scheme::{Session, SessionError};

/// A host, and the Scheme session made on it once lowered code runs.
pub struct Front {
    inner: Inner,
    /// The engine a Scheme session is made with, when it is.
    backend: Backend,
    /// The engine's step limit, given it when made, and kept in it after.
    step_limit: Option<u64>,
    /// Whether the engine says a failure without its irritants
    /// (`Session::bare_failures`), the same way.
    bare_failures: bool,
}

enum Inner {
    Host(Box<Host>),
    Scheme(Box<Session>),
    /// Only while a host becomes a session (`lowered`).
    Moving,
}

impl std::ops::Deref for Front {
    type Target = Host;
    fn deref(&self) -> &Host {
        match &self.inner {
            Inner::Host(h) => h,
            Inner::Scheme(s) => s,
            Inner::Moving => unreachable!("a host being made a session"),
        }
    }
}

impl std::ops::DerefMut for Front {
    fn deref_mut(&mut self) -> &mut Host {
        match &mut self.inner {
            Inner::Host(h) => h,
            Inner::Scheme(s) => s,
            Inner::Moving => unreachable!("a host being made a session"),
        }
    }
}

impl Front {
    /// On `host`; a Scheme session, when one is made, with `backend`.
    pub fn new(backend: Backend, host: Host) -> Front {
        Front { inner: Inner::Host(Box::new(host)), backend, step_limit: None, bare_failures: false }
    }

    /// Run `f`; the handles it makes are released when it returns, as
    /// [`Host::scope`] does, but `f` gets the front, session and all.
    pub fn scope<R>(&mut self, f: impl FnOnce(&mut Front) -> R) -> R {
        let depth = self.root_mark();
        let r = f(self);
        self.release_to(depth);
        r
    }

    /// The Scheme session, made on this host the first time, and ready to
    /// run lowered code: the prelude and FX-26's runtime in Scheme loaded
    /// (`session::scheme_ready`). The only way to one.
    pub fn lowered(&mut self) -> &mut Session {
        if let Inner::Host(_) = self.inner {
            let Inner::Host(host) = std::mem::replace(&mut self.inner, Inner::Moving) else { unreachable!() };
            let mut s = Session::on_host(self.backend, *host);
            s.engine.set_step_limit(self.step_limit);
            s.bare_failures = self.bare_failures;
            self.inner = Inner::Scheme(Box::new(s));
        }
        let Inner::Scheme(s) = &mut self.inner else { unreachable!("made above") };
        crate::session::scheme_ready(s).expect("the prelude and FX-26's runtime must load");
        s
    }

    /// The Scheme session, if lowered code has made one: for what calls
    /// lowered code that only such a session can have loaded (the front end
    /// lowered, `crate::entries`).
    pub fn scheme_made(&mut self) -> Option<&mut Session> {
        match &mut self.inner {
            Inner::Scheme(s) => Some(s),
            _ => None,
        }
    }

    /// The Scheme engine's step limit: for lowered code, as the machines'
    /// fuel is for compiled code.
    pub fn set_step_limit(&mut self, limit: Option<u64>) {
        self.step_limit = limit;
        if let Inner::Scheme(s) = &mut self.inner {
            s.engine.set_step_limit(limit);
        }
    }

    pub fn step_limit(&self) -> Option<u64> {
        self.step_limit
    }

    /// Whether lowered code's failures are said without their irritants,
    /// as FX-26's machines say them.
    pub fn set_bare_failures(&mut self, bare: bool) {
        self.bare_failures = bare;
        if let Inner::Scheme(s) = &mut self.inner {
            s.bare_failures = bare;
        }
    }

    /// `word`, a cellular word or closure, run with `args` on the runtime's
    /// machine, as `%run-word` runs it, with no engine between.
    pub fn run_word(&mut self, word: Handle, args: &[Handle]) -> Result<Handle, SessionError> {
        self.call_handle_with(word, args, fixpt_runtime::prim::enter_word).map_err(SessionError::Raised)
    }

    /// `word` run as [`run_word`](Self::run_word) runs it, its arguments the
    /// list `args` roots: as `(%run-word word args)` is called.
    pub fn run_word_on(&mut self, word: Handle, args: Handle) -> Result<Handle, SessionError> {
        self.call_handle_with(word, &[args], |rt, w, a| {
            let args = rt.heap.list_to_vec(a[0]).ok_or("a list of arguments is expected")?;
            fixpt_runtime::prim::enter_word(rt, w, &args)
        })
        .map_err(SessionError::Raised)
    }

    /// A list of what `items` root, as `list` makes it.
    pub fn list(&mut self, items: &[Handle]) -> Result<Handle, SessionError> {
        Ok(self.make(|m| {
            let vs: Vec<fixpt_heap::Value> = items.iter().map(|h| m.get(*h)).collect();
            m.heap().list_from(&vs)
        }))
    }

    /// `word` run as the front end's code is (`%run-front-end`), with
    /// `args`.
    pub fn run_front_end(&mut self, word: Handle, args: &[Handle]) -> Result<Handle, SessionError> {
        self.call_handle_with(word, args, fixpt_runtime::prim::enter_front_end).map_err(SessionError::Raised)
    }
}
