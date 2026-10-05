//! Values for code outside the runtime: handles, scopes and views.
//!
//! A `Value` is a pointer the collector moves, and anything that may
//! collect (every call into the engine, every evaluation) leaves a Value
//! held across it stale. Code driving a session never holds one:
//!
//! * what a session hands out is a [`Handle`], rooted, so it survives
//!   collections, and stamped, so using one after the [`Session::scope`]
//!   that made it has ended is refused rather than misread;
//! * a heap's contents are read only in [`Session::view`], whose [`Local`]s
//!   cannot leave the closure, and which borrows the session immutably, so
//!   nothing in it can collect;
//! * Values are built only in [`Session::make`], whose closure cannot call
//!   the engine, and whose result is rooted as it returns.
//!
//! The runtime itself is behind [`Session::runtime_unrooted`], for code that
//! is part of the machinery; its name says what it gives up.
//!
//! This is the discipline V8's `HandleScope` and `Local`, and JNI's local
//! references, keep; in effect-system terms, the heap is a region, a Local
//! is a read of it scoped to the view, and a call that may collect is the
//! effect that ends it.

use super::Session;
use fixpt_heap::{Heap, ObjType, Value};
use fixpt_runtime::Runtime;

/// A rooted Value: valid across collections, until its scope ends.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Handle {
    index: u32,
    stamp: u32,
}

impl Session {
    /// Root `v` as a new handle. `v` must be a Value from just now: from
    /// `make`, or from the engine's result before anything else ran.
    pub(super) fn root_value(&mut self, v: Value) -> Handle {
        let index = self.rt.heap.push_root(v);
        if self.handle_stamps.len() <= index {
            self.handle_stamps.resize(index + 1, 0);
        }
        self.next_stamp = self.next_stamp.wrapping_add(1).max(1);
        self.handle_stamps[index] = self.next_stamp;
        Handle { index: index as u32, stamp: self.next_stamp }
    }

    /// The Value a handle roots, now; for this module's callers, which use
    /// it at once.
    pub(super) fn handle_value(&self, h: Handle) -> Value {
        let i = h.index as usize;
        assert!(
            i < self.rt.heap.root_count() && self.handle_stamps.get(i) == Some(&h.stamp),
            "a handle used after its scope ended"
        );
        self.rt.heap.root_at(i)
    }

    /// How deep the explicit roots are now: for [`release_to`](Session::release_to),
    /// where a [`scope`](Session::scope) cannot be used (its caller owns
    /// more than the session).
    pub fn root_mark(&self) -> usize {
        self.rt.heap.root_count()
    }

    /// Release the handles made, and the roots pushed, since `mark`
    /// ([`root_mark`](Session::root_mark)), as the end of a scope does.
    pub fn release_to(&mut self, mark: usize) {
        self.rt.heap.pop_roots_to(mark);
        self.handle_stamps.truncate(mark);
    }

    /// Run `f`; the handles it makes are released when it returns (so are
    /// any roots anything in it pushed). Keep what `f` computes as Rust data
    /// or as handles made before the scope.
    pub fn scope<R>(&mut self, f: impl FnOnce(&mut Session) -> R) -> R {
        let depth = self.rt.heap.root_count();
        let r = f(self);
        self.rt.heap.pop_roots_to(depth);
        self.handle_stamps.truncate(depth);
        r
    }

    /// Look at the heap: `f` gets a view, whose `Local`s cannot leave it,
    /// and cannot run anything that collects.
    pub fn view<R>(&self, f: impl for<'v> FnOnce(View<'v>) -> R) -> R {
        f(View { session: self })
    }

    /// Build a Value: `f` gets the heap, whose allocation never collects,
    /// and the Values handles root, for the moment; what it returns is
    /// rooted as a handle.
    pub fn make(&mut self, f: impl FnOnce(&mut Maker) -> Value) -> Handle {
        let v = {
            let mut m = Maker { session: self };
            f(&mut m)
        };
        self.root_value(v)
    }

    /// Make `h` root what `f` builds instead.
    pub fn replace(&mut self, h: Handle, f: impl FnOnce(&mut Maker) -> Value) {
        let _ = self.handle_value(h);
        let v = {
            let mut m = Maker { session: self };
            f(&mut m)
        };
        self.rt.heap.set_root_at(h.index as usize, v);
    }

    /// The written form of what `h` roots, as `write` would print it.
    pub fn write(&self, h: Handle) -> String {
        self.view(|v| v.get(h).write())
    }

    /// What `h` roots, as `display` would print it.
    pub fn display(&self, h: Handle) -> String {
        self.view(|v| v.get(h).display())
    }

    // Value-free access: what holds no heap Values needs no discipline.

    /// Where source text is registered, for locating errors.
    pub fn sources(&mut self) -> &mut fixpt_read::SourceMap {
        &mut self.rt.sources
    }
    pub fn interner(&mut self) -> &mut fixpt_read::Interner {
        &mut self.rt.interner
    }
    pub fn interner_ref(&self) -> &fixpt_read::Interner {
        &self.rt.interner
    }
    /// Where a relative path in `%open-input-file` is found.
    pub fn set_file_base(&mut self, base: std::path::PathBuf) {
        self.rt.file_base = base;
    }
    /// Collect now. Every handle is a root, so none is disturbed.
    pub fn collect(&mut self) {
        self.rt.heap.collect(&mut []);
    }
    /// Check the heap's invariants.
    pub fn verify(&self) -> Result<(), String> {
        self.rt.heap.verify()
    }
    /// The heap as an image (`fixpt_heap::image`); collect first to compact it.
    pub fn image(&self) -> Vec<u8> {
        fixpt_heap::image::dump(&self.rt.heap)
    }
    /// Words in use in the heap.
    pub fn heap_used(&self) -> usize {
        self.rt.heap.used()
    }
    /// The collector's bug-finding policy (`Heap::gc_every`).
    pub fn set_gc_every(&mut self, n: u64) {
        self.rt.heap.gc_every = n;
    }

    /// The runtime, with nothing rooted: for the machinery (engines, front
    /// ends that lower into this session), not for code driving it. A Value
    /// taken from here is stale after anything that may collect.
    pub fn runtime_unrooted(&mut self) -> &mut Runtime {
        &mut self.rt
    }

    /// The same, to read.
    pub fn runtime_unrooted_ref(&self) -> &Runtime {
        &self.rt
    }
}

/// Building Values: the heap, and what handles root, within `make`.
pub struct Maker<'m> {
    session: &'m mut Session,
}

impl Maker<'_> {
    pub fn heap(&mut self) -> &mut Heap {
        &mut self.session.rt.heap
    }
    pub fn get(&self, h: Handle) -> Value {
        self.session.handle_value(h)
    }
}

/// The heap, to look at, within `view`.
#[derive(Copy, Clone)]
pub struct View<'v> {
    session: &'v Session,
}

impl<'v> View<'v> {
    pub fn get(self, h: Handle) -> Local<'v> {
        Local { v: self.session.handle_value(h), rt: &self.session.rt }
    }
    /// What a global holds, if it is bound.
    pub fn global(self, name: &str) -> Option<Local<'v>> {
        self.session.global_value_raw(name).map(|v| Local { v, rt: &self.session.rt })
    }
}

/// A Value, within a view. It has no way out: every question it answers is
/// Rust data, or another `Local` of the same view.
#[derive(Copy, Clone)]
pub struct Local<'v> {
    v: Value,
    rt: &'v Runtime,
}

impl<'v> Local<'v> {
    fn at(self, v: Value) -> Local<'v> {
        Local { v, rt: self.rt }
    }
    fn heap(self) -> &'v Heap {
        &self.rt.heap
    }
    pub fn is_false(self) -> bool {
        self.v.is_false()
    }
    pub fn is_true(self) -> bool {
        self.v == Value::TRUE
    }
    pub fn is_null(self) -> bool {
        self.v == Value::NULL
    }
    pub fn is_pair(self) -> bool {
        self.v.is_pair()
    }
    pub fn is_bloblet(self) -> bool {
        self.v.is_bloblet()
    }
    /// The same object as `other`.
    pub fn same_object(self, other: Local<'_>) -> bool {
        self.v == other.v
    }
    pub fn fixnum(self) -> Option<i64> {
        self.v.is_fixnum().then(|| self.v.as_fixnum())
    }
    pub fn char(self) -> Option<char> {
        self.v.is_char().then(|| self.v.as_char())
    }
    pub fn obj_type(self) -> Option<ObjType> {
        self.heap().obj_type(self.v)
    }
    pub fn symbol_name(self) -> Option<String> {
        (self.obj_type() == Some(ObjType::Symbol)).then(|| self.heap().symbol_name(self.v))
    }
    pub fn string(self) -> Option<String> {
        (self.obj_type() == Some(ObjType::String)).then(|| self.heap().string_to_rust(self.v))
    }
    pub fn bytevector(self) -> Option<Vec<u8>> {
        (self.obj_type() == Some(ObjType::Bytevector)).then(|| self.heap().bytevector_to_vec(self.v))
    }
    pub fn flonum(self) -> Option<f64> {
        (self.obj_type() == Some(ObjType::Flonum)).then(|| self.heap().flonum_value(self.v))
    }
    pub fn car(self) -> Option<Local<'v>> {
        self.v.is_pair().then(|| self.at(self.heap().car(self.v)))
    }
    pub fn cdr(self) -> Option<Local<'v>> {
        self.v.is_pair().then(|| self.at(self.heap().cdr(self.v)))
    }
    /// A proper list's elements.
    pub fn list(self) -> Option<Vec<Local<'v>>> {
        self.heap().list_to_vec(self.v).map(|xs| xs.into_iter().map(|x| self.at(x)).collect())
    }
    /// A vector's elements.
    pub fn vector(self) -> Option<Vec<Local<'v>>> {
        (self.obj_type() == Some(ObjType::Vector))
            .then(|| (0..self.heap().obj_len(self.v)).map(|i| self.at(self.heap().obj_ref(self.v, i))).collect())
    }
    pub fn bloblet_kind(self) -> Option<u8> {
        self.v.is_bloblet().then(|| self.heap().bloblet_kind(self.v))
    }
    /// Field `k` of a bloblet (`layout`), checked.
    pub fn field(self, k: usize) -> Option<Local<'v>> {
        if !self.v.is_bloblet() {
            return None;
        }
        self.heap().bloblet_field(self.v, k).ok().map(|x| self.at(x))
    }
    pub fn write(self) -> String {
        fixpt_runtime::write_value(self.heap(), self.v)
    }
    pub fn display(self) -> String {
        fixpt_runtime::display_value(self.heap(), self.v)
    }
}
