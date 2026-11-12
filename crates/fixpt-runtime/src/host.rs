//! A host for code that drives the runtime from Rust (`TODO.md` §252): the
//! runtime, and the discipline for the Values it holds, handles, scopes and
//! views; its globals looked up and given to Rust. No engine: a Scheme
//! session (`fixpt_scheme::Session`) is a host and the Scheme engine, and
//! FX-26's sessions need the engine only where code is lowered.
//!
//! Values for code outside the runtime: handles, scopes and views.
//!
//! A `Value` is a pointer the collector moves, and anything that may
//! collect (every call into the engine, every evaluation) leaves a Value
//! held across it stale. Code driving a host never holds one:
//!
//! * what a host hands out is a [`Handle`], rooted, so it survives
//!   collections, and stamped, so using one after the [`Host::scope`]
//!   that made it has ended is refused rather than misread;
//! * a heap's contents are read only in [`Host::view`], whose [`Local`]s
//!   cannot leave the closure, and which borrows the host immutably, so
//!   nothing in it can collect;
//! * Values are built only in [`Host::make`], whose closure cannot call
//!   the engine, and whose result is rooted as it returns.
//!
//! The runtime itself is behind [`Host::runtime_unrooted`], for code that
//! is part of the machinery; its name says what it gives up.
//!
//! This is the discipline V8's `HandleScope` and `Local`, and JNI's local
//! references, keep; in effect-system terms, the heap is a region, a Local
//! is a read of it scoped to the view, and a call that may collect is the
//! effect that ends it.

use crate::Runtime;
use fixpt_heap::{Heap, ObjType, Value};

/// The runtime and the handles rooted in it.
pub struct Host {
    /// Private: a Value from here is stale after anything that may collect,
    /// so code driving a host gets handles, views and `make` instead, and the
    /// machinery `runtime_unrooted`.
    rt: Runtime,
    /// For each explicit root that is a handle, the stamp it was made with.
    handle_stamps: Vec<u32>,
    next_stamp: u32,
    /// A root kept for an engine made on this host later (a Scheme
    /// session's held hole): pushed first, below every handle and scope, so
    /// that no scope's end pops it.
    engine_root: usize,
}

/// A rooted Value: valid across collections, until its scope ends.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Handle {
    index: u32,
    stamp: u32,
}

impl Host {
    /// A host of runtime `rt`.
    pub fn new(mut rt: Runtime) -> Host {
        let engine_root = rt.heap.push_root(Value::FALSE);
        Host { rt, handle_stamps: Vec::new(), next_stamp: 0, engine_root }
    }

    /// The root kept for an engine made on this host ([`Host::new`]).
    pub fn engine_root(&self) -> usize {
        self.engine_root
    }

    /// Root `v` as a new handle. `v` must be a Value from just now: from
    /// `make`, or from the engine's result before anything else ran.
    pub fn root_value(&mut self, v: Value) -> Handle {
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
    pub fn handle_value(&self, h: Handle) -> Value {
        let i = h.index as usize;
        assert!(
            i < self.rt.heap.root_count() && self.handle_stamps.get(i) == Some(&h.stamp),
            "a handle used after its scope ended"
        );
        self.rt.heap.root_at(i)
    }

    /// How deep the explicit roots are now: for [`release_to`](Host::release_to),
    /// where a [`scope`](Host::scope) cannot be used (its caller owns
    /// more than the host).
    pub fn root_mark(&self) -> usize {
        self.rt.heap.root_count()
    }

    /// Release the handles made, and the roots pushed, since `mark`
    /// ([`root_mark`](Host::root_mark)), as the end of a scope does.
    pub fn release_to(&mut self, mark: usize) {
        self.rt.heap.pop_roots_to(mark);
        self.handle_stamps.truncate(mark);
    }

    /// Run `f`; the handles it makes are released when it returns (so are
    /// any roots anything in it pushed). Keep what `f` computes as Rust data
    /// or as handles made before the scope.
    pub fn scope<R>(&mut self, f: impl FnOnce(&mut Host) -> R) -> R {
        let depth = self.rt.heap.root_count();
        let r = f(self);
        self.rt.heap.pop_roots_to(depth);
        self.handle_stamps.truncate(depth);
        r
    }

    /// Look at the heap: `f` gets a view, whose `Local`s cannot leave it,
    /// and cannot run anything that collects.
    pub fn view<R>(&self, f: impl for<'v> FnOnce(View<'v>) -> R) -> R {
        f(View { host: self })
    }

    /// Build a Value: `f` gets the heap, whose allocation never collects,
    /// and the Values handles root, for the moment; what it returns is
    /// rooted as a handle.
    pub fn make(&mut self, f: impl FnOnce(&mut Maker) -> Value) -> Handle {
        let v = {
            let mut m = Maker { host: self };
            f(&mut m)
        };
        self.root_value(v)
    }

    /// Make `h` root what `f` builds instead.
    pub fn replace(&mut self, h: Handle, f: impl FnOnce(&mut Maker) -> Value) {
        let _ = self.handle_value(h);
        let v = {
            let mut m = Maker { host: self };
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
        fixpt_heap::image::dump_mappable(&self.rt.heap)
    }
    /// Words in use in the heap.
    pub fn heap_used(&self) -> usize {
        self.rt.heap.used()
    }
    /// The collector's bug-finding policy (`Heap::gc_every`): its period of
    /// forced collections, in safepoints.
    pub fn set_gc_every(&mut self, n: u64) {
        self.rt.heap.gc_every = n;
    }

    /// All three of its periods: of forced collections, major ones, and code
    /// collections.
    pub fn set_gc_stress(&mut self, every: u64, major: u64, code: u64) {
        let heap = &mut self.rt.heap;
        (heap.gc_every, heap.gc_major_every, heap.gc_code_every) = (every, major, code);
    }

    /// The runtime, with nothing rooted: for the machinery (engines, front
    /// ends that lower into this host), not for code driving it. A Value
    /// taken from here is stale after anything that may collect.
    pub fn runtime_unrooted(&mut self) -> &mut Runtime {
        &mut self.rt
    }

    /// The same, to read.
    pub fn runtime_unrooted_ref(&self) -> &Runtime {
        &self.rt
    }

    /// Global `name`'s value, now, if it is bound: for this module's callers,
    /// which use it at once.
    pub fn global_value_raw(&self, name: &str) -> Option<Value> {
        let sym = self.rt.heap.intern_existing(name)?;
        let v = self.rt.heap.global(self.rt.heap.symbol_global_slot(sym));
        if v.is_unbound() { None } else { Some(v) }
    }

    /// Global `name`'s value, rooted, if it is bound.
    pub fn global(&mut self, name: &str) -> Option<Handle> {
        let v = self.global_value_raw(name)?;
        Some(self.root_value(v))
    }

    /// Whether a global is bound.
    pub fn is_bound(&self, name: &str) -> bool {
        self.global_value_raw(name).is_some()
    }

    /// What handle `callee` roots given to `f` with `args`, no engine
    /// between (`prim::enter_word`, `prim::enter_front_end`): its result
    /// rooted, or why it failed.
    pub fn call_handle_with(
        &mut self,
        callee: Handle,
        args: &[Handle],
        f: impl FnOnce(&mut Runtime, Value, &[Value]) -> Result<Value, String>,
    ) -> Result<Handle, String> {
        let callee = self.handle_value(callee);
        let args: Vec<Value> = args.iter().map(|a| self.handle_value(*a)).collect();
        f(&mut self.rt, callee, &args).map(|v| self.root_value(v))
    }

    /// Global `name`'s value given to `f` with `args`, no engine between:
    /// for one that Rust enters itself, such as the front end written in
    /// FX-26's (`prim::enter_front_end`). Its result rooted, or why it
    /// failed; none if `name` is unbound.
    pub fn call_global_with(
        &mut self,
        name: &str,
        args: &[Handle],
        f: impl FnOnce(&mut Runtime, Value, &[Value]) -> Result<Value, String>,
    ) -> Option<Result<Handle, String>> {
        let callee = self.global_value_raw(name)?;
        let args: Vec<Value> = args.iter().map(|a| self.handle_value(*a)).collect();
        Some(f(&mut self.rt, callee, &args).map(|v| self.root_value(v)))
    }
}

/// Building Values: the heap, and what handles root, within `make`.
pub struct Maker<'m> {
    host: &'m mut Host,
}

impl Maker<'_> {
    pub fn heap(&mut self) -> &mut Heap {
        &mut self.host.rt.heap
    }
    pub fn get(&self, h: Handle) -> Value {
        self.host.handle_value(h)
    }
}

/// The heap, to look at, within `view`.
#[derive(Copy, Clone)]
pub struct View<'v> {
    host: &'v Host,
}

impl<'v> View<'v> {
    pub fn get(self, h: Handle) -> Local<'v> {
        Local { v: self.host.handle_value(h), rt: &self.host.rt }
    }
    /// What a global holds, if it is bound.
    pub fn global(self, name: &str) -> Option<Local<'v>> {
        self.host.global_value_raw(name).map(|v| Local { v, rt: &self.host.rt })
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
    /// A keyword's name (FX-26's `#:name`).
    pub fn keyword_name(self) -> Option<String> {
        let h = self.heap();
        h.is_keyword(self.v).then(|| h.symbol_name(h.keyword_symbol(self.v)))
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
    /// Field `k` of a bloblet, by its layout's number (`layout`), checked:
    /// for a fixed layout's field. A value, as the bloblet was made with
    /// it, is [`value`](Local::value)'s; a product's field, a sum's tag and
    /// payload, by what FX-26 calls them (`TODO.md` §205).
    pub fn raw_field(self, k: usize) -> Option<Local<'v>> {
        if !self.v.is_bloblet() {
            return None;
        }
        self.heap().bloblet_field(self.v, k).ok().map(|x| self.at(x)) // fields: the caller's field number
    }
    /// Value `i` of a bloblet, from 0, as it was made with them
    /// (`Heap::bloblet_value`), checked.
    pub fn value(self, i: usize) -> Option<Local<'v>> {
        self.heap().bloblet_value_checked(self.v, i).map(|x| self.at(x))
    }
    /// A product's field at position `n`, from 1, as FX-26 writes them
    /// (`Heap::product_field`), checked.
    pub fn product_field(self, n: usize) -> Option<Local<'v>> {
        if n == 0 || !self.heap().is_product(self.v) {
            return None;
        }
        self.value(n - 1)
    }
    /// A sum's tag, checked.
    pub fn sum_tag(self) -> Option<Local<'v>> {
        if !self.heap().is_sum(self.v) {
            return None;
        }
        self.value(0)
    }
    /// A sum's payload, checked.
    pub fn sum_payload(self) -> Option<Local<'v>> {
        if !self.heap().is_sum(self.v) {
            return None;
        }
        self.value(1)
    }
    pub fn write(self) -> String {
        crate::write_value(self.heap(), self.v)
    }
    pub fn display(self) -> String {
        crate::display_value(self.heap(), self.v)
    }
}
