//! Phase 1 (`docs/research/typed-macros.md`, "Decided: transformers in
//! the front end's heap", decision 2, stage 3): a namespace in a session's
//! runtime, made anew for each program's expansion, that a procedural
//! macro's transformer is defined in where its macro is defined, and called
//! in on each use's datum.
//!
//! It is a front end of its own, the conductor's `make-session-compiler`'s,
//! as a session's on the checker written in FX-26 is (`sessions26.rs`):
//! its checker holds the namespace's definitions as the REPL's holds a
//! program's, the standard environment's and the transformers' prelude's
//! first, and nothing of phase 0; its compiler's globals are the
//! namespace's, apart from the program's and every other namespace's. Its
//! code is cellular words, whatever the program's machine, run on the
//! cellular machine written in Rust, which every session's runtime has
//! (`Fx26Session::with_backend_preloaded_in`): as the transformers' session
//! runs them, so that both agree.
//!
//! The front end is held by a global of the namespace's own (`%phase1:N`),
//! which a collection updates; [`Phase1::end`] lets it go. An expansion's
//! is the runtime's current one, `%phase1:current` ([`Phase1::current`]),
//! which both front ends' expanders call their transformers in
//! ([`run_transformer`]: the Rust expander's from inside its lending, the
//! one written in FX-26's by `%fx26-call-procedural`), each transformer
//! defined there once, by its style and text (`%phase1:current:defined`):
//! so that both run the one compiled closure, and agree by construction.

use crate::stage::Wrapped;
use fixpt_heap::Value;
use fixpt_runtime::Runtime;

/// The conductor's entry that makes the front end, and the fields of what
/// it makes, from 1: a step, and a name's global.
const MAKE: &str = "fx26-native:make-session-compiler";
const E_STEP: usize = 4;
const E_CELL: usize = 9;

/// How `session-step` checks: the first, in the standard environment, only
/// checked; and more, kept and compiled.
const FIRST: i64 = 0;
const MORE: i64 = 1;

/// The global that holds the runtime's current namespace, an expansion's
/// (and, after it, `:DIGEST`, each of its namespaces of phase-1 forms).
const CURRENT: &str = "%phase1:current";
/// The global listing the expansion's namespaces of phase-1 forms.
const ALL: &str = "%phase1:current:all";

/// A phase-1 form, `begin-for-syntax`'s: its text, and the directory of
/// the file it is written in, a relative path a load of it names is from:
/// `""` the program's (`syn::load_base`), else a key's directory, its last
/// `/` kept (`dir_of_key`). So its loads are read where it is written, and
/// two forms of one text in two directories are two namespaces' (Heist's
/// should-work note, entry 14).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Form {
    pub text: String,
    pub dir: String,
}

impl Form {
    /// The form as the expander written in FX-26 holds it, a string
    /// (`macros-written.fx`'s `phase1-form`): the directory's length in
    /// characters, `:`, the directory, then the text. Or, a string not so
    /// made, a text of the program's directory.
    pub(crate) fn decoded(s: &str) -> Form {
        let parsed = s.split_once(':').and_then(|(n, rest)| {
            let n = n.parse::<usize>().ok()?;
            let split = rest.char_indices().nth(n).map_or(rest.len(), |(i, _)| i);
            (rest.chars().count() >= n).then(|| Form { dir: rest[..split].to_string(), text: rest[split..].to_string() })
        });
        parsed.unwrap_or_else(|| Form { text: s.to_string(), dir: String::new() })
    }

    /// Where its loads' relative paths are from: none for the current
    /// directory.
    pub(crate) fn dir_path(&self) -> Option<std::path::PathBuf> {
        if self.dir.is_empty() { crate::syn::load_base() } else { Some(std::path::PathBuf::from(&self.dir)) }
    }

    /// Its directory resolved, as its namespace is named by: the program's
    /// as a key's would be, its last `/` kept.
    fn dir_resolved(&self) -> String {
        match self.dir_path() {
            Some(d) => dir_of_key(&format!("{}/", d.display().to_string().trim_end_matches('/'))),
            None => String::new(),
        }
    }
}

/// The directory of the file of key `key` (`TODO.md` §68's, `input:` or
/// not) as a phase-1 form names it: up to its last `/`, kept; `""` if it
/// has none. The same as the expander written in FX-26's `key-dir`.
pub(crate) fn dir_of_key(key: &str) -> String {
    let path = key.strip_prefix("input:").unwrap_or(key);
    path.rfind('/').map_or(String::new(), |i| path[..=i].to_string())
}

/// Phase-1 forms `forms`'s digest: what names their namespace, each form
/// by its text and its directory resolved.
pub(crate) fn forms_digest(forms: &[Form]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    for f in forms {
        f.text.hash(&mut h);
        f.dir_resolved().hash(&mut h);
    }
    h.finish()
}

/// A phase-1 form refused: why, and, where the refusal is at a place of
/// one of them, which and where in its text (characters, from 0).
#[derive(Debug)]
pub struct Refused {
    pub why: String,
    pub at: Option<(usize, i64, i64)>,
}

impl Refused {
    /// As the expander written in FX-26 is answered (`for-syntax!`): `@I S
    /// E` and a newline first, where it has a place.
    pub(crate) fn answer(&self) -> String {
        match self.at {
            Some((i, a, b)) => format!("@{i} {a} {b}\n{}", self.why),
            None => self.why.clone(),
        }
    }
}

impl From<Refused> for String {
    fn from(r: Refused) -> String {
        r.why
    }
}

/// The product kind the step's loads are given in (`session-step`).
const PRODUCT: u8 = fixpt_heap::layout::kind("product");

/// What every transformer sees besides the standard environment.
const PRELUDE: &str = include_str!("macros/procedural-prelude.fx");

thread_local! {
    /// The namespaces made on this thread: each one's global its own.
    static MADE: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// The expander written in FX-26's calls answered in a namespace.
    static CALLED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// How many of the expander written in FX-26's transformers' calls this
/// thread answered in a phase-1 namespace (`call_procedural`): for tests.
pub fn called_for_fx26() -> u64 {
    CALLED.with(|c| c.get())
}

/// How many namespaces this thread has made: for tests, that each
/// expansion has its own.
pub fn made() -> u64 {
    MADE.with(|m| m.get())
}

/// A phase-1 namespace ([`self`]): the name of the global that holds its
/// front end.
pub struct Phase1 {
    global: String,
}

impl Phase1 {
    /// A namespace made in `rt`, the standard environment and the
    /// transformers' prelude defined in it; or why not (a session whose
    /// front end is not compiled, which `stage` cannot use either).
    pub fn new(rt: &mut Runtime) -> Result<Phase1, String> {
        let n = MADE.with(|m| m.get());
        Phase1::made_at(rt, format!("%phase1:{n}"))
    }

    /// The runtime's current namespace, an expansion's: made if it has none.
    pub fn current(rt: &mut Runtime) -> Result<Phase1, String> {
        Phase1::current_for(rt, &[]).map_err(String::from)
    }

    /// The expansion's namespace of the phase-1 forms `forms`
    /// (`begin-for-syntax`'s, in order), made if it has none: the standard
    /// environment, the prelude, then `forms`, defined there. A transformer
    /// runs in the namespace of the forms in force where it was defined, so
    /// that what it names is what was there, whatever was defined after or
    /// in another file (`docs/research/typed-macros.md`, "for-syntax").
    pub fn current_for(rt: &mut Runtime, forms: &[Form]) -> Result<Phase1, Refused> {
        let global = if forms.is_empty() { CURRENT.to_string() } else { format!("{CURRENT}:{:016x}", forms_digest(forms)) };
        if crate::stage::global(rt, &global).is_some_and(|v| v != Value::FALSE) {
            return Ok(Phase1 { global });
        }
        let p = Phase1::made_at(rt, global.clone()).map_err(|why| Refused { why, at: None })?;
        // Each made one's global listed, for the expansion's end.
        let name = rt.heap.make_string(&global);
        let base = rt.heap.push_root(name);
        let all = crate::stage::global(rt, ALL).unwrap_or(Value::NULL);
        let l = rt.heap.cons(rt.heap.root_at(base), all);
        rt.heap.pop_roots_to(base);
        let sym = rt.heap.intern(ALL);
        let slot = rt.heap.symbol_ref(sym);
        rt.heap.set_global_at(&slot, l);
        if let Err(e) = p.define_forms(rt, forms) {
            let sym = rt.heap.intern(&global);
            let slot = rt.heap.symbol_ref(sym);
            rt.heap.set_global_at(&slot, Value::FALSE);
            return Err(e);
        }
        Ok(p)
    }

    /// A namespace of its own made in `rt` ([`Phase1::new`]), `forms`
    /// defined in it: the transformers' session's, for those forms.
    pub fn with_forms(rt: &mut Runtime, forms: &[Form]) -> Result<Phase1, Refused> {
        let p = Phase1::new(rt).map_err(|why| Refused { why, at: None })?;
        p.define_forms(rt, forms)?;
        Ok(p)
    }

    /// Phase-1 forms `forms` checked, compiled and run in the namespace,
    /// in order, each given the files it loads, read from its directory
    /// (`syn::loads_given`); or why one was refused, and where in it.
    fn define_forms(&self, rt: &mut Runtime, forms: &[Form]) -> Result<(), Refused> {
        for (i, f) in forms.iter().enumerate() {
            let loads = crate::syn::loads_given(&f.text, f.dir_path());
            self.run_loading(rt, &format!("{}\n", f.text), MORE, &loads).map_err(|(why, at)| Refused { why, at: at.map(|(a, b)| (i, a, b)) })?;
        }
        Ok(())
    }

    /// The runtime's current namespaces ended, if it has any: an
    /// expansion's end (`Fx26Session::expansion`).
    pub fn end_current(rt: &mut Runtime) {
        let mut l = crate::stage::global(rt, ALL).unwrap_or(Value::NULL);
        let mut globals = vec![CURRENT.to_string()];
        while l.is_pair() {
            globals.push(rt.heap.string_to_rust(rt.heap.car(l)));
            l = rt.heap.cdr(l);
        }
        for g in globals {
            if crate::stage::global(rt, &g).is_some_and(|v| v != Value::FALSE) {
                Phase1 { global: g }.end(rt);
            }
        }
        let sym = rt.heap.intern(ALL);
        let slot = rt.heap.symbol_ref(sym);
        rt.heap.set_global_at(&slot, Value::NULL);
    }

    /// The transformer of `key` (its style and text) defined in the
    /// namespace, its global, if it is; and how many are.
    fn defined_of(&self, rt: &mut Runtime, key: &str) -> (Option<String>, usize) {
        let defined = format!("{}:defined", self.global);
        // `((key . name) …)`, the newest first.
        let mut l = crate::stage::global(rt, &defined).unwrap_or(Value::NULL);
        let mut n = 0;
        while l.is_pair() {
            let entry = rt.heap.car(l);
            if rt.heap.string_to_rust(rt.heap.car(entry)) == key {
                return (Some(rt.heap.symbol_name(rt.heap.cdr(entry))), n);
            }
            n += 1;
            l = rt.heap.cdr(l);
        }
        (None, n)
    }

    /// Transformer `code`, of style `ty` (`key` its style and text), defined
    /// in the namespace if it is not yet, `procedural::helpers` around it: the
    /// global it is; or why it was not defined.
    pub fn transformer(&self, rt: &mut Runtime, ty: &str, key: &str, code: &str) -> Result<String, String> {
        let defined = format!("{}:defined", self.global);
        let (n, count) = self.defined_of(rt, key);
        if let Some(n) = n {
            return Ok(n);
        }
        let name = format!("%transformer:{count}");
        self.define(rt, &name, ty, code)?;
        let k = rt.heap.make_string(key);
        let base = rt.heap.push_root(k);
        let sym = rt.heap.intern(&name);
        let entry = rt.heap.cons(rt.heap.root_at(base), sym);
        rt.heap.push_root(entry);
        let old = crate::stage::global(rt, &defined).unwrap_or(Value::NULL);
        let entry = rt.heap.root_at(base + 1);
        let l = rt.heap.cons(entry, old);
        rt.heap.pop_roots_to(base);
        let dsym = rt.heap.intern(&defined);
        let slot = rt.heap.symbol_ref(dsym);
        rt.heap.set_global_at(&slot, l);
        Ok(name)
    }

    /// A namespace made at global `global`.
    fn made_at(rt: &mut Runtime, global: String) -> Result<Phase1, String> {
        let make = crate::stage::global(rt, MAKE).ok_or("phase 1 needs the front end compiled")?;
        let fe = fixpt_runtime::prim::call_front_end(rt, make, &[])?;
        MADE.with(|m| m.set(m.get() + 1));
        let p = Phase1 { global };
        let sym = rt.heap.intern(&p.global);
        let slot = rt.heap.symbol_ref(sym);
        rt.heap.set_global_at(&slot, fe);
        // The first step begins the checker in the standard environment, and
        // only checks; the prelude is the next, compiled.
        p.run(rt, "(define %phase1 unit #u)\n", FIRST).map_err(|e| format!("phase 1's start: {e}"))?;
        p.run(rt, PRELUDE, MORE).map_err(|e| format!("phase 1's prelude: {e}"))?;
        Ok(p)
    }

    /// `(define name ty code)` checked, compiled and run in the namespace;
    /// or why not, as its checker or compiler says it. Naming a global reads
    /// it, as in a program (`Checker::globals_effects`): a transformer of a
    /// type with no such effect binds the prelude's procedures it calls
    /// around its `lambda`, read as it is defined (`procedural::helpers`).
    pub fn define(&self, rt: &mut Runtime, name: &str, ty: &str, code: &str) -> Result<(), String> {
        self.run(rt, &format!("(define {name} {ty}\n{code})\n"), MORE)
    }

    /// The value of the namespace's global `name`, if it has one.
    pub fn value(&self, rt: &mut Runtime, name: &str) -> Option<Value> {
        let sym = rt.heap.intern(name);
        let cells = self.call_entry(rt, E_CELL, &[sym]).ok()?;
        (cells != Value::NULL).then(|| rt.heap.bloblet_slot(rt.heap.car(cells), fixpt_heap::layout::cellular::GLOBAL_VALUE))
    }

    /// The namespace's procedure `name` called with `args`, each rooted by
    /// the caller: its value, or why it failed.
    pub fn call(&self, rt: &mut Runtime, name: &str, args: &[Value]) -> Result<Value, String> {
        let base = rt.heap.root_count();
        for &a in args {
            rt.heap.push_root(a);
        }
        let f = self.value(rt, name);
        let args: Vec<Value> = (0..args.len()).map(|i| rt.heap.root_at(base + i)).collect();
        rt.heap.pop_roots_to(base);
        let f = f.ok_or_else(|| format!("phase 1 has no `{name}`"))?;
        // Its failure said as the transformer's own, as the transformers'
        // session says it, not as the machine's.
        on_cellular(rt, |rt| fixpt_runtime::prim::enter_word(rt, f, &args))
            .map_err(|e| e.strip_prefix("cellular word: ").map_or(e.clone(), str::to_string))
    }

    /// The namespace let go: its front end, and what it defined, garbage.
    pub fn end(self, rt: &mut Runtime) {
        for g in [self.global.clone(), format!("{}:defined", self.global)] {
            let sym = rt.heap.intern(&g);
            let slot = rt.heap.symbol_ref(sym);
            rt.heap.set_global_at(&slot, Value::FALSE);
        }
    }

    fn front_end(&self, rt: &mut Runtime) -> Value {
        let sym = rt.heap.intern(&self.global);
        rt.heap.global_of(sym)
    }

    /// Entry `i` of the namespace's front end, called with `args`.
    fn call_entry(&self, rt: &mut Runtime, i: usize, args: &[Value]) -> Result<Value, String> {
        let fe = self.front_end(rt);
        let f = rt.heap.product_field(fe, i);
        let fuel = std::mem::replace(&mut rt.word_fuel, u64::MAX);
        let out = fixpt_runtime::prim::call_front_end(rt, f, args);
        rt.word_fuel = fuel;
        out
    }

    /// `text`, definitions, checked as `how` says and kept, compiled, and
    /// the word run; or the refusal's message.
    fn run(&self, rt: &mut Runtime, text: &str, how: i64) -> Result<(), String> {
        self.run_loading(rt, text, how, &[]).map_err(|(why, _)| why)
    }

    /// [`run`](Self::run), `loads` the files `text` loads: or the refusal's
    /// message, and where in `text` it is, if it is.
    fn run_loading(&self, rt: &mut Runtime, text: &str, how: i64, loads: &[crate::syn::LoadGiven]) -> Result<(), (String, Option<(i64, i64)>)> {
        let standard = crate::stage::standard(rt).ok_or(("phase 1 needs the standard environment read".to_string(), None))?;
        let w = Wrapped::of(String::new(), text, "", text, 0);
        let mark = rt.heap.push_root(standard);
        let whole = rt.heap.make_string(&w.whole);
        rt.heap.push_root(whole);
        let none = rt.heap.intern("%none");
        rt.heap.push_root(none);
        let rep = rt.heap.make_bytevector(&[]);
        rt.heap.push_root(rep);
        let given = loads_list(rt, loads);
        rt.heap.push_root(given);
        let [standard, whole, none, rep, given] = [0, 1, 2, 3, 4].map(|i| rt.heap.root_at(mark + i));
        rt.heap.pop_roots_to(mark);
        // Made and not deferred; cellular words, neither native nor with
        // register code; no names given types by rep.
        let (made, deferred, native, registers) = (Value::TRUE, Value::FALSE, Value::FALSE, Value::FALSE);
        let mode = Value::fixnum(crate::ids::mode() as i64);
        let args = [standard, whole, Value::fixnum(w.skip), Value::fixnum(w.len), Value::fixnum(how), none, made, deferred, native, registers, rep, Value::NULL, mode, given];
        let out = self.call_entry(rt, E_STEP, &args).map_err(|e| (e, None))?;
        let tag = rt.heap.symbol_name(rt.heap.sum_tag(out));
        let payload = rt.heap.sum_payload(out);
        if tag == "checked" && how == FIRST {
            return Ok(());
        }
        if tag != "made" {
            // `(sum failed (product kind message start end))`.
            let message = rt.heap.product_field(payload, 2);
            let why = if rt.heap.is_a(message, fixpt_heap::ObjType::String) { rt.heap.string_to_rust(message) } else { tag };
            let (a, b) = (rt.heap.product_field(payload, 3), rt.heap.product_field(payload, 4));
            let at = (a.is_fixnum() && b.is_fixnum()).then(|| (a.as_fixnum(), b.as_fixnum()));
            return Err((why, at));
        }
        on_cellular(rt, |rt| fixpt_engine::cellular::run_word(rt, payload, &[])).map(|_| ()).map_err(|e| (e, None))
    }
}

/// `loads` as the step takes them (`session-step`'s `given`): a list of
/// `(product here base why path text key)`, the last read first, as
/// `loaded-files!` takes a program's.
pub(crate) fn loads_list(rt: &mut Runtime, loads: &[crate::syn::LoadGiven]) -> Value {
    let mut l = Value::NULL;
    for g in loads {
        let base = rt.heap.push_root(l);
        for s in [&g.why, &g.path, &g.text, &g.key] {
            let v = rt.heap.make_string(s);
            rt.heap.push_root(v);
        }
        let fields: Vec<Value> = [Value::fixnum(g.here), Value::fixnum(g.base)].into_iter().chain((1..=4).map(|i| rt.heap.root_at(base + i))).collect();
        let p = rt.heap.make_frozen(PRODUCT, &fields);
        rt.heap.push_root(p);
        let (l0, p) = (rt.heap.root_at(base), rt.heap.root_at(base + 5));
        l = rt.heap.cons(p, l0);
        rt.heap.pop_roots_to(base);
    }
    l
}

/// `f`, with the cellular machine written in Rust the runtime's: phase 1's
/// code is cellular words whatever machine runs the program's.
fn on_cellular<T>(rt: &mut Runtime, f: impl FnOnce(&mut Runtime) -> T) -> T {
    let run = std::mem::replace(&mut rt.run_word, Some(fixpt_engine::cellular::run_word));
    let out = f(rt);
    rt.run_word = run;
    out
}

/// Transformer `code`, of `style`, called on `datum` in expansion `made`, in
/// `rt`'s current namespace ([`Phase1::current`]), the namespace made and
/// the transformer defined there if they are not yet: what it gave, raw
/// (its caller makes it syntax before anything collects); or why it failed.
/// None where `rt` has no phase 1 (its front end not compiled), where the
/// transformers' session runs it. Both front ends' expanders call it, so
/// both run the one closure.
///
/// Either expander may define, inside its own parse: a definition is a
/// parse of the namespace's own front end, whose reader, parser and
/// expander, with their state, are its own (the conductor makes them for
/// each front end), so the parse it is inside is left as it was.
pub(crate) fn run_transformer(rt: &mut Runtime, style: crate::macros::procedural::Style, code: &str, forms: &[Form], datum: Value) -> Option<Result<Value, String>> {
    use crate::macros::procedural;
    let base = rt.heap.push_root(datum);
    let out = (|| {
        let key = procedural::key(style, code);
        // No phase 1 here at all (its front end not compiled, or the
        // standard environment not read): apart. A phase-1 form refused:
        // the transformer's failure.
        let plain = Phase1::current(rt).ok()?;
        let ph = if forms.is_empty() {
            plain
        } else {
            match Phase1::current_for(rt, forms) {
                Ok(ph) => ph,
                Err(e) => return Some(Err(e.why)),
            }
        };
        let global = match ph.transformer(rt, style.ty(), &key, &procedural::helpers(code)) {
            Ok(g) => g,
            Err(e) => return Some(Err(e)),
        };
        let d = rt.heap.root_at(base);
        Some(call_transformer(rt, &ph, &global, style, d))
    })();
    rt.heap.pop_roots_to(base);
    out
}

/// Transformer `global` of namespace `ph`, of `style`, called on `datum` in
/// expansion `made`: what it gave, raw; or why it failed. Its second
/// argument and third as its style has them (a renamer of the expansion and
/// a comparer; or the use's or the macro's environment).
pub(crate) fn call_transformer(rt: &mut Runtime, ph: &Phase1, global: &str, style: crate::macros::procedural::Style, datum: Value) -> Result<Value, String> {
    use crate::macros::procedural::{self, Style};
    let base = rt.heap.push_root(datum);
    let out = (|| {
        let second = match style {
            Style::Er => ph.value(rt, "%er-rename").ok_or("no `%er-rename` in phase 1")?,
            Style::Sc => rt.heap.intern(procedural::USE_ENV),
            Style::Rsc => rt.heap.intern(procedural::MACRO_ENV),
        };
        rt.heap.push_root(second);
        if let Style::Er = style {
            let compare = ph.value(rt, "%er-compare").unwrap_or(Value::FALSE);
            rt.heap.push_root(compare);
        }
        // Where a transformer's call collects (`TODO.md` §278): a test's, on
        // either side of it, what it is given and gives rooted; the Rust
        // expander's syntax tenured, moved by neither.
        crate::heap_syn::collect_young_if_asked_in(&mut rt.heap);
        let args: Vec<Value> = (base..rt.heap.root_count()).map(|i| rt.heap.root_at(i)).collect();
        let out = ph.call(rt, global, &args)?;
        let at = rt.heap.push_root(out);
        crate::heap_syn::collect_young_if_asked_in(&mut rt.heap);
        Ok(rt.heap.root_at(at))
    })();
    rt.heap.pop_roots_to(base);
    out
}

/// What `%fx26-call-procedural` does (`Runtime::procedural`), for the
/// expander written in FX-26: its arguments a style (0 explicit renaming, 1
/// syntactic closures, 2 reversed), the transformer's text, the use's
/// datum, the expansion's tag (`K.N`, which no transformer is given now:
/// the expander makes `rename`'s aliases its own, `procedural::tagged`),
/// and the phase-1 forms in force where it was
/// defined (a list of texts, `begin-for-syntax`'s); `(sum ok datum)`, what the transformer gave, or
/// `(sum failed why)`. In the expansion's namespace, made and the
/// transformer defined there if they are not yet; else, where the runtime
/// has no phase 1, in the transformers' session, the datum and what it gave
/// copied between the heaps (`procedural::apply_copied`).
pub fn call_procedural(rt: &mut Runtime, a: &[Value]) -> Result<Value, String> {
    use crate::macros::procedural::Style;
    let style = match a[0].as_fixnum() {
        0 => Style::Er,
        1 => Style::Sc,
        _ => Style::Rsc,
    };
    let code = rt.heap.string_to_rust(a[1]);
    // The phase-1 forms in force where it was defined, a list of them,
    // each as the expander holds it (`Form::encoded`).
    let mut forms = Vec::new();
    let mut l = a[4];
    while l.is_pair() {
        forms.push(Form::decoded(&rt.heap.string_to_rust(rt.heap.car(l))));
        l = rt.heap.cdr(l);
    }
    let out = match run_transformer(rt, style, &code, &forms, a[2]) {
        Some(out) => {
            CALLED.with(|c| c.set(c.get() + 1));
            out
        }
        None => crate::macros::procedural::apply_copied(style, &code, &forms, &mut rt.heap, a[2]),
    };
    Ok(match out {
        Ok(v) => crate::sessions::sum(rt, "ok", v),
        Err(why) => {
            let why = rt.heap.make_string(&why);
            crate::sessions::sum(rt, "failed", why)
        }
    })
}
