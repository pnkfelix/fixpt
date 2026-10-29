//! Running FX-26: check, lower, evaluate.
//!
//! One top-level form at a time, in one environment: a definition stays
//! defined, for the checker (`Checker::top`) and for the Scheme session
//! (`lower::Globals`) alike. The lowered code goes across as text and is
//! re-read, as FX-87's and FX-91's does, because the checker and the Scheme
//! session intern symbols separately — and so that `,code` can show it.
//!
//! Running goes through `Session::eval_capturing`, which is the whole of what
//! the three FX front ends' sessions had in common: evaluate, and keep what the
//! program printed apart from its value.

use crate::check::Checker;
use crate::error::{FxError, R};
use crate::lower::{Globals, lower};
use crate::top::Top;
use fixpt_read::{FileId, Span, Sym, Syntax};
use fixpt_scheme::Session;

/// The FX-26 run-time environment, as Scheme.
pub const RUNTIME: &str = include_str!("runtime.scm");

/// Default evaluation budget for one form, as FX-87's.
pub const DEFAULT_STEP_LIMIT: u64 = 20_000_000;

pub struct Fx26Session {
    pub checker: Checker,
    /// REPL entries of type definitions that name types not defined yet:
    /// held, unrun, until those are (`Fx26Session::consider`).
    pub pending: Vec<Pending>,
    pub scheme: Session,
    pub globals: Globals,
    /// How checked forms run.
    pub strategy: Strategy,
    /// Whether the prelude's data is still to be read
    /// (`with_backend_preloaded_in`, `whole_prelude`).
    prelude_data_pending: bool,
    /// Under `Strategy::Cellular`: whether the compiler written in FX-26
    /// makes each lambda's register code too, for a machine that runs it.
    pub register_code: bool,
    /// Whether the FX-26 front end's checker and compilers run as register
    /// code (`front_end_as_register_code`), made so when first loaded; the
    /// runtime's `front_end_run_word` must be a machine for register code.
    pub front_end_compiled: bool,
    /// Whether that register code is the native convention's
    /// (`front_end_as_register_code`): checked so, its closures made native
    /// as they are made, by the runtime's `adapt`, which must compile them.
    pub front_end_native: bool,
    /// How that native code is kept in the cache, after the front end's
    /// first run, and read back (`TODO.md` §126); without it, the front end
    /// is compiled and run natively in every session, its word kept.
    pub native_keeping: Option<NativeKeeping>,
    /// Whether the program's convention is native (a `nativecc` machine;
    /// set by [`set_native_convention`](Fx26Session::set_native_convention)).
    native_convention: bool,
    /// Whether naming a global reads it (`set_globals_effects`).
    globals_effects: bool,
    /// Whether re-runs wait (`set_defer_reruns`).
    defer_reruns: bool,
    /// Whether the FX-26 checker holds aside its last check's breaks
    /// (`Session::hold_breaks`).
    breaks_held: bool,
    /// Whether the form running is one the pieces written in FX-26 made
    /// already (`run_forms`).
    own_made: bool,
    /// Under `Strategy::Cellular` with the native convention: how an
    /// expression form is run, in place of the cellular machine.
    pub native_runner: Option<NativeRunner>,
    /// And how a definition's procedure, made by cellular code, is compiled
    /// to a native closure of the same code: for the definitions the native
    /// runner declines, and `define-rec`'s.
    pub native_compiler: Option<NativeCompiler>,
    /// The same by the compiler written in FX-26, in place of
    /// `native_compiler`'s, and before `native_runner` runs an expression
    /// (which it then gives the native closure, or, if this declined, the
    /// cellular one): `fx-regs-fxjit-nativecc`.
    pub native_fx: Option<NativeFx>,
    /// Under `Strategy::Cellular`: whether the checker written in FX-26 has
    /// begun this session's program, so that each form is checked after the
    /// ones before (`check-more`), and compiled alone against the globals
    /// they made, which the compiler keeps.
    own_begun: bool,
    /// The loads whose hidden globals this session's program has made, by
    /// key (`syn::set_shared_made`): forms compiled one by one make none of
    /// them again. Forgotten as a whole program begins.
    shared_made: std::collections::HashSet<String>,
    /// The module files built in given a `.fasl` this session, or tried
    /// (`cache_built_ins`).
    built_ins_cached: std::collections::HashSet<String>,
    /// The file the forms run now are from, as a debugger's lines name it
    /// (`crate::sources`): set by a driver, as `fixpt run` does each file's.
    pub source_file: Option<crate::sources::File>,
    /// The form compiled next, as written, with where each datum went.
    source_form: Option<(String, Vec<(usize, usize, Span)>)>,
    /// Each module file loaded, as a source names it, made once.
    source_loaded: std::collections::HashMap<FileId, crate::sources::File>,
    /// How a redefinition that would break definitions is decided: asked of
    /// the driver, or, with none, `Redefine::Break`.
    pub redefine: Option<fn(&Redefinition) -> Redefine>,
    /// What the next such redefinition does, said ahead of it (the REPL's
    /// `,redefine`), in place of asking.
    pub next_redefine: Option<Redefine>,
    /// Under `Strategy::Cellular`: whether each form's [`Outcome::code`] is
    /// the words the compiler written in FX-26 made for it, those not shown
    /// for an earlier form, rather than its lowering to Scheme.
    pub show_words: bool,
    /// The words shown so far, each as its disassembly.
    words_shown: std::collections::HashSet<String>,
    /// The initial environment as the FX-26 reader read it, for the checker
    /// written in FX-26: read once, as it takes the reader a while.
    standard26: Option<fixpt_scheme::Handle>,
    /// Under `Evaluate`, where the next form's positions begin: past every
    /// text the evaluator was given before (`eval_form`).
    eval_base: i64,
    /// How many steps a form may take when run, or no limit: see
    /// [`set_step_limit`](Fx26Session::set_step_limit).
    step_limit: Option<u64>,
    /// The same for a form run early, as it is typed ([`speculate`]
    /// (Fx26Session::speculate)): small, so that a loop costs a keystroke
    /// nothing noticeable. No limit lets a loop being typed hang the editor.
    pub speculation_limit: Option<u64>,
    /// Whether a load reads a fresh `.fasl` beside its file
    /// (`docs/research/fasl.md`): under `Strategy::Cellular`, unless
    /// `FIXPT_NO_FASL` says not.
    pub fasls: bool,
    /// Whether a `.fasl` made keeps its procedures as cellular words alone
    /// (`compile-file --cellular`), which a loader compiles natively, rather
    /// than as the native code they are (`crate::fasl::image`).
    pub fasl_cellular: bool,
    /// The program's file the forms run now are, for its `.fasl` (set by a
    /// driver: `fixpt run`, `fixpt eval`, `,load`), which `run_forms` reads.
    pub program_file: Option<std::path::PathBuf>,
    /// While a program's file is compiled to a `.fasl` (`compile_file`):
    /// what each of its forms checked as, by its place among them; and its
    /// forms are checked and made globals but not run, but for the
    /// definitions of procedures, whose making does nothing else.
    program_record: Option<Vec<(usize, Top, String)>>,
    /// While so: the globals whose definitions ran, whose values are made,
    /// so that a definition that only reads them can run too.
    program_ran: std::collections::HashSet<Sym>,
}

/// A program's `.fasl` read for its forms (`Fx26Session::program_fasl`):
/// each definition kept, by its form's place, with its value's; the image
/// they are copied from, its values, and what stands in it for what it
/// links to.
struct ProgramFasl {
    defs: std::collections::HashMap<usize, Vec<(crate::fasl::Def, usize)>>,
    heap: fixpt_heap::Heap,
    values: Vec<fixpt_heap::Value>,
    links: std::collections::HashMap<u64, crate::fasl::Link>,
    /// The closures that were native, of cellular words alone (`compile-file
    /// --cellular`): compiled natively where they are defined.
    natives: Vec<fixpt_heap::Value>,
    /// The file's own abbreviations to check as they are named, each with
    /// what it was (`program_fasl`).
    later: std::cell::RefCell<std::collections::HashMap<String, String>>,
    /// The names of all it keeps, what each is printed with to compare.
    alias_names: Vec<Sym>,
}

/// The budget for one speculative run: enough for a REPL-sized
/// computation, small enough that a loop costs a keystroke nothing noticeable.
pub const SPECULATION_STEP_LIMIT: u64 = 200_000;

/// What running a form early came to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Speculation {
    /// It ran, to this value.
    Value(String),
    /// It ran, and failed — `(car nil)` is well typed.
    Failed(String),
    /// It does not check.
    Rejected(String),
    /// It was not run: its effect has this atom, which the licence does not
    /// cover.
    NotLicensed(String),
    /// A definition: running one early would define it.
    NotAnExpression,
}

/// A REPL entry that defines types naming types not defined yet: held as
/// it was read, and run with the entries that complete it.
#[derive(Debug, Clone)]
pub struct Pending {
    pub forms: Vec<Syntax>,
    /// What it defines: types, and values (a datatype's constructors).
    pub defines: Vec<String>,
}

/// What entering a REPL entry does, given the entries pending.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Consider {
    /// It runs as any entry does.
    Run,
    /// It completes the pending entries: they and it run together.
    Completes(Vec<String>),
    /// It waits too: these types are not defined yet.
    Pends(Vec<String>),
}

/// Check and lower one top-level form, keeping what it defines, alone: not
/// under redefinition (`compile_form_defining` is).
pub fn compile_form(checker: &mut Checker, globals: &mut Globals, form: &Syntax) -> R<(Top, String)> {
    let before = std::mem::take(&mut checker.hoisted);
    let top = checker.top(form);
    // The hidden globals of the files it loads first, defined before it.
    let hoisted = std::mem::replace(&mut checker.hoisted, before);
    let top = top?;
    let mut code: String = hoisted.iter().map(|(t, _)| lower_top(checker, globals, t)).collect::<Vec<_>>().join("\n");
    if !code.is_empty() {
        code.push('\n');
    }
    code.push_str(&lower_top(checker, globals, &top));
    Ok((top, code))
}

/// Check and lower one top-level form, under redefinition
/// (`Checker::top_defining`): the Scheme for everything it makes run, in
/// order, and what it broke.
pub fn compile_form_defining(checker: &mut Checker, globals: &mut Globals, form: &Syntax) -> R<(crate::top::Defining, Vec<String>)> {
    let done = checker.top_defining(form)?;
    let code = done.hoisted.iter().chain(&done.run).map(|(top, _)| lower_top(checker, globals, top)).collect();
    Ok((done, code))
}

/// A checked top-level form, lowered: a definition that assigns keeps the
/// global its name has (`Globals::keep_next`).
pub fn lower_top(checker: &Checker, globals: &mut Globals, top: &Top) -> String {
    match top {
        Top::Define { name, assigns: true, .. } => globals.keep_next(*name),
        Top::DefineRec { bindings, assigns: true } => bindings.iter().for_each(|(n, _, _)| globals.keep_next(*n)),
        _ => {}
    }
    match top {
        Top::DefineType { .. } | Top::DefineTypeFamily { .. } | Top::DefineGenerative { .. } | Top::DefineEffect { .. } | Top::DefineConvention { .. } => {
            String::new()
        }
        Top::Define { name, exp, recursive, .. } => {
            // A recursive definition refers to itself; a plain one to
            // whatever the name meant before it.
            let (global, body) = if *recursive {
                let g = globals.define(checker, *name);
                (g, lower(checker, globals, *exp))
            } else {
                let body = lower(checker, globals, *exp);
                (globals.define(checker, *name), body)
            };
            format!("(define {global} {body})")
        }
        Top::DefineRec { bindings, .. } => {
            // Every name first: each lambda refers to the group's globals.
            let names: Vec<String> = bindings.iter().map(|(n, _, _)| globals.define(checker, *n)).collect();
            let defs: Vec<String> =
                bindings.iter().zip(&names).map(|((_, _, e), g)| format!("(define {g} {})", lower(checker, globals, *e))).collect();
            format!("(begin {})", defs.join(" "))
        }
        Top::Exp(k) => lower(checker, globals, k.exp),
    }
}

/// A whole program, checked and lowered but not run: the checker that
/// checked it, and the Scheme for each form, in order.
pub struct Compiled {
    pub checker: Checker,
    pub code: Vec<String>,
}

/// Check and lower the program `text`, whose definitions may come in any
/// order.
pub fn compile_program(text: &str) -> R<Compiled> {
    compile_program_as(text, "fx:")
}

/// The same, with every global the program defines named `<prefix><name>`,
/// so that it can share a Scheme session with another FX-26 program.
pub fn compile_program_as(text: &str, prefix: &str) -> R<Compiled> {
    let mut checker = Checker::new();
    let mut globals = Globals::with_prefix(prefix);
    let forms = checker.read_in(FileId(0), text)?;
    let done = checker.declare_ahead(&forms)?;
    let mut code = Vec::new();
    for (f, done) in forms.iter().zip(done) {
        if !done {
            let (_, cs) = compile_form_defining(&mut checker, &mut globals, f)?;
            code.extend(cs.into_iter().filter(|c| !c.is_empty()));
        }
    }
    Ok(Compiled { checker, code })
}

/// The global prefix the eager reader is loaded under when it shares a
/// Scheme session with other code, so that a user's `(define need …)` —
/// `fx:need` — cannot replace the reader's `need`.
pub const READER_PREFIX: &str = "fx26-reader:";

/// Check the eager reader written in FX-26, check its licence, and only
/// then load it into `scheme`, under [`READER_PREFIX`]. It runs on every
/// keystroke, so nothing of it may run before the licence says it can.
pub fn load_eager_reader(scheme: &mut Session) -> Result<(), String> {
    load_lowered(scheme, &crate::front_end())
}

/// The reader and parser alone (the front end's first files, which need
/// none after them), lowered and loaded: all a session whose checker and
/// compilers run as register code runs lowered, and all an eager reader
/// needs. A tenth of the front end, and of its loading, which is most of a
/// session's start (3.6 s for the whole, lowered, on x86_64).
pub fn load_reader_alone(scheme: &mut Session) -> Result<(), String> {
    let parser = crate::FRONT_END_FILES.iter().position(|(n, _)| *n == "reader.fx").expect("listed");
    let text = crate::FRONT_END_FILES[..=parser].iter().map(|(_, t)| *t).collect::<Vec<_>>().join("\n");
    load_lowered(scheme, &text)
}

/// Each of `entries`, called by `{prefix}{name}` from Scheme, run as the
/// register code in global `{native}{name}`. In one text: each text run
/// analyses all the session's Scheme again, some 50 ms, so one for each
/// would cost a second and a half.
fn entry_defines(entries: &[&str], native: &str, prefix: &str) -> String {
    entries.iter().map(|name| format!("(define ({prefix}{name} . args) (%run-front-end {native}{name} args))\n")).collect()
}

/// `text`, the front end or its first files, checked, licensed as the
/// reader, lowered and loaded.
fn load_lowered(scheme: &mut Session, text: &str) -> Result<(), String> {
    // An error in the front end says where in its files.
    let mut compiled = compile_program_as(text, READER_PREFIX)
        .map_err(|e| format!("the front end, {}: {}", crate::front_end_location(e.span.start as usize), e.message))?;
    compiled.checker.reader_licence()?;
    // The front end is the session's own, licensed code: loading it is not
    // the program's work, and counts against no step limit (as reading
    // with it does not, `read_with_own_reader`).
    let limit = scheme.engine.step_limit();
    scheme.engine.set_step_limit(None);
    let r = compiled.load_into(scheme);
    scheme.engine.set_step_limit(limit);
    r
}

/// A failure of the lowered Scheme, said as the other machines say it
/// (`DONE.md` §85): its message alone (`Session::bare_failures`), and a
/// A digest as a global's stamp: a fixnum, not negative, of 60 bits.
fn stamp_fixnum(digest: u64) -> i64 {
    (digest >> 4) as i64
}

/// A stamp of this process's own, for a definition whose value its form
/// does not decide (`definition_stamps`): no other session's code expects
/// it.
fn process_stamp() -> i64 {
    use std::hash::{BuildHasher, Hasher};
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    thread_local! { static SEED: std::collections::hash_map::RandomState = std::collections::hash_map::RandomState::new(); }
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    SEED.with(|s| {
        let mut h = s.build_hasher();
        h.write_u64(n);
        stamp_fixnum(h.finish())
    })
}

/// `car` or `cdr` of a non-pair, the one Scheme type check an FX-26
/// program can fail, in their words.
fn lowered_failure(m: String) -> String {
    if m == "expected a pair" { "car or cdr of a non-pair".into() } else { m }
}

/// Where the front end's register code is cached, if anywhere (native, the
/// front end after its first run: `save_native_front_end`), and the key
/// its file must start with: a heap image in the user's cache directory, one
/// file for each build of the sources (`FIXPT_BUILD_HASH`, `build.rs`),
/// shared by every executable built from them, and the key a hash of the
/// front end's text and of the build, so that a rebuilt compiler never
/// reads what an older one made. (Each executable had a cache of its own
/// before, which each test binary made at its first run: `TODO.md` §167.)
/// `FIXPT_NO_CACHE` turns it off.
fn front_end_cache(text: &str, native: bool) -> Option<(std::path::PathBuf, u64)> {
    use std::hash::{Hash, Hasher};
    if std::env::var_os("FIXPT_NO_CACHE").is_some() {
        return None;
    }
    // By the sources and the build (`build.rs`), not the executable: every
    // one built from them shares the cache, the CLI and each test binary.
    let build = env!("FIXPT_BUILD_HASH");
    let mut name = std::collections::hash_map::DefaultHasher::new();
    (build, native).hash(&mut name);
    let mut key = std::collections::hash_map::DefaultHasher::new();
    (text, build).hash(&mut key);
    let dir = crate::fasl::cache_dir()?;
    Some((dir.join(format!("front-end-{:016x}.img", name.finish())), key.finish()))
}

/// The front end's compiled word `w`, copied out of `heap` into a heap of
/// its own and written to `path` as an image after `key`: by a temporary
/// file renamed, so that a reader never sees half of one; then the caches
/// no longer wanted are removed (`sweep_cache`). Any failure only means no
/// cache.
fn save_front_end(heap: &fixpt_heap::Heap, w: fixpt_heap::Value, path: &std::path::Path, key: u64) {
    let mut alone = fixpt_heap::Heap::new();
    let copy = alone.copy_graph_from(heap, w);
    alone.push_root(copy);
    save_image(&alone, path, key);
}

/// The front end in the native convention after its first run (`TODO.md`
/// §126): what it gave (`pieces`, its entry points, native closures) and
/// all they reach, copied out of `heap` and written to `path` as an image
/// after `key`, as [`save_front_end`] writes its word. Its native code is
/// kept too, as ordinary bloblets, named in a list: the image's root is
/// `(pieces codes adapter)`, `adapter` the heap's native adapter's code if
/// they reach it (shared, not copied, when read back). The call-outs the
/// code makes are in its fields, each the call-out itself, encoded, the
/// same in every machine.
fn save_native_front_end(heap: &fixpt_heap::Heap, pieces: fixpt_heap::Value, standard: fixpt_heap::Value, path: &std::path::Path, key: u64) {
    use fixpt_heap::Value;
    let mut alone = fixpt_heap::Heap::new();
    // The shared stub first, where a session's heap has it when the image
    // is read, so that the image can go where it was made (`TODO.md` §160).
    alone.foreign_stub();
    let (copy, made) = alone.copy_graph_with(heap, pieces, |_| false, &Default::default());
    let adapter = heap.adapter_code().filter(|a| made.contains_key(&a.raw()));
    let mut codes = Value::NULL;
    for (&k, &c) in &made {
        let v = Value::from_raw(k);
        if heap.code_part(v) == Some(fixpt_heap::CodePart::Native) && Some(v) != adapter {
            codes = alone.cons(c, codes);
        }
    }
    let adapter = adapter.map_or(Value::FALSE, |a| made[&a.raw()]);
    // The standard environment as the reader written in FX-26 reads it
    // (`standard26`): the same at every start, read once (`TODO.md` §177).
    let standard = alone.copy_graph_from(heap, standard);
    let rest = alone.cons(standard, Value::NULL);
    let rest = alone.cons(adapter, rest);
    let rest = alone.cons(codes, rest);
    let root = alone.cons(copy, rest);
    alone.push_root(root);
    save_image(&alone, path, key);
}

/// What [`save_native_front_end`] kept, copied into `heap`, its code made
/// code again: the pieces; none if the image is not one, when the front
/// end is compiled and run as ever.
fn load_native_front_end(k: &NativeKeeping, heap: &mut fixpt_heap::Heap, file: &fixpt_heap::Mapped) -> Option<fixpt_heap::Value> {
    let bytes = file.get(CACHE_IMAGE_AT..)?;
    use fixpt_heap::Value;
    let img = fixpt_heap::image::parts(bytes, false).ok()?;
    let root = *img.roots.first()?;
    if !root.is_pair() || !img.cdr(root).is_pair() || !img.cdr(img.cdr(root)).is_pair() {
        return None;
    }
    let adapter = img.car(img.cdr(img.cdr(root)));
    // Spliced in, unless `FIXPT_IMAGE_COPY` asks for the copy of a graph
    // that the splice replaced (`TODO.md` §160): for debugging.
    // The standard environment read, kept with it, if it is (an older
    // cache has none).
    let standard_of = |h: &fixpt_heap::Heap, root: Value| {
        let rest = h.cdr(h.cdr(h.cdr(root)));
        if rest.is_pair() { h.car(rest) } else { Value::FALSE }
    };
    let (pieces, standard, made_code) = if std::env::var_os("FIXPT_IMAGE_COPY").is_some() {
        let from = fixpt_heap::image::load_trusted(bytes).ok()?;
        let root = *from.roots_slice().first()?;
        let code: std::collections::HashSet<u64> = list(&from, from.car(from.cdr(root))).iter().map(|c| c.raw()).collect();
        let mut given = std::collections::HashMap::new();
        if adapter != Value::FALSE {
            given.insert(from.car(from.cdr(from.cdr(root))).raw(), (k.adapter_code)(heap).ok()?);
        }
        let (copy, made) = heap.copy_graph_with(&from, from.car(root), |v| code.contains(&v.raw()), &given);
        let standard = standard_of(&from, root);
        let standard = if standard == Value::FALSE { standard } else { heap.copy_graph_from(&from, standard) };
        (copy, standard, code.iter().filter_map(|k| made.get(k).copied()).collect())
    } else {
        // This heap's adapter stands for the image's; if it has none yet,
        // the image's is its own, so that the image goes where it was made.
        let mine = heap.adapter_code().filter(|_| adapter != Value::FALSE);
        let given: Vec<(Value, Value)> = mine.map(|m| (adapter, m)).into_iter().collect();
        // A cache of this executable's that cannot be put in is said: the
        // front end is then made again at every run, as fast as from no
        // cache at all, and nothing else would show it.
        // Its static area mapped from the file where the splice is in place
        // (`TODO.md` §160 item 4), unless `FIXPT_IMAGE_NO_MAP` asks for it
        // copied.
        let map = std::env::var_os("FIXPT_IMAGE_NO_MAP").is_none().then_some(file);
        // Its code copied, not mapped, where `perf` is to name it by the
        // perf map (`FIXPT_PERF_MAP`): it names none of a file's
        // (`TODO.md` §179).
        let map_code = std::env::var_os("FIXPT_PERF_MAP").is_none();
        let spliced = heap.splice_image_from(&img, &given, map, map_code).inspect_err(|e| eprintln!("fixpt: the front end's cache could not be read ({e}); it is made again"));
        let root = *spliced.ok()?.first()?;
        let theirs = heap.car(heap.cdr(heap.cdr(root)));
        if mine.is_none() && theirs != Value::FALSE {
            heap.set_adapter_code(theirs);
        }
        (heap.car(root), standard_of(heap, root), list(heap, heap.car(heap.cdr(root))))
    };
    (k.note_code)(heap, &made_code);
    let pieces = heap.cons(pieces, standard);
    Some(pieces)
}

/// The elements of list `l` of `heap`'s.
fn list(heap: &fixpt_heap::Heap, mut l: fixpt_heap::Value) -> Vec<fixpt_heap::Value> {
    let mut out = Vec::new();
    while l.is_pair() {
        out.push(heap.car(l));
        l = heap.cdr(l);
    }
    out
}

/// Where in the front end's cache file its image starts: the page after its
/// key.
const CACHE_IMAGE_AT: usize = fixpt_heap::image::PAGE;

/// The text a program's register code is made of: `text`, then a product of
/// its `entries`, what the cache of it is keyed by (`front_end_cache`).
fn register_text(text: &str, entries: &[&str]) -> String {
    let fields: Vec<String> = entries.iter().enumerate().map(|(i, n)| format!("({} {n})", i + 1)).collect();
    format!("{text}\n(product {})\n", fields.join(" "))
}

/// `heap`, all of it, written to `path` as an image after `key`.
fn save_image(alone: &fixpt_heap::Heap, path: &std::path::Path, key: u64) {
    // The key, then the image on the file's next page (`CACHE_IMAGE_AT`),
    // so that it may be mapped from the file (`TODO.md` §165); its words the
    // static area's, so that where it is read nothing of it is copied by a
    // collection (`TODO.md` §161).
    let mut bytes = key.to_le_bytes().to_vec();
    bytes.resize(CACHE_IMAGE_AT, 0);
    bytes.extend(fixpt_heap::image::dump_static(alone));
    let Some(dir) = path.parent() else { return };
    if std::fs::create_dir_all(dir).is_err() {
        return;
    }
    let tmp = path.with_extension(format!("tmp{}", std::process::id()));
    if std::fs::write(&tmp, &bytes).is_ok() && std::fs::rename(&tmp, path).is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
    sweep_cache(dir);
}

/// How long a cache unused is kept (`sweep_cache`): a day. Each build of the
/// sources has caches of its own (`FIXPT_BUILD_HASH`), 20 MB each, so an
/// edit makes new ones and leaves the old to no one; a day keeps those of
/// another branch or profile still in use.
const CACHE_LIFE: std::time::Duration = std::time::Duration::from_secs(24 * 3600);
/// And at most this many front-end caches, the most recently used: two
/// kinds for each of a few builds (debug, release, a second tree).
const CACHE_MOST: usize = 8;

/// The caches in `dir` let go: front-end caches and the `.fasl`s of the
/// module files built in (`fasl::path_for_load`, made again by the next run
/// that wants them) unused for `CACHE_LIFE`, and the front-end caches past
/// the `CACHE_MOST` most recent. Done by whatever writes a front-end cache
/// (a process of the CLI, a test's session, `fixpt prewarm`): that is when
/// a build is new. Used is read or written, by the file's times (access
/// times may lag by a day where the file system keeps them `relatime`).
fn sweep_cache(dir: &std::path::Path) {
    let mut front_ends = Vec::new();
    for e in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let Ok(m) = e.metadata() else { continue };
        let used = [m.accessed().ok(), m.modified().ok()].into_iter().flatten().max();
        let old = used.and_then(|t| t.elapsed().ok()).is_some_and(|a| a > CACHE_LIFE);
        let name = e.file_name().to_string_lossy().into_owned();
        if name.starts_with("front-end-") {
            if old {
                let _ = std::fs::remove_file(e.path());
            } else {
                front_ends.push((used, e.path()));
            }
        } else if old && name.starts_with("built-in-") {
            let _ = std::fs::remove_dir_all(e.path());
        }
    }
    front_ends.sort_by(|a, b| b.0.cmp(&a.0));
    for (_, p) in front_ends.into_iter().skip(CACHE_MOST) {
        let _ = std::fs::remove_file(p);
    }
}

/// Each entry point in the product `pieces` (field `i + 1` its `i`th, in
/// slot `i + 2`) in a global of its own, `{native}{name}`.
fn set_entries(heap: &mut fixpt_heap::Heap, pieces: fixpt_heap::Value, entries: &[&str], native: &str) {
    for (i, name) in entries.iter().enumerate() {
        let piece = heap.bloblet_slot(pieces, 2 + i);
        let sym = heap.intern(&format!("{native}{name}"));
        let slot = heap.symbol_global_slot(sym);
        heap.set_global(slot, piece);
    }
}

/// The global prefix the bootstrap program is loaded under.
pub const BOOTSTRAP_PREFIX: &str = "fx26-boot:";

/// The bootstrap program ([`crate::bootstrap_program`]: the front end and
/// its driver) lowered to Scheme and loaded into `scheme` under
/// [`BOOTSTRAP_PREFIX`], so that each piece can be run and timed lowered,
/// as the compiled ones are.
pub fn load_bootstrap_program(scheme: &mut Session) -> Result<(), String> {
    let compiled = compile_program_as(&crate::bootstrap_program(), BOOTSTRAP_PREFIX).map_err(|e| e.to_string())?;
    compiled.load_into(scheme)
}

impl Compiled {
    /// Load into `scheme`: the FX-26 runtime, then the program.
    pub fn load_into(&self, scheme: &mut Session) -> Result<(), String> {
        if !scheme.is_bound("%fx26-unit") {
            scheme.eval_str("<fx26-runtime>", RUNTIME).map_err(|e| e.to_string())?;
        }
        // All in one evaluation: each recompiles the whole of the session's
        // program so far (`Prepared::update`), so one per form made loading
        // the front end quadratic in its forms.
        let all: String = self.code.iter().flat_map(|c| [c.as_str(), "\n"]).collect();
        scheme.eval_str("<fx26>", &all).map_err(|e| e.to_string())?;
        Ok(())
    }
}

/// What one form did.
pub struct Outcome {
    /// What checking found, as the REPL prints it after the value.
    pub top: Top,
    /// The Scheme it was lowered to, empty for a `define-type`.
    pub code: String,
    /// What it printed while it ran.
    pub printed: String,
    /// Its value, written; `None` for a definition. An error when running
    /// failed — which checking does not rule out: `(car nil)` is well typed.
    pub value: Result<Option<String>, String>,
}

/// What running an expression in the native convention did: ran, to a
/// value (written) or a trap; or was declined, and why (the compiler cannot
/// do something in it yet).
pub enum NativeRun {
    /// The value, as it is now: for the caller to write or keep at once,
    /// before anything allocates.
    Ran(Result<fixpt_heap::Value, String>),
    Declined(String),
}

/// How a driver runs an expression in the native convention: the closure
/// of a procedure of no arguments that computes it (made by the compiler
/// written in FX-26, with register code), in the runtime, with at most so
/// much fuel. The CLI's is `fixpt_native::direct`'s.
pub type NativeRunner = fn(&mut fixpt_runtime::Runtime, fixpt_heap::Value, u64) -> NativeRun;

/// A cellular closure compiled in the native convention by the compiler
/// written in FX-26 (`native-direct-x64.fx`), the driver's (`fixpt_native::
/// direct`'s `fx_begin` …) being the CLI's: a native closure of the same
/// code over the same values, or why not. It runs FX-26, so it is given
/// the Scheme session, and the closure rooted.
pub type NativeFx = fn(&mut fixpt_scheme::Session, fixpt_scheme::Handle) -> Result<fixpt_scheme::Handle, String>;

/// How the front end's native code is kept in the cache and read back
/// (`TODO.md` §126). The CLI's are `fixpt_native::direct`'s.
#[derive(Clone, Copy)]
pub struct NativeKeeping {
    /// The heap's native adapter's code, shared.
    pub adapter_code: fn(&mut fixpt_heap::Heap) -> Result<fixpt_heap::Value, String>,
    /// Code read back, named for `FIXPT_SYMBOLS` and perf.
    pub note_code: fn(&fixpt_heap::Heap, &[fixpt_heap::Value]),
}

/// A cellular closure compiled in the native convention: a native closure
/// of the same code over the same values, or why not.
pub type NativeCompiler = fn(&mut fixpt_heap::Heap, fixpt_heap::Value) -> Result<fixpt_heap::Value, String>;

/// Whether a redefinition goes ahead that would break definitions (those
/// that use the name and would no longer check). To keep a value as it was
/// instead, a program binds it: `(define d (let ((g g)) …))`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Redefine {
    /// Those that still check run again; the rest are broken, unusable
    /// until they are defined again. What a REPL does unless told otherwise.
    Break,
    /// The redefinition is refused, and nothing changes.
    Refuse,
}

/// A redefinition that would break definitions, for a driver to decide
/// (`Fx26Session::redefine`): the names redefined, each definition that
/// would no longer check and why, and those that would run again.
pub struct Redefinition {
    pub names: Vec<String>,
    pub breaking: Vec<(String, String)>,
    pub rerun: Vec<String>,
}

/// How a checked form is run.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub enum Strategy {
    /// Lowered to annotated Scheme and run on the session's engine.
    #[default]
    Lower,
    /// Run by the evaluator written in FX-26 (`eval-core.fx`).
    Evaluate,
    /// Compiled to a cellular word by the compiler written in FX-26
    /// (`compile.fx`) and run on the cellular machine.
    Cellular,
}

impl Fx26Session {
    pub fn with_backend(backend: fixpt_engine::Backend) -> R<Fx26Session> {
        Fx26Session::with_backend_preloaded(backend, None)
    }

    /// [`with_backend`](Fx26Session::with_backend), and where `keeping`
    /// says the front end is native, its cache read into the heap before
    /// the runtime and the prelude put anything there (`TODO.md` §161), so
    /// that their symbols are the image's, and nothing of it is written to
    /// make them one. The session then uses it as its front end
    /// (`as_register_code`), with `front_end_native` and `native_keeping`
    /// set as the cache was made.
    pub fn with_backend_preloaded(backend: fixpt_engine::Backend, keeping: Option<NativeKeeping>) -> R<Fx26Session> {
        Fx26Session::with_backend_preloaded_in(backend, keeping, false, Strategy::Lower)
    }

    /// [`with_backend_preloaded`](Fx26Session::with_backend_preloaded), its
    /// checker of the native convention if `native`, made so at once: not
    /// made cellular and then again native
    /// ([`set_native_convention`](Fx26Session::set_native_convention)), each
    /// some 2 ms of a start (`TODO.md` §177); and its strategy `strategy`.
    /// Its forms not lowered, the prelude's data (`PRELUDE_DATA`) is left
    /// out, some 2 ms more, until the session lowers one
    /// (`whole_prelude`).
    pub fn with_backend_preloaded_in(
        backend: fixpt_engine::Backend,
        keeping: Option<NativeKeeping>,
        native: bool,
        strategy: Strategy,
    ) -> R<Fx26Session> {
        let preload = |heap: &mut fixpt_heap::Heap| -> Option<fixpt_heap::Value> {
            let k = keeping?;
            let text = register_text(&crate::front_end(), &Self::FRONT_ENTRIES);
            let (path, key) = front_end_cache(&text, true)?;
            let b = fixpt_heap::Mapped::open(&path).ok()?;
            if b.get(..8)? != key.to_le_bytes() {
                return None;
            }
            load_native_front_end(&k, heap, &b)
        };
        let lowered = strategy == Strategy::Lower;
        let prelude = if lowered { fixpt_scheme::PRELUDE } else { fixpt_scheme::PRELUDE_CONTROL };
        let mut scheme = Session::with_prelude_preloaded(backend, prelude, preload);
        scheme
            .eval_str("<fx26-runtime>", RUNTIME)
            .map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), format!("the FX-26 runtime failed to load: {e}")))?;
        scheme.engine.set_step_limit(Some(DEFAULT_STEP_LIMIT));
        scheme.runtime_unrooted().type_at = Some(crate::typeat::type_at);
        // The front end run as register code (`front_end_compiled`), read
        // back from its cache, on the hand register machine (where no
        // machine code runs, the cellular machine written in Rust): lowered,
        // on the bytecode VM, it is some 30 times as slow, and loading it
        // took most of a session's start, a test's (`TODO.md` §167). A
        // caller that wants it lowered says so.
        scheme.runtime_unrooted().front_end_run_word.get_or_insert(if fixpt_native::CELLULAR_AVAILABLE {
            fixpt_native::cellular::run_word_registers
        } else {
            fixpt_engine::cellular::run_word
        });
        Ok(Fx26Session {
            checker: if native { Checker::with_convention(crate::ast::Conv::Native) } else { Checker::new() },
            scheme,
            globals: Globals::default(),
            strategy,
            prelude_data_pending: !lowered,
            register_code: false,
            front_end_compiled: true,
            front_end_native: false,
            native_keeping: None,
            native_convention: false,
            native_runner: None,
            native_compiler: None,
            native_fx: None,
            globals_effects: true,
            defer_reruns: false,
            breaks_held: false,
            own_made: false,
            own_begun: false,
            shared_made: Default::default(),
            built_ins_cached: Default::default(),
            source_file: None,
            source_form: None,
            source_loaded: std::collections::HashMap::new(),
            redefine: None,
            next_redefine: None,
            show_words: false,
            words_shown: Default::default(),
            standard26: None,
            eval_base: 0,
            step_limit: Some(DEFAULT_STEP_LIMIT),
            speculation_limit: Some(SPECULATION_STEP_LIMIT),
            pending: Vec::new(),
            fasls: std::env::var_os("FIXPT_NO_FASL").is_none(),
            fasl_cellular: false,
            program_file: None,
            program_record: None,
            program_ran: Default::default(),
        })
    }

    /// How many steps a form may take when run (`DEFAULT_STEP_LIMIT` to
    /// start with), or `None` for no limit.
    pub fn set_step_limit(&mut self, limit: Option<u64>) {
        self.step_limit = limit;
        self.scheme.engine.set_step_limit(limit);
    }

    pub fn step_limit(&self) -> Option<u64> {
        self.step_limit
    }

    /// Check one top-level form and lower it, without running it.
    pub fn compile(&mut self, form: &Syntax) -> R<(Top, String)> {
        compile_form(&mut self.checker, &mut self.globals, form)
    }

    /// Run `form` early, if the licence allows: check it without keeping
    /// anything, and run it only if it is an expression whose effect is
    /// licensed for a driver that owns no region of the program's. That
    /// leaves allocation, and effects on regions inference made fresh for
    /// this form alone, which masking has already removed. The run has a
    /// budget of its own, since speculation must not hang the editor.
    pub fn speculate(&mut self, form: &Syntax) -> Speculation {
        let code = self.checker.try_top(form, |c, r| match r {
            Err(e) => Err(Speculation::Rejected(e.message)),
            Ok(Top::Exp(k)) => match crate::licence::unlicensed(&k.effect, &[]) {
                Some(a) => Err(Speculation::NotLicensed(c.show_atom(a))),
                None => Ok(lower(c, &self.globals, k.exp)),
            },
            Ok(_) => Err(Speculation::NotAnExpression),
        });
        let code = match code {
            Ok(code) => code,
            Err(s) => return s,
        };
        // Run as the session runs forms: the definitions before it are where
        // its strategy put them, not in the lowered program's globals.
        if self.strategy != Strategy::Lower {
            return self.speculate_own(&fixpt_read::write_syntax(form, &self.checker.interner));
        }
        self.whole_prelude();
        self.scheme.engine.set_step_limit(self.speculation_limit);
        let result = self.scheme.scope(|s| {
            let (_, result) = s.eval_capturing("<fx26-speculative>", &code);
            result.map(|v| s.write(v))
        });
        self.scheme.engine.set_step_limit(self.step_limit);
        match result {
            Ok(v) => Speculation::Value(v),
            Err(e) => Speculation::Failed(e.to_string()),
        }
    }

    /// What entering `forms`, a REPL entry, would do with the entries
    /// pending: run alone if it checks alone, or if it defines no type; with
    /// them, if together they lack nothing; else wait, if it defines a type
    /// and only types are missing. Nothing is kept.
    pub fn consider(&mut self, forms: &[Syntax]) -> Consider {
        let c = &mut self.checker;
        let defines_type = forms.iter().any(|f| f.as_proper_list().and_then(|l| l.first()?.as_symbol()).is_some_and(|h| c.interner.name(h) == "define-type"));
        if !defines_type {
            return Consider::Run;
        }
        let alone = c.missing_types(forms);
        if alone.as_ref().is_some_and(|m| m.is_empty()) {
            return Consider::Run;
        }
        let names = |c: &Checker, ms: Vec<Sym>| ms.into_iter().map(|m| c.interner.name(m).to_string()).collect::<Vec<_>>();
        if !self.pending.is_empty() {
            let group: Vec<Syntax> = self.pending.iter().flat_map(|p| p.forms.iter().cloned()).chain(forms.iter().cloned()).collect();
            match self.checker.missing_types(&group) {
                Some(m) if m.is_empty() => return Consider::Completes(self.pending.iter().flat_map(|p| p.defines.iter().cloned()).collect()),
                Some(m) => return Consider::Pends(names(&self.checker, m)),
                None => {}
            }
        }
        match alone {
            Some(m) if !m.is_empty() => Consider::Pends(names(&self.checker, m)),
            _ => Consider::Run,
        }
    }

    /// `forms`, an entry `consider` said waits, held.
    pub fn hold(&mut self, forms: &[Syntax]) {
        let c = &self.checker;
        let mut defines = Vec::new();
        for f in forms {
            let l = f.as_proper_list().unwrap_or(&[]);
            match (l.first().and_then(|h| h.as_symbol()).map(|h| c.interner.name(h)), l.get(1).and_then(|n| n.as_symbol())) {
                (Some("define-type"), Some(n)) => defines.push(c.interner.name(n).to_string()),
                _ => defines.extend(c.defined_names(f).into_iter().map(|n| c.interner.name(n).to_string())),
            }
        }
        self.pending.push(Pending { forms: forms.to_vec(), defines });
    }

    /// The pending entries, and `forms` after them, run as a program's
    /// forms are; none pending after.
    pub fn complete(&mut self, forms: &[Syntax]) -> R<Vec<R<Outcome>>> {
        let group: Vec<Syntax> = std::mem::take(&mut self.pending).into_iter().flat_map(|p| p.forms).chain(forms.iter().cloned()).collect();
        self.run_forms(&group)
    }

    /// What the pending entries still lack, as `consider` would find it.
    pub fn awaiting(&mut self) -> Vec<String> {
        let group: Vec<Syntax> = self.pending.iter().flat_map(|p| p.forms.iter().cloned()).collect();
        if group.is_empty() {
            return Vec::new();
        }
        let m = self.checker.missing_types(&group).unwrap_or_default();
        m.into_iter().map(|m| self.checker.interner.name(m).to_string()).collect()
    }

    /// An expression (text), licensed, run early by the pieces written in
    /// FX-26 as `run_checked` runs one, on the speculation budget: natively
    /// if it can be, else as cellular code, or by the evaluator.
    fn speculate_own(&mut self, text: &str) -> Speculation {
        let saved = self.step_limit;
        self.step_limit = self.speculation_limit;
        let r = self.run_expression_own(text);
        self.step_limit = saved;
        self.scheme.engine.set_step_limit(saved);
        self.scheme.scope(|s| s.runtime_unrooted().heap.regions_exit_to(0));
        match r {
            Ok(Ok(v)) => Speculation::Value(v),
            Ok(Err(e)) | Err(FxError { message: e, .. }) => Speculation::Failed(e),
        }
    }

    fn run_expression_own(&mut self, text: &str) -> R<Result<String, String>> {
        if let (Some(run), Strategy::Cellular) = (self.native_runner, self.strategy) {
            let fuel = self.step_limit.unwrap_or(u64::MAX >> 1);
            let written = |rt: &mut fixpt_runtime::Runtime, clo| match run(rt, clo, fuel) {
                NativeRun::Ran(v) => Ok(v.map(|v| fixpt_runtime::write_value(&rt.heap, v))),
                NativeRun::Declined(why) => Err(why),
            };
            if let Ok(Ok(value)) = self.with_native_thunk(text, written)? {
                return Ok(value);
            }
        }
        let out = match self.strategy {
            Strategy::Evaluate => self.eval_form(&format!("{text}\n"))?,
            _ => self.compile_form_showing(&format!("{text}\n"), false)?.0,
        };
        Ok(match out.strip_prefix("!! ") {
            Some(e) => Err(e.to_string()),
            None => Ok(out),
        })
    }

    /// Run the forms of a whole program, its type abbreviations first. One
    /// outcome per form still to run; the abbreviations are done in the
    /// first pass and have none. Redefinition is as at the REPL.
    pub fn run_forms(&mut self, forms: &[Syntax]) -> R<Vec<R<Outcome>>> {
        self.checker.fasls = self.reads_fasls();
        let done = self.checker.declare_ahead(forms)?;
        // The type definitions, declared ahead, are the pieces written in
        // FX-26's too, first: all in one text, so that its checker declares
        // them ahead as well, and they may name each other.
        if self.strategy != Strategy::Lower {
            let ahead: Vec<&Syntax> = forms.iter().zip(&done).filter(|(_, d)| **d).map(|(f, _)| f).collect();
            let text: String = ahead.iter().map(|f| format!("{}\n", fixpt_read::write_syntax(f, &self.checker.interner))).collect();
            if let (Some(first), false) = (ahead.first(), text.is_empty()) {
                let out = match self.strategy {
                    Strategy::Evaluate => self.eval_form(&text)?,
                    _ => self.compile_form_showing(&text, false)?.0,
                };
                if let Some(e) = out.strip_prefix("!! ") {
                    return Err(FxError::at(first.span, e.to_string()));
                }
            }
        }
        // What the reader made of a `define-generative` declared ahead (its
        // `up-` and `down-`, which have its span) the pieces written in
        // FX-26 made of it themselves, above, in its context. (A datatype's
        // constructors they are given as the reader made them.)
        let generative = |f: &Syntax| {
            f.as_proper_list().and_then(|l| l.first()?.as_symbol()).is_some_and(|h| self.checker.interner.name(h) == "define-generative")
        };
        let ahead: Vec<Span> = forms.iter().zip(&done).filter(|(f, d)| **d && generative(f)).map(|(f, _)| f.span).collect();
        // The program's `.fasl`, if it has a fresh one: its procedures'
        // definitions read from it, the rest of its forms run here.
        let fasl = match self.program_file.clone() {
            Some(p) if self.reads_fasls() && self.program_record.is_none() => self.program_fasl(&p, forms),
            _ => None,
        };
        let mut outs = Vec::new();
        for (i, (f, done)) in forms.iter().zip(done).enumerate() {
            if !done {
                self.own_made = self.strategy != Strategy::Lower && ahead.contains(&f.span);
                let out = match fasl.as_ref().and_then(|p| Some((p, p.defs.get(&i)?))) {
                    Some((p, group)) => self.run_program_def(f, group, p).map(|o| vec![o]),
                    None => self.run_each(f),
                };
                // What the pieces written in FX-26 made themselves (a
                // generative's conversions) is not the program's to keep.
                if let (Some(r), Ok(each), false) = (self.program_record.as_mut(), &out, self.own_made) {
                    r.extend(each.iter().map(|o| (i, o.top.clone(), o.printed.clone())));
                }
                self.own_made = false;
                // Only a form refused ends the run; one that failed as it
                // ran does not.
                match out {
                    Ok(each) => outs.extend(each.into_iter().map(Ok)),
                    Err(e) => {
                        outs.push(Err(e));
                        break;
                    }
                }
            }
        }
        Ok(outs)
    }

    /// `run`, each outcome: of a top-level `include`, the forms it is made
    /// (`include_forms`), each run as one, so that each front end is given
    /// them, until one fails; of any other form, its own.
    pub fn run_each(&mut self, form: &Syntax) -> R<Vec<Outcome>> {
        let Some(forms) = self.checker.include_forms(form)? else { return Ok(vec![self.run(form)?]) };
        if forms.is_empty() {
            return Err(FxError::at(form.span, "this module gives nothing to include"));
        }
        let mut out = Vec::new();
        for f in &forms {
            let o = self.run(f)?;
            let failed = o.value.is_err();
            out.push(o);
            if failed {
                break;
            }
        }
        Ok(out)
    }

    /// Check one top-level form, and run it as `strategy` says: lowered to
    /// Scheme, or through the evaluator or the compiler written in FX-26,
    /// which are given the form as text and read and parse it themselves.
    /// Checking comes first either way, so a form that does not check does
    /// not run.
    pub fn run(&mut self, form: &Syntax) -> R<Outcome> {
        self.checker.fasls = self.reads_fasls();
        // `(compile-file "path")`: the file's `.fasl` made, as `fixpt
        // compile-file` makes it (`compile_file`).
        if let Some((path, program)) = compile_file_form(form, &self.checker) {
            let made = self.compile_file(&path, program).map_err(|e| FxError::at(form.span, e))?;
            let printed = format!("; compiled `{path}` to `{}`\n", made.display());
            let exp = self.checker.arena.exp(form.span, crate::ast::Exp::Unit);
            let top = Top::Exp(crate::check::Checked { ty: self.checker.unit, effect: crate::ast::Effect::pure(), exp });
            return Ok(Outcome { top, code: String::new(), printed, value: Ok(None) });
        }
        // A top-level `include`: its forms' outcomes, the last shown.
        if self.checker.include_forms(form)?.is_some() {
            let mut each = self.run_each(form)?;
            let printed: String = each.iter().map(|o| o.printed.as_str()).collect();
            let mut last = each.pop().expect("an `include` makes forms");
            last.printed = printed;
            return Ok(last);
        }
        let out = self.run_defining(form);
        // A run that failed leaves no process to resume: a failure in any
        // ends the run (`docs/fx26.md`, "Processes").
        let failed = !matches!(&out, Ok(o) if o.value.is_ok());
        if !failed {
            self.cache_built_ins();
        }
        // No body of a region runs once a form is done: any region still
        // live was left by an error, or an escape no prompt ended.
        self.scheme.scope(|s| {
            let heap = &mut s.runtime_unrooted().heap;
            if failed {
                fixpt_runtime::sched::reset(heap);
            }
            heap.regions_exit_to(0)
        });
        out
    }

    /// `text`, about to be compiled, as a source of the form last run, if
    /// sources are wanted (`crate::sources::wanted`): its number; else 0.
    fn source_of(&mut self, text: &str) -> u32 {
        if !crate::sources::wanted() {
            return 0;
        }
        for (path, ftext, id) in self.checker.loaded.values() {
            self.source_loaded.entry(*id).or_insert_with(|| std::rc::Rc::new((path.clone(), ftext.clone())));
        }
        let loaded = self.source_loaded.iter().map(|(id, f)| (*id, f.clone())).collect();
        crate::sources::register(text, self.source_form.clone(), self.source_file.clone(), loaded)
    }

    /// A whole program begins with no process from one before.
    fn processes_forgotten(&mut self) {
        self.scheme.scope(|s| fixpt_runtime::sched::reset(&mut s.runtime_unrooted().heap));
    }

    /// `form`, run under redefinition (`Checker::top_defining`), as the
    /// language says for files and the REPL alike. Only whether a
    /// redefinition that would break definitions goes ahead is the driver's
    /// to decide (`Redefine`): asked, or said ahead, before anything changes.
    fn run_defining(&mut self, form: &Syntax) -> R<Outcome> {
        let names = self.checker.defined_names(form);
        let shown = |c: &Checker, ns: &[Sym]| ns.iter().map(|n| format!("`{}`", c.interner.name(*n))).collect::<Vec<_>>().join(", ");
        if names.iter().any(|n| self.checker.global_type(*n).is_some())
            && let Ok(trial) = self.checker.try_defining(form)
            && !trial.broken.is_empty()
        {
            let choice = self.next_redefine.take().unwrap_or_else(|| {
                let q = Redefinition {
                    names: names.iter().map(|n| self.checker.interner.name(*n).to_string()).collect(),
                    breaking: trial.broken.iter().map(|(ns, why)| (shown(&self.checker, ns), why.clone())).collect(),
                    rerun: trial.run[1..].iter().map(|(_, f)| shown(&self.checker, &self.checker.defined_names(f))).collect(),
                };
                self.redefine.map_or(Redefine::Break, |ask| ask(&q))
            });
            if choice == Redefine::Refuse {
                let list: Vec<String> = trial.broken.iter().map(|(ns, why)| format!("{}: {why}", shown(&self.checker, ns))).collect();
                return Err(FxError::at(form.span, format!("{} not redefined: it would break {}", shown(&self.checker, &names), list.join("; "))));
            }
        }
        let redefined = names.iter().any(|n| self.checker.global_type(*n).is_some());
        let done = self.checker.top_defining(form)?;
        let reran: Vec<Sym> = done.run[1..].iter().flat_map(|(_, f)| self.checker.defined_names(f)).collect();
        let mut notes = String::new();
        // The hidden globals of the files it loads first, quietly.
        let mut first = String::new();
        for (top, f) in done.hoisted {
            let shared = match &top {
                Top::Define { name, .. } => self.checker.interner.name(*name).strip_prefix("%shared:").map(str::to_string),
                _ => None,
            };
            // A syscall's hidden global, whether the runtime has it: the
            // front end written in FX-26 makes it itself, from the
            // declaration (`syscall.rs`), as the Rust lowering does not.
            let syscall = matches!(&top, Top::Define { name, .. }
                if self.checker.interner.name(*name).starts_with(crate::syscall::AVAILABLE));
            if syscall && self.strategy != Strategy::Lower {
                continue;
            }
            let mut o = self.run_checked(top, &f, false)?;
            if o.value.is_err() {
                o.printed.insert_str(0, &first);
                // A required syscall's check failed: said of the declaration.
                if syscall {
                    o.top = done.run[0].0.clone();
                }
                return Ok(o);
            }
            self.shared_made.extend(shared);
            first.push_str(&o.printed);
        }
        let mut out = None;
        for (i, (top, f)) in done.run.into_iter().enumerate() {
            let o = self.run_checked(top, &f, i > 0)?;
            if i == 0 {
                out = Some(o);
            } else if let Err(e) = &o.value {
                notes.push_str(&format!("; {} failed as it ran again: {e}\n", shown(&self.checker, &self.checker.defined_names(&f))));
            }
        }
        let mut out = out.expect("the form itself runs first");
        out.printed.insert_str(0, &first);
        match &out.top {
            Top::Define { assigns: true, .. } | Top::DefineRec { assigns: true, .. } => {
                out.printed.push_str(&format!("; {} redefined: every use sees the new one\n", shown(&self.checker, &names)));
            }
            _ if redefined => {
                out.printed.push_str(&format!("; {} redefined", shown(&self.checker, &names)));
                if !reran.is_empty() {
                    out.printed.push_str(&format!("; run again, as they use it: {}", shown(&self.checker, &reran)));
                }
                out.printed.push('\n');
            }
            _ => {}
        }
        if !done.broken.is_empty() {
            let list: Vec<String> = done.broken.iter().map(|(ns, why)| format!("{} ({why})", shown(&self.checker, ns))).collect();
            out.printed.push_str(&format!("; broken until defined again: {}\n", list.join("; ")));
        }
        out.printed.push_str(&notes);
        Ok(out)
    }

    /// The next definition of `name` the compiler written in FX-26 makes a
    /// global for keeps the one it has: for a definition run in the native
    /// convention, which makes its global so (`native_define`).
    fn keep_global(&mut self, name: Sym) -> R<()> {
        if self.own_begun {
            let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
            let text = self.checker.interner.name(name).to_string();
            let mark = self.scheme.root_mark();
            let sym = self.scheme.make(|m| m.heap().intern(&text));
            let r = self.scheme.call_global(&format!("{READER_PREFIX}compile-keep-global!"), &[sym]).map_err(fail);
            self.scheme.release_to(mark);
            r?;
        }
        Ok(())
    }

    /// `top`, checked from `form`, run as `strategy` says; `again` when it
    /// is a definition run again for a redefinition, which the pieces
    /// written in FX-26 do themselves as they compile the redefinition,
    /// but which the native convention's definitions and the lowering do
    /// here.
    fn run_checked(&mut self, top: Top, form: &Syntax, again: bool) -> R<Outcome> {
        // Each global it defines left its definition's stamp by the write
        // that defines it (`definition_stamps`).
        let assigns = matches!(&top, Top::Define { assigns: true, .. } | Top::DefineRec { assigns: true, .. });
        // The pieces written in FX-26, which compile the definition, loaded
        // first, so that no definition goes unstamped for being early.
        if self.strategy == Strategy::Cellular && matches!(&top, Top::Define { .. } | Top::DefineRec { .. }) {
            self.own_pieces()?;
        }
        self.released(|s| {
            let stamps = s.definition_stamps(&top, form);
            s.plan_stamps(&stamps, assigns)
        })?;
        let r = self.run_checked_in(top, form, again);
        self.scheme.runtime_unrooted().heap.forget_planned_writes();
        // The breaks a native definition's check made, held while its value
        // was checked again (`native_define`), put back, on every path.
        let back = self.hold_breaks(false);
        let out = r?;
        back?;
        Ok(out)
    }

    /// The stamp each global `top` defines is left with
    /// (`layout::cellular::GLOBAL_WRITES`), which the guards compiled code
    /// keeps test: the same for the same definition in any session, from
    /// its source or a `.fasl`, so that code a `.fasl` keeps finds its
    /// assumptions hold where they do, and only there. A load's, its file's
    /// stamp (`fasl::stamp`: its text and its loads'). Another's, a digest
    /// of its form, its name, its type and the stamps of the globals it
    /// reads, if that is all its making does (a `lambda`'s does nothing);
    /// else one of this process's own, which no other session's code
    /// expects. A write when the program runs counts on from it (`setglbl`),
    /// so that a guard expecting the stamp fails after one.
    fn definition_stamps(&mut self, top: &Top, form: &Syntax) -> Vec<(Sym, i64)> {
        use std::hash::{Hash, Hasher};
        // Only compiled code keeps guards, and only the compiler written in
        // FX-26 finds its cells (`run_checked` loads it first).
        if self.strategy != Strategy::Cellular || !self.scheme.is_bound(&format!("{READER_PREFIX}compile-global-cell")) {
            return Vec::new();
        }
        let defined: Vec<(Sym, crate::ast::TyId, Option<crate::ast::Effect>)> = match top {
            Top::Define { name, ty, effect, .. } => vec![(*name, *ty, Some(effect.clone()))],
            Top::DefineRec { bindings, .. } => bindings.iter().map(|(n, t, _)| (*n, *t, None)).collect(),
            _ => return Vec::new(),
        };
        let text = fixpt_read::write_syntax(form, &self.checker.interner);
        let mut out = Vec::new();
        for (name, ty, effect) in defined {
            if let Some(f) = self.checker.shared_files.get(&name) {
                out.push((name, stamp_fixnum(f.stamp)));
                continue;
            }
            let reads: Option<Vec<Sym>> = match &effect {
                None => Some(Vec::new()),
                Some(e) => e.0.iter().map(|a| match a {
                    crate::ast::Atom::Read(crate::ast::Region::Global(g)) => Some(g.clone()),
                    _ => None,
                }).collect(),
            };
            let Some(mut reads) = reads else {
                out.push((name, process_stamp()));
                continue;
            };
            reads.sort_by_key(|g| self.checker.interner.name(*g).to_string());
            let mut h = std::collections::hash_map::DefaultHasher::new();
            ("fixpt-stamp", self.checker.interner.name(name), &text, self.checker.show_ty(ty)).hash(&mut h);
            for g in reads {
                let n = self.checker.interner.name(g).to_string();
                let w = self.global_cell(&n).ok().flatten().map(|c| {
                    let mut k = 0;
                    self.scheme.make(|m| {
                        let c = m.get(c);
                        k = m.heap().bloblet_slot(c, fixpt_heap::layout::cellular::GLOBAL_WRITES).as_fixnum();
                        fixpt_heap::Value::FALSE
                    });
                    k
                });
                (n, w).hash(&mut h);
            }
            out.push((name, stamp_fixnum(h.finish())));
        }
        out
    }

    /// `stamps` planned: a global the form writes again (`assigns`) left one
    /// short of its stamp now; one it makes a cell for, made so
    /// (`Heap::plan_global_writes`). Its one write then leaves the stamp,
    /// which code compiled for the form expects of it (`writes_expected`).
    fn plan_stamps(&mut self, stamps: &[(Sym, i64)], assigns: bool) -> R<()> {
        for &(name, stamp) in stamps {
            let shown = self.checker.interner.name(name).to_string();
            let cell = if assigns { self.global_cell(&shown)? } else { None };
            self.scheme.make(|m| {
                match cell {
                    Some(c) => {
                        let g = m.get(c);
                        m.heap().set_bloblet_slot(g, fixpt_heap::layout::cellular::GLOBAL_WRITES, fixpt_heap::Value::fixnum(stamp - 1));
                    }
                    None => m.heap().plan_global_writes(&shown, stamp - 1),
                }
                fixpt_heap::Value::FALSE
            });
        }
        Ok(())
    }

    /// Whether the FX-26 checker holds aside the breaks its last check made
    /// (`check-hold-breaks!`), so that the checks after see the definitions
    /// as that check did: on while a native definition's value is checked
    /// again, after the definition was; off when the definition is done.
    fn hold_breaks(&mut self, on: bool) -> R<()> {
        if self.breaks_held == on {
            return Ok(());
        }
        // Its handles released at its end, as `native_define`'s are.
        let mark = self.scheme.root_mark();
        let v = self.scheme.make(|_| fixpt_heap::Value::boolean(on));
        let r = self.scheme.call_global(&format!("{READER_PREFIX}check-hold-breaks!"), &[v]);
        self.scheme.release_to(mark);
        r.map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), e.to_string()))?;
        self.breaks_held = on;
        Ok(())
    }

    /// Tell the checker written in FX-26 that the text it checks next is a
    /// module file built in, or no longer (`check-built-in!`).
    fn check_built_in(&mut self, on: bool) -> R<()> {
        self.own_pieces()?;
        let mark = self.scheme.root_mark();
        let v = self.scheme.make(|_| fixpt_heap::Value::boolean(on));
        let r = self.scheme.call_global(&format!("{READER_PREFIX}check-built-in!"), &[v]);
        self.scheme.release_to(mark);
        r.map(|_| ()).map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), e.to_string()))
    }

    fn run_checked_in(&mut self, top: Top, form: &Syntax, again: bool) -> R<Outcome> {
        if self.strategy == Strategy::Lower {
            self.whole_prelude();
        }
        // What runs natively is typed so: a call typed `cellular` is made
        // with no look at its callee (`TODO.md` §97).
        debug_assert!(self.native_runner.is_none() || self.native_convention, "native code in the cellular convention");
        // And the closures cellular code makes then are made native (`nclosure`).
        debug_assert!(!self.native_convention || self.scheme.runtime_unrooted().adapt.is_some(), "no adapters in the native convention");
        let code = lower_top(&self.checker, &mut self.globals, &top);
        if self.strategy != Strategy::Lower {
            // A program's file being compiled to a `.fasl`: only a
            // procedure's definition, a type's and a load run; another
            // definition is checked and given its global, an expression
            // checked, neither run (`compile_program_file`).
            if self.program_record.is_some() && !again {
                match &top {
                    Top::Exp(_) => return Ok(Outcome { top, code: String::new(), printed: String::new(), value: Ok(None) }),
                    // One that only reads globals whose definitions ran runs
                    // too: making it does nothing else (a module of
                    // procedures, say).
                    Top::Define { name, exp, effect, .. } if !Self::names_its_word(&self.checker, *exp) && !self.checker.interner.name(*name).starts_with('%') => {
                        if !self.only_reads_ran(effect) {
                            self.declare_only(form)?;
                            return Ok(Outcome { top, code: String::new(), printed: String::new(), value: Ok(None) });
                        }
                    }
                    _ => {}
                }
                self.program_ran.extend(self.checker.defined_names(form));
            }
            // A load read from its `.fasl`: its hidden global given the
            // value kept there, not made.
            if let Top::Define { name, .. } = &top
                && let Some((fasl, _)) = self.checker.shared_files.get(name).and_then(|f| f.fasl.clone())
            {
                let name = *name;
                let value = self.fasl_define(name, form, &fasl)?;
                return Ok(Outcome { top, code: String::new(), printed: String::new(), value });
            }
            if self.own_made {
                // What the native compiler declines runs as cellular code,
                // which is slower: said, with why.
                let mut printed = String::new();
                if let (Top::Define { name, .. }, Some(compile)) = (&top, self.native_compiler)
                    && let Err(why) = self.compile_global_natively(*name, compile)?
                {
                    let name = self.checker.interner.name(*name);
                    printed = format!("; `{name}` is not in the native convention yet, so it runs as cellular code: {why}\n");
                }
                return Ok(Outcome { top, code: String::new(), printed, value: Ok(None) });
            }
            if again && self.native_runner.is_none() {
                return Ok(Outcome { top, code: String::new(), printed: String::new(), value: Ok(None) });
            }
            let form_text = if crate::sources::wanted() {
                let (text, map) = fixpt_read::write_syntax_mapped(form, &self.checker.interner);
                self.source_form = Some((text.clone(), map));
                text
            } else {
                fixpt_read::write_syntax(form, &self.checker.interner)
            };
            // An expression, in the native convention: as a procedure of no
            // arguments, compiled and called; what the compiler declines
            // runs as cellular code, saying why.
            let mut note = String::new();
            if let (Some(run), Top::Exp(_), Strategy::Cellular) = (self.native_runner, &top, self.strategy) {
                let fuel = self.step_limit.unwrap_or(u64::MAX >> 1);
                let written = |rt: &mut fixpt_runtime::Runtime, clo| {
                    // The runner compiles to machine code first, and counts
                    // that as compiling; the rest is the run.
                    let (start, compiled) = (std::time::Instant::now(), rt.compile_nanos);
                    let ran = run(rt, clo, fuel);
                    rt.run_nanos += (start.elapsed().as_nanos() as u64).saturating_sub(rt.compile_nanos - compiled);
                    match ran {
                        NativeRun::Ran(v) => Ok(v.map(|v| fixpt_runtime::write_value(&rt.heap, v))),
                        NativeRun::Declined(why) => Err(why),
                    }
                };
                match self.with_native_thunk(&form_text, written)? {
                    Ok(Ok(value)) => {
                        return Ok(Outcome { top, code: String::new(), printed: String::new(), value: value.map(Some) });
                    }
                    Ok(Err(why)) => note = format!("; not in the native convention yet, so run as cellular code: {why}\n"),
                    Err(why) => note = format!("; not compiled as a procedure: {why}\n"),
                }
            }
            // A definition, in the native convention: its global made, and
            // filled with its value, computed as an expression is.
            if let (Some(run), Top::Define { name, assigns, exp, .. }, Strategy::Cellular) = (self.native_runner, &top, self.strategy)
                && let Some((ty, init)) = definition_init(form, &self.checker, *name)
            {
                if *assigns {
                    self.keep_global(*name)?;
                }
                let name = self.checker.interner.name(*name).to_string();
                // Checked against the type the definition says, if it says
                // one: a `lambda`'s parameters may be typed only by it.
                let w = |s: &Syntax| fixpt_read::write_syntax(s, &self.checker.interner);
                let built_in = ty.is_none().then(|| built_in_load(init, &self.checker)).flatten();
                let init = match ty {
                    Some(t) => format!("(the {} {})", w(t), w(init)),
                    None => built_in.clone().unwrap_or_else(|| w(init)),
                };
                // A module file built in, as its text: seen as built in.
                if built_in.is_some() {
                    self.check_built_in(true)?;
                }
                let lambda = Self::names_its_word(&self.checker, *exp);
                let defined = self.native_define(&name, &format!("{form_text}\n"), &init, lambda, run);
                if built_in.is_some() {
                    self.check_built_in(false)?;
                }
                match defined? {
                    Ok(()) => return Ok(Outcome { top, code: String::new(), printed: String::new(), value: Ok(None) }),
                    Err(NativeRun::Ran(Err(e))) => return Ok(Outcome { top, code: String::new(), printed: String::new(), value: Err(e) }),
                    Err(NativeRun::Declined(why)) => note = format!("; not in the native convention yet, so `{name}` runs as cellular code: {why}\n"),
                    Err(NativeRun::Ran(Ok(_))) => unreachable!("a value is stored"),
                }
            }
            let (out, words) = match self.strategy {
                Strategy::Evaluate => (self.eval_form(&format!("{form_text}\n"))?, None),
                _ => self.compile_form_showing(&format!("{form_text}\n"), self.show_words)?,
            };
            // A form is compiled with every definition before it, so only
            // the words not shown before are this form's.
            let code = match words {
                Some(w) => w
                    .split_inclusive('\n')
                    .fold(Vec::<String>::new(), |mut blocks, line| {
                        match blocks.last_mut() {
                            Some(b) if !line.starts_with("word ") => b.push_str(line),
                            _ => blocks.push(line.to_string()),
                        }
                        blocks
                    })
                    .into_iter()
                    .filter(|b| self.words_shown.insert(b.clone()))
                    .collect::<String>()
                    .trim_matches('\n')
                    .to_string(),
                None => code,
            };
            let value = match out.strip_prefix("!! ") {
                Some(e) => Err(e.to_string()),
                None if matches!(top, Top::Exp(_)) => Ok(Some(out)),
                None => Ok(None),
            };
            // In the native convention, a definition run so has its
            // procedures compiled after, as it made them: each global that
            // holds a cellular closure then holds a native one.
            let names = match &top {
                Top::Define { name, .. } => vec![*name],
                Top::DefineRec { bindings, .. } => bindings.iter().map(|b| b.0).collect(),
                _ => Vec::new(),
            };
            if let (Some(compile), Ok(_), false) = (self.native_compiler, &value, names.is_empty()) {
                let (mut why, mut compiled) = (Vec::new(), false);
                for n in names {
                    match self.compile_global_natively(n, compile)? {
                        Ok(c) => compiled |= c,
                        Err(w) => why.push(format!("`{}` runs as cellular code: {w}", self.checker.interner.name(n))),
                    }
                }
                // Why its procedures stay cellular code, if they do: why they
                // were not compiled after; else why the definition ran so,
                // unless its procedure was compiled after (a module's
                // members, which nothing compiles after, stay so).
                if !why.is_empty() {
                    note = format!("; not in the native convention yet, so {}\n", why.join("; "));
                } else if compiled {
                    note.clear();
                }
            }
            return Ok(Outcome { top, code, printed: note, value });
        }
        if code.is_empty() {
            return Ok(Outcome { top, code, printed: String::new(), value: Ok(None) });
        }
        let is_define = matches!(top, Top::Define { .. } | Top::DefineRec { .. });
        let (printed, value) = self.scheme.scope(|s| {
            // The lowered Scheme's own compiling, quick, is counted as run.
            let start = std::time::Instant::now();
            s.bare_failures = true;
            let (printed, result) = s.eval_capturing("<fx26>", &code);
            s.bare_failures = false;
            s.runtime_unrooted().run_nanos += start.elapsed().as_nanos() as u64;
            let value = match result {
                Ok(_) if is_define => Ok(None),
                Ok(v) => Ok(Some(s.write(v))),
                Err(fixpt_scheme::SessionError::Raised(m)) => Err(lowered_failure(m)),
                Err(e) => Err(e.to_string()),
            };
            (printed, value)
        });
        Ok(Outcome { top, code, printed, value })
    }

    /// Whether a load reads a fresh `.fasl` (`fasls`): only compiled code
    /// is kept in one, so not where the lowering or the evaluator runs.
    fn reads_fasls(&self) -> bool {
        self.fasls && self.strategy == Strategy::Cellular
    }

    /// The hidden global `name` of a load read from `.fasl` file `fasl`
    /// defined, as `form` (`(define %shared:key (%loaded …))`) says: checked
    /// by the checker written in FX-26 as the next form, as the Rust
    /// checker checked it, its global made by the compiler written in
    /// FX-26, and given the value kept, linked to this session (`crate::fasl`):
    /// each global its code names, this session's of that name (as the
    /// compiler would find it, compiling the file now); each file the file
    /// loads, its load here. Nothing of the file is compiled or run.
    fn fasl_define(&mut self, name: Sym, form: &Syntax, fasl: &std::path::Path) -> R<Result<Option<String>, String>> {
        self.own_pieces()?;
        let standard = self.next_standard()?;
        let text = format!("{}\n", fixpt_read::write_syntax(form, &self.checker.interner));
        self.released(|s| s.fasl_define_in(standard, name, &text, fasl))
    }

    fn fasl_define_in(&mut self, standard: Option<fixpt_scheme::Handle>, name: Sym, text: &str, fasl: &std::path::Path) -> R<Result<Option<String>, String>> {
        let shown = self.checker.interner.name(name).to_string();
        if let Err(why) = crate::syn::check_only(&mut self.scheme, standard, FileId(0), text)? {
            return Err(FxError::at(Span::new(FileId(0), 0, 0), format!("the checkers disagree: the Rust checker takes `{shown}`'s definition, and the one written in FX-26 refuses it: {why}")));
        }
        self.own_begun = true;
        let fail = |e: String| FxError::at(Span::new(FileId(0), 0, 0), format!("`{}`: {e}", fasl.display()));
        let bytes = fixpt_heap::Mapped::open(fasl).map_err(|e| fail(e.to_string()))?;
        let (_, image) = crate::fasl::Header::read(&bytes).map_err(fail)?;
        let (from, value, links, natives) = crate::fasl::read_image(image).map_err(fail)?;
        let deps: Vec<Sym> = self.checker.shared_files.get(&name).map(|f| f.deps.iter().map(|d| d.2).collect()).unwrap_or_default();
        // What each link is here, held while the value is copied in; the
        // native adapter's, this heap's, found as it is copied.
        let mut found = Vec::new();
        let mut adapters = Vec::new();
        for (p, link) in links {
            let (global, value) = match link {
                crate::fasl::Link::Adapter => {
                    adapters.push(p);
                    continue;
                }
                crate::fasl::Link::Global(n) => (n, false),
                crate::fasl::Link::DepCell(i) | crate::fasl::Link::DepValue(i) => {
                    let Some(d) = deps.get(i) else { return Ok(Err(fail(format!("it names its load {i}, which it has not")).message)) };
                    (self.checker.interner.name(*d).to_string(), matches!(link, crate::fasl::Link::DepValue(_)))
                }
            };
            let Some(cell) = self.global_cell(&global)? else { return Ok(Err(fail(format!("it names `{global}`, which is not defined here")).message)) };
            let h = if value { self.scheme.make(|m| { let c = m.get(cell); m.heap().bloblet_slot(c, 2) }) } else { cell };
            found.push((p, h));
        }
        let stamp = self.checker.shared_files.get(&name).map_or(0, |f| stamp_fixnum(f.stamp));
        let sym = self.scheme.make(|m| m.heap().intern(&shown));
        let cell = self.scheme.call_global(&format!("{READER_PREFIX}compile-new-global"), &[sym]).map_err(|e| fail(e.to_string()))?;
        // Its native code as it was kept: nothing compiled here. Of cellular
        // words alone, the closures that were native compiled natively, as
        // they are made when the file is (`crate::fasl::native_procedures`).
        let adapter = self.native_keeping.map(|k| k.adapter_code);
        let compile = self.native_compiler.filter(|_| self.native_convention);
        let mut why = None;
        self.scheme.make(|m| {
            let mut given: std::collections::HashMap<u64, fixpt_heap::Value> = found.iter().map(|(p, h)| (p.raw(), m.get(*h))).collect();
            let g = m.get(cell);
            let heap = m.heap();
            if !adapters.is_empty() {
                match adapter.map(|a| a(heap)) {
                    Some(Ok(a)) => given.extend(adapters.iter().map(|p| (p.raw(), a))),
                    _ => {
                        why = Some("it holds native code's adapter, and this session makes none");
                        return fixpt_heap::Value::FALSE;
                    }
                }
            }
            let (copy, made) = heap.copy_graph_with(&from, value, |_| false, &given);
            let copy = match compile {
                Some(c) if !natives.is_empty() => crate::fasl::native_procedures(heap, copy, c, &natives.iter().filter_map(|n| made.get(&n.raw()).map(|v| v.raw())).collect()),
                _ => copy,
            };
            heap.set_bloblet_slot(g, 2, copy);
            // Its definition's stamp, as its load from source leaves it
            // (`definition_stamps`), which the guards test.
            heap.set_bloblet_slot(g, fixpt_heap::layout::cellular::GLOBAL_WRITES, fixpt_heap::Value::fixnum(stamp));
            fixpt_heap::Value::FALSE
        });
        if let Some(why) = why {
            return Ok(Err(fail(why.into()).message));
        }
        Ok(Ok(None))
    }

    /// Global `name`'s cell, the newest, as the compiler written in FX-26
    /// finds it (`compile-global-cell`); none if it has none.
    fn global_cell(&mut self, name: &str) -> R<Option<fixpt_scheme::Handle>> {
        let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
        let sym = self.scheme.make(|m| m.heap().intern(name));
        let cells = self.scheme.call_global(&format!("{READER_PREFIX}compile-global-cell"), &[sym]).map_err(fail)?;
        let mut found = false;
        let g = self.scheme.make(|m| {
            let cells = m.get(cells);
            found = cells.is_pair();
            if found { m.heap().car(cells) } else { fixpt_heap::Value::FALSE }
        });
        Ok(found.then_some(g))
    }

    /// The file at `path` (from the program's directory, as a load's)
    /// compiled to a `.fasl` beside it (`docs/research/fasl.md`): as a
    /// program's file if `program`; else as a module file, or, if it is none
    /// (its making is not pure, say), a program's. `fixpt compile-file`, the
    /// REPL's `,compile-file` and a program's `(compile-file "path")`.
    pub fn compile_file(&mut self, path: &str, program: bool) -> Result<std::path::PathBuf, String> {
        if program {
            return self.compile_program_file(path);
        }
        self.compile_module_file(path).or_else(|module| self.compile_program_file(path).map_err(|p| format!("{module}\n  and as a program's file: {p}")))
    }

    /// The module file at `path` (from the program's directory, as a
    /// load's) compiled to a `.fasl` beside it (`docs/research/fasl.md`):
    /// loaded, as `(load-module "path")` loads it, or `(load-input "path")`
    /// a file of one expression; then the type its load was checked at,
    /// the files it loads, and its value kept (`crate::fasl::image`). The
    /// `.fasl` made, or why not.
    pub fn compile_module_file(&mut self, path: &str) -> Result<std::path::PathBuf, String> {
        if self.strategy != Strategy::Cellular {
            return Err("only compiled code is kept in a `.fasl`: not on rs-scheme-vm or fx-ast-eval".into());
        }
        let at = match &self.checker.base_dir {
            Some(d) if std::path::Path::new(path).is_relative() => d.join(path),
            _ => std::path::PathBuf::from(path),
        };
        if crate::built_in_module(path).is_some() {
            return Err(format!("`{path}` is built in"));
        }
        let text = std::fs::read_to_string(&at).map_err(|e| format!("cannot read `{path}`: {e}"))?;
        // A file of one expression, not an item, is a `load-input`'s.
        let mut interner = fixpt_read::Interner::new();
        let forms = fixpt_read::Reader::new(&text, FileId(0), fixpt_read::SyntaxProfile::FX26, &mut interner).read_all().map_err(|e| format!("in `{path}`: {}", e.message))?;
        let one_exp = matches!(&forms[..], [one] if !crate::parse::is_item_form(one, &interner));
        let loader = if one_exp { "load-input" } else { "load-module" };
        let load = format!("({loader} {})", crate::fasl::string_literal(path));
        let form = self.checker.read_in(FileId(0), &load).map_err(|e| e.message)?;
        let out = self.run(&form[0]).map_err(|e| e.message)?;
        out.value?;
        self.write_module_fasl(path, &at, &text, one_exp, &crate::fasl::path_for(&at))
    }

    /// The `.fasl` of the module file at `at` (`path` as written, its text
    /// `text`, of one expression if `one_exp`), just loaded, written to
    /// `fasl` (`compile_module_file`): the `.fasl` made, or why not.
    fn write_module_fasl(&mut self, path: &str, at: &std::path::Path, text: &str, one_exp: bool, fasl: &std::path::Path) -> Result<std::path::PathBuf, String> {
        let input = one_exp || crate::parse::takes_modules_at(at, path);
        let key = format!("{}{}", if input { "input:" } else { "" }, at.display());
        let name = *self.checker.shared_loads.get(&key).ok_or_else(|| format!("`{path}` was not loaded"))?;
        let file = self.checker.shared_files.get(&name).cloned().ok_or_else(|| format!("`{path}` was not loaded"))?;
        // A maker's: its parameters as its source wrote them; else its type.
        // Either named by the standard type abbreviations it uses, as the
        // file sees them.
        self.checker.fasl_aliases_begin(self.checker.fasl_standard_aliases());
        let made = match self.checker.read_in(FileId(0), text) {
            Ok(forms) if input => {
                let maker = if one_exp { forms.first().cloned() } else { self.checker.modules_made(&forms) };
                maker.and_then(|m| self.checker.fasl_made(name, &m)).unwrap_or_default()
            }
            _ => String::new(),
        };
        let ty = match made.is_empty() {
            true => self.checker.fasl_type(name).map_err(|e| format!("`{path}`'s type cannot be kept: {e}")),
            false => Ok(String::new()),
        };
        let used = self.checker.fasl_aliases_end();
        let ty = ty?;
        let aliases = self.checker.fasl_alias_closure(used, &self.checker.fasl_standard_aliases());
        let mut deps = Vec::new();
        let mut dep_values = Vec::new();
        for (written, input, d) in &file.deps {
            let stamp = self.checker.shared_files.get(d).map_or(0, |f| f.stamp);
            deps.push(crate::fasl::Dep { path: written.clone(), input: *input, stamp });
            dep_values.push(self.checker.interner.name(*d).to_string());
        }
        let header = crate::fasl::Header {
            build: crate::fasl::build(),
            arch: std::env::consts::ARCH.to_string(),
            native: self.native_convention,
            cellular: self.fasl_cellular,
            kind: if input { crate::fasl::Kind::Input } else { crate::fasl::Kind::Module },
            source: file.source,
            stamp: file.stamp,
            deps,
            ty,
            made,
            defs: Vec::new(),
            aliases,
        };
        let image = self.released(|s| s.fasl_image(&name, &dep_values)).map_err(|e| format!("`{path}`'s value cannot be kept: {e}"))?;
        let tmp = fasl.with_extension(format!("fasl-tmp{}", std::process::id()));
        std::fs::write(&tmp, header.file(&image)).map_err(|e| format!("cannot write `{}`: {e}", tmp.display()))?;
        std::fs::rename(&tmp, fasl).map_err(|e| format!("cannot write `{}`: {e}", fasl.display()))?;
        Ok(fasl.to_path_buf())
    }

    /// Each module file built in (`fx26:…`) that a form just loaded from its
    /// source, not a `.fasl`, given one in the cache directory
    /// (`fasl::path_for_load`), which later runs read instead: a built-in
    /// has no directory for `fixpt compile-file` to write one in. Once a
    /// session each; any failure only means none.
    fn cache_built_ins(&mut self) {
        if !self.reads_fasls() {
            return;
        }
        let loaded: Vec<(String, std::path::PathBuf)> = self
            .checker
            .shared_files
            .values()
            .filter(|f| f.fasl.is_none() && self.shared_made.contains(&f.key))
            .map(|f| (f.key.strip_prefix("input:").unwrap_or(&f.key).to_string(), f.path.clone()))
            .filter(|(p, _)| crate::built_in_module(p).is_some() && !self.built_ins_cached.contains(p))
            .collect();
        for (path, at) in loaded {
            self.built_ins_cached.insert(path.clone());
            let (Some(text), Some(fasl)) = (crate::built_in_module(&path), crate::fasl::path_for_load(&at, &path, self.native_convention)) else { continue };
            if fasl.parent().is_some_and(|d| std::fs::create_dir_all(d).is_ok()) {
                let _ = self.write_module_fasl(&path, &at, text, false, &fasl);
            }
        }
    }

    /// Whether `effect` reads globals alone, each one whose definition ran
    /// (`program_ran`).
    fn only_reads_ran(&self, effect: &crate::ast::Effect) -> bool {
        use crate::ast::{Atom, Region};
        effect.0.iter().all(|a| matches!(a, Atom::Read(Region::Global(g)) if self.program_ran.contains(g)))
    }

    /// Definition `form`, checked by the checker written in FX-26 as the
    /// next form and its globals made, but not run: a program's file being
    /// compiled (`program_record`).
    fn declare_only(&mut self, form: &Syntax) -> R<()> {
        self.own_pieces()?;
        let standard = self.next_standard()?;
        let text = format!("{}\n", fixpt_read::write_syntax(form, &self.checker.interner));
        let names = self.checker.defined_names(form);
        self.released(|s| {
            let fail = |e: fixpt_scheme::SessionError| FxError::at(form.span, e.to_string());
            if let Err(why) = crate::syn::check_only(&mut s.scheme, standard, FileId(0), &text)? {
                return Err(FxError::at(form.span, format!("the checkers disagree: the Rust checker takes this definition, and the one written in FX-26 refuses it: {why}")));
            }
            s.own_begun = true;
            for n in names {
                let shown = s.checker.interner.name(n).to_string();
                let sym = s.scheme.make(|m| m.heap().intern(&shown));
                s.scheme.call_global(&format!("{READER_PREFIX}compile-new-global"), &[sym]).map_err(fail)?;
            }
            Ok(())
        })
    }

    /// Program file `path`'s `.fasl`, if it is fresh for `forms`, the file's:
    /// made from this text, by this executable, for this architecture and
    /// convention; none of the names it defines from it defined here yet;
    /// and each global its definitions' code uses that the file does not
    /// define, here at the type it had (`fasl_program_type`), so that the
    /// code is right for it. Whole or not at all: its procedures were
    /// compiled together, a call of one maybe made in line in another's
    /// code. A stale one said (`fasl_notes`).
    fn program_fasl(&mut self, path: &std::path::Path, forms: &[Syntax]) -> Option<ProgramFasl> {
        let fasl = crate::fasl::path_for(path);
        let bytes = fixpt_heap::Mapped::open(&fasl).ok()?;
        let stale = |s: &mut Self, why: &str| {
            s.checker.fasl_notes.push(format!("`{}` is stale ({why}): `{}` is run from its source", fasl.display(), path.display()));
            None
        };
        let (header, image) = match crate::fasl::Header::read(&bytes) {
            Ok(h) => h,
            Err(e) => return stale(self, &e),
        };
        if header.kind != crate::fasl::Kind::Program {
            // A module file's, for its loads: nothing to say here.
            return None;
        }
        let text = std::fs::read_to_string(path).ok()?;
        let why = if header.build != crate::fasl::build() {
            Some("another fixpt made it".to_string())
        } else if header.arch != std::env::consts::ARCH {
            Some(format!("it is for {}", header.arch))
        } else if header.native != self.native_convention {
            Some(if header.native { "it is for the native convention" } else { "it is for the cellular convention" }.to_string())
        } else if header.source != crate::fasl::digest(&text) {
            Some("its source changed".to_string())
        } else {
            None
        };
        if let Some(why) = why {
            return stale(self, &why);
        }
        // Each abbreviation it names what it was; one the file defines that
        // is not yet (it selects from a module a form loads, say), checked
        // when a definition that names it is declared (`run_program_def`).
        let own: Vec<Sym> = self.checker.type_abbreviations(forms).into_iter().map(|(n, _)| n).collect();
        let mut later = std::collections::HashMap::new();
        let names = self.checker.fasl_alias_names(&header.aliases);
        for (n, t) in &header.aliases {
            let a = self.checker.interner.intern(n);
            if self.checker.fasl_alias_expansion(a, &names).map(|(t, _)| t).as_deref() == Some(t.as_str()) {
                continue;
            }
            if !own.contains(&a) {
                return stale(self, &format!("the type `{n}` is not what it was"));
            }
            later.insert(n.clone(), t.clone());
        }
        let defined: std::collections::HashSet<String> = forms.iter().flat_map(|f| self.checker.defined_names(f)).map(|n| self.checker.interner.name(n).to_string()).collect();
        self.checker.fasl_aliases_begin(self.checker.fasl_allowed_aliases(forms));
        let stale_use = self.stale_use(&header.defs, &defined);
        self.checker.fasl_aliases_end();
        if let Some(why) = stale_use {
            return stale(self, &why);
        }
        for d in &header.defs {
            let n = self.checker.interner.intern(&d.name);
            if d.form >= forms.len() || !self.checker.defined_names(&forms[d.form]).contains(&n) {
                return stale(self, &format!("its definition of `{}` is not its form's", d.name));
            }
            if self.checker.global_type(n).is_some() {
                return stale(self, &format!("`{}` is defined here already", d.name));
            }
        }
        let (heap, value, links, natives) = match crate::fasl::read_image(image) {
            Ok(r) => r,
            Err(e) => return stale(self, &e),
        };
        let mut values = Vec::new();
        let mut l = value;
        while l.is_pair() {
            values.push(heap.car(l));
            l = heap.cdr(l);
        }
        if values.len() != header.defs.len() {
            return stale(self, "its image is not its definitions'");
        }
        if std::env::var_os("FIXPT_FASL_SAY").is_some() {
            self.checker.fasl_notes.push(format!("`{}` is read from `{}`", path.display(), fasl.display()));
        }
        let mut defs: std::collections::HashMap<usize, Vec<(crate::fasl::Def, usize)>> = std::collections::HashMap::new();
        for (i, d) in header.defs.into_iter().enumerate() {
            defs.entry(d.form).or_default().push((d, i));
        }
        let links = links.into_iter().map(|(p, l)| (p.raw(), l)).collect();
        Some(ProgramFasl { defs, heap, values, links, natives, later: std::cell::RefCell::new(later), alias_names: names })
    }

    /// Why `defs`' code is not right here, if it is not: a global it uses,
    /// not one the file defines (`defined`), not here, or not at the type
    /// it had (printed as `fasl_program_type` prints it).
    fn stale_use(&mut self, defs: &[crate::fasl::Def], defined: &std::collections::HashSet<String>) -> Option<String> {
        for d in defs {
            for (u, t) in &d.uses {
                if defined.contains(u) {
                    continue;
                }
                let un = self.checker.interner.intern(u);
                let now = self.checker.global_type(un).map(|g| self.checker.fasl_program_type(g));
                if now.as_ref().is_none_or(|n| n.as_deref() != Ok(t.as_str())) {
                    return Some(format!("`{}` uses `{u}`, which is not here at the type it was", d.name));
                }
            }
        }
        None
    }

    /// `form`, a program's definition of a procedure, read from its `.fasl`
    /// (`program_fasl`): checked, by both checkers, as `(define name T (the
    /// T %fasl-value))`, then made what `form` would have made of it for a
    /// redefinition (`Checker::fasl_defined`); its global given the value
    /// kept, linked to the globals here by name, its procedures compiled
    /// natively in the native convention.
    fn run_program_def(&mut self, form: &Syntax, group: &[(crate::fasl::Def, usize)], p: &ProgramFasl) -> R<Outcome> {
        let fail = |m: String| FxError::at(form.span, m);
        // The file's own abbreviations it names that were not yet when the
        // `.fasl` was read: what they were, or the form runs from its source.
        for t in group.iter().flat_map(|(d, _)| &d.types) {
            let Some(was) = p.later.borrow().get(t).cloned() else { continue };
            let a = self.checker.interner.intern(t);
            if self.checker.fasl_alias_expansion(a, &p.alias_names).map(|(t, _)| t).as_deref() != Some(was.as_str()) {
                self.checker.fasl_notes.push(format!("the type `{t}` is not what it was: `{}` is run from its source", group[0].0.name));
                return self.run_each(form).and_then(|mut v| v.pop().ok_or_else(|| fail("a definition".into())));
            }
            p.later.borrow_mut().remove(t);
        }
        let text = match &group[..] {
            [(d, _)] if !d.rec => format!("(define {} {} {})", d.name, d.ty, d.init),
            _ => format!("(define-rec {})", group.iter().map(|(d, _)| format!("({} {} {})", d.name, d.ty, d.init)).collect::<Vec<_>>().join(" ")),
        };
        let decl = self.checker.read_in(form.span.file, &text)?.pop().ok_or_else(|| fail("a definition".into()))?;
        let done = self.checker.top_defining(&decl)?;
        for (d, _) in group {
            let name = self.checker.interner.intern(&d.name);
            let uses = d.uses.iter().map(|(u, _)| self.checker.interner.intern(u)).collect();
            self.checker.fasl_defined(name, std::rc::Rc::new(form.clone()), uses);
        }
        let top = done.run.into_iter().next().map(|(t, _)| t).ok_or_else(|| fail("a definition".into()))?;
        // Each its definition's stamp, as its run from source leaves it.
        let stamps: Vec<i64> = {
            let all = self.definition_stamps(&top, form);
            group.iter().map(|(d, _)| { let n = self.checker.interner.intern(&d.name); all.iter().find(|(m, _)| *m == n).map_or(0, |(_, s)| *s) }).collect()
        };
        self.own_pieces()?;
        let standard = self.next_standard()?;
        let value = self.released(|s| -> R<String> {
            let sfail = |e: fixpt_scheme::SessionError| FxError::at(form.span, e.to_string());
            if let Err(why) = crate::syn::check_only(&mut s.scheme, standard, FileId(0), &format!("{text}\n"))? {
                return Err(fail(format!("the checkers disagree: the Rust checker takes `{}`'s definition, and the one written in FX-26 refuses it: {why}", group[0].0.name)));
            }
            s.own_begun = true;
            let mut cells = Vec::new();
            for (d, _) in group {
                let sym = s.scheme.make(|m| m.heap().intern(&d.name));
                cells.push(s.scheme.call_global(&format!("{READER_PREFIX}compile-new-global"), &[sym]).map_err(sfail)?);
            }
            // What their code links to, found here: the globals before them,
            // and themselves.
            let mut found = Vec::new();
            let mut adapters = Vec::new();
            let mut todo: Vec<fixpt_heap::Value> = group.iter().map(|(_, at)| p.values[*at]).collect();
            let mut seen = std::collections::HashSet::new();
            while let Some(v) = todo.pop() {
                if !v.is_ref() || v.is_suffix_ref() || !seen.insert(v.raw()) {
                    continue;
                }
                if let Some(link) = p.links.get(&v.raw()) {
                    if *link == crate::fasl::Link::Adapter {
                        adapters.push(v);
                        continue;
                    }
                    let crate::fasl::Link::Global(n) = link else { return Err(fail("it links to a file's load".into())) };
                    let c = s.global_cell(n)?.ok_or_else(|| fail(format!("it names `{n}`, which is not defined here")))?;
                    found.push((v, c));
                    continue;
                }
                if v.is_pair() {
                    todo.extend([p.heap.car(v), p.heap.cdr(v)]);
                } else if p.heap.obj_type(v) != Some(fixpt_heap::ObjType::Symbol) {
                    let trailer = p.heap.bloblet_has_trailer(v) as usize;
                    todo.extend(((1 + trailer)..=p.heap.bloblet_head(v).fields).map(|k| p.heap.bloblet_slot(v, k)));
                }
            }
            // Its native code as it was kept: nothing compiled here; of
            // cellular words alone, compiled natively (`native_procedures`).
            let adapter = s.native_keeping.map(|k| k.adapter_code);
            let compile = s.native_compiler.filter(|_| s.native_convention);
            let mut no_adapter = false;
            s.scheme.make(|m| {
                let mut given: std::collections::HashMap<u64, fixpt_heap::Value> = found.iter().map(|(v, h)| (v.raw(), m.get(*h))).collect();
                let gs: Vec<fixpt_heap::Value> = cells.iter().map(|c| m.get(*c)).collect();
                let heap = m.heap();
                if !adapters.is_empty() {
                    match adapter.map(|a| a(heap)) {
                        Some(Ok(a)) => given.extend(adapters.iter().map(|v| (v.raw(), a))),
                        _ => {
                            no_adapter = true;
                            return fixpt_heap::Value::FALSE;
                        }
                    }
                }
                for (((_, at), g), stamp) in group.iter().zip(gs).zip(&stamps) {
                    let (copy, made) = heap.copy_graph_with(&p.heap, p.values[*at], |_| false, &given);
                    let copy = match compile {
                        Some(c) if !p.natives.is_empty() => crate::fasl::native_procedures(heap, copy, c, &p.natives.iter().filter_map(|n| made.get(&n.raw()).map(|v| v.raw())).collect()),
                        _ => copy,
                    };
                    // What the group's definitions share, copied once.
                    given.extend(made);
                    heap.set_bloblet_slot(g, 2, copy);
                    heap.set_bloblet_slot(g, fixpt_heap::layout::cellular::GLOBAL_WRITES, fixpt_heap::Value::fixnum(*stamp));
                }
                fixpt_heap::Value::FALSE
            });
            if no_adapter {
                return Err(fail("it holds native code's adapter, and this session makes none".into()));
            }
            // What the definition said where it was made, said again.
            Ok(group.iter().flat_map(|(d, _)| d.said.iter()).map(|l| format!("{l}\n")).collect())
        });
        let printed = value?;
        Ok(Outcome { top, code: String::new(), printed, value: Ok(None) })
    }

    /// Program file `path` (from the program's directory) compiled to a
    /// `.fasl` beside it: its forms checked in order, as `,load` checks them,
    /// in this session, each definition given its global, but only those of
    /// procedures (and of types, and loads) run, so that compiling runs
    /// nothing of what the program does; then each procedure's definition
    /// kept, with its type and those of the globals its code uses, and its
    /// value. What its code assumes of a global, its guards test by the
    /// global's stamp (`definition_stamps`), the same where it is loaded
    /// only if the global's definition is.
    pub fn compile_program_file(&mut self, path: &str) -> Result<std::path::PathBuf, String> {
        if self.strategy != Strategy::Cellular {
            return Err("only compiled code is kept in a `.fasl`: not on rs-scheme-vm or fx-ast-eval".into());
        }
        let at = match &self.checker.base_dir {
            Some(d) if std::path::Path::new(path).is_relative() => d.join(path),
            _ => std::path::PathBuf::from(path),
        };
        let text = std::fs::read_to_string(&at).map_err(|e| format!("cannot read `{path}`: {e}"))?;
        let forms = self.checker.read_in(FileId(0), &text).map_err(|e| format!("in `{path}`: {}", e.message))?;
        let outer = std::mem::replace(&mut self.checker.base_dir, at.parent().map(|d| d.to_path_buf()));
        self.program_ran = self.checker.value_names().into_iter().filter(|n| self.checker.global_type(*n).is_some()).collect();
        self.program_record = Some(Vec::new());
        let ran = self.run_forms(&forms);
        let record = self.program_record.take().unwrap_or_default();
        self.checker.base_dir = outer;
        for o in ran.map_err(|e| format!("in `{path}`: {}", e.message))? {
            o.map_err(|e| format!("in `{path}`: {}", e.message))?;
        }
        // Each definition of a procedure the file makes once, of a name it
        // defines once, in a form that loads nothing.
        let mut counts: std::collections::HashMap<Sym, usize> = std::collections::HashMap::new();
        for f in &forms {
            for n in self.checker.defined_names(f) {
                *counts.entry(n).or_default() += 1;
            }
        }
        let loads = |f: &Syntax, c: &Checker| {
            let written = fixpt_read::write_syntax(f, &c.interner);
            ["load-module", "load-input", "compile-file"].iter().any(|w| written.contains(w))
        };
        // A form after a top-level `include` sees what it gives, and the
        // type abbreviations after it are not declared ahead: the form's.
        let included = forms.iter().position(|f| self.checker.include_forms(f).is_ok_and(|i| i.is_some())).unwrap_or(forms.len());
        let mut defs = Vec::new();
        let mut names = Vec::new();
        self.checker.fasl_aliases_begin(self.checker.fasl_allowed_aliases(&forms));
        let mut kept_names: std::collections::HashSet<Sym> = std::collections::HashSet::new();
        for (i, top, printed) in &record {
            let said: Vec<String> = printed.lines().map(str::to_string).collect();
            let (bindings, rec) = match top {
                Top::Define { name, ty, exp, .. } => (vec![(*name, *ty, *exp)], false),
                Top::DefineRec { bindings, .. } => (bindings.clone(), true),
                _ => continue,
            };
            // A value that is no procedure is kept if its making read only
            // what is kept, so that it is what making it makes where the
            // program is loaded; and it ran here.
            let (value_ok, reads) = match top {
                Top::Define { name, effect, .. } => {
                    use crate::ast::{Atom, Region};
                    let reads: Vec<Sym> = effect.0.iter().filter_map(|a| match a {
                        Atom::Read(Region::Global(g)) => Some(*g),
                        _ => None,
                    }).collect();
                    (self.program_ran.contains(name) && reads.len() == effect.0.len() && reads.iter().all(|g| kept_names.contains(g)), reads)
                }
                _ => (false, Vec::new()),
            };
            // Of procedures, each defined once, in a form that loads nothing,
            // before an `include`, and proves no lemma (which a declaration
            // would not); a `define` written so, or a `define-rec`.
            let written = definition_init(&forms[*i], &self.checker, bindings[0].0);
            let proves = written.and_then(|(t, _)| t?.as_proper_list()?.first()?.as_symbol()).is_some_and(|h| self.checker.interner.name(h) == "proves");
            if (!rec && written.is_none()) || proves || *i > included || loads(&forms[*i], &self.checker) {
                continue;
            }
            let Some(kept) = bindings.iter().map(|b| self.kept_binding(*b, &counts, rec, value_ok.then_some(&reads[..]))).collect::<Option<Vec<_>>>() else { continue };
            // Its declaration, which must check, as the form did, at the
            // types it has.
            let decl = match rec {
                false => format!("(define {} {} {})", kept[0].0, kept[0].1, kept[0].2),
                true => format!("(define-rec {})", kept.iter().map(|(n, t, init, _)| format!("({n} {t} {init})")).collect::<Vec<_>>().join(" ")),
            };
            let checks = match self.checker.read_in(FileId(0), &decl).ok().and_then(|mut v| v.pop()) {
                Some(d) => self.checker.try_defining(&d).is_ok_and(|done| {
                    let tys: Vec<crate::ast::TyId> = match done.run.first() {
                        Some((Top::Define { ty, .. }, _)) => vec![*ty],
                        Some((Top::DefineRec { bindings, .. }, _)) => bindings.iter().map(|b| b.1).collect(),
                        _ => Vec::new(),
                    };
                    tys.len() == kept.len() && tys.iter().zip(&kept).all(|(t, k)| self.checker.fasl_program_type(*t).as_deref() == Ok(k.1.as_str()))
                }),
                None => false,
            };
            if !checks {
                continue;
            }
            kept_names.extend(bindings.iter().map(|b| b.0));
            for (n, (name, ty, init, uses)) in kept.into_iter().enumerate() {
                let said = if n == 0 { said.clone() } else { Vec::new() };
                defs.push(crate::fasl::Def { form: *i, rec, name: name.clone(), ty, init, uses, said, types: Vec::new() });
                names.push(name);
            }
        }
        // The abbreviations named, each with what it is, the file's own
        // (declared ahead) as the standard ones, to compare where it is read.
        // Each definition notes those its type names, and those they name.
        let used = self.checker.fasl_aliases_end();
        let aliases = self.checker.fasl_alias_closure(used, &self.checker.fasl_allowed_aliases(&forms));
        let kept: std::collections::HashMap<&str, &str> = aliases.iter().map(|(n, t)| (n.as_str(), t.as_str())).collect();
        for d in &mut defs {
            let mut types: Vec<String> = crate::fasl::symbols_in(&d.ty).into_iter().filter(|w| kept.contains_key(w.as_str())).collect();
            let mut i = 0;
            while i < types.len() {
                for w in crate::fasl::symbols_in(kept[types[i].as_str()]) {
                    if kept.contains_key(w.as_str()) && !types.contains(&w) {
                        types.push(w);
                    }
                }
                i += 1;
            }
            d.types = types;
        }
        let header = crate::fasl::Header {
            build: crate::fasl::build(),
            arch: std::env::consts::ARCH.to_string(),
            native: self.native_convention,
            cellular: self.fasl_cellular,
            kind: crate::fasl::Kind::Program,
            source: crate::fasl::digest(&text),
            stamp: 0,
            deps: Vec::new(),
            ty: String::new(),
            made: String::new(),
            defs,
            aliases,
        };
        let image = self.released(|s| s.program_image(&names)).map_err(|e| format!("`{path}`'s definitions cannot be kept: {e}"))?;
        let fasl = crate::fasl::path_for(&at);
        let tmp = fasl.with_extension(format!("fasl-tmp{}", std::process::id()));
        std::fs::write(&tmp, header.file(&image)).map_err(|e| format!("cannot write `{}`: {e}", tmp.display()))?;
        std::fs::rename(&tmp, &fasl).map_err(|e| format!("cannot write `{}`: {e}", fasl.display()))?;
        Ok(fasl)
    }

    /// What a program's `.fasl` keeps of binding `b` (name, type, value) of
    /// a definition, if it can (`compile_program_file`): its name, its type,
    /// the expression its declaration has the type by (a `define-rec`'s,
    /// `rec`, a `lambda`), and the globals its code uses with their types.
    /// None for a binding of no procedure (but a value made of what is kept
    /// alone, reading the globals `value` says), of a name the file defines more
    /// than once (`counts`), of a type that does not read back as itself,
    /// or that uses a load's hidden global, which the forms that load it
    /// make as they are checked.
    fn kept_binding(&mut self, b: (Sym, crate::ast::TyId, crate::ast::ExpId), counts: &std::collections::HashMap<Sym, usize>, rec: bool, value: Option<&[Sym]>) -> Option<(String, String, String, Vec<(String, String)>)> {
        let (name, tid, exp) = b;
        if counts.get(&name) != Some(&1) || !(value.is_some() || Self::names_its_word(&self.checker, exp)) {
            return None;
        }
        let ty = self.checker.fasl_program_type(tid).ok()?;
        if self.checker.fasl_reads_back(&ty).as_deref() != Some(ty.as_str()) {
            return None;
        }
        let used = self.checker.uses_of(name);
        if used.iter().any(|u| self.checker.interner.name(*u).starts_with("%shared:")) {
            return None;
        }
        let uses = used.into_iter().filter_map(|u| Some((self.checker.interner.name(u).to_string(), self.checker.fasl_program_type(self.checker.global_type(u)?).ok()?))).collect();
        // The type, its `poly`s and procedures taken apart: as printed, if
        // that shows them, else written out (an abbreviation of a `poly`,
        // say), which can be much longer.
        let shaped = |t: &str| t.starts_with("(poly ") || (rec && t.starts_with("(subr "));
        let text = match shaped(&ty) || (!rec && ty.starts_with('(')) {
            true => ty.clone(),
            false => {
                let kept = self.checker.print_aliases.borrow_mut().take();
                let expanded = self.checker.fasl_program_type(tid);
                *self.checker.print_aliases.borrow_mut() = kept;
                match expanded.ok()? {
                    e if shaped(&e) => e,
                    _ => ty.clone(),
                }
            }
        };
        let syn = self.checker.read_in(FileId(0), &text).ok()?.pop()?;
        let init = match rec {
            false => crate::fasl::fasl_value_at(&syn, &self.checker.interner),
            true => crate::fasl::fasl_lambda_at(&syn, &self.checker.interner)?,
        };
        // A value's making read globals, which its declaration reads too,
        // to have its effect; not under a `plambda`, which must be pure.
        let init = match value.filter(|_| !Self::names_its_word(&self.checker, exp)) {
            Some([]) | None => init,
            Some(_) if init.starts_with("(plambda") => return None,
            Some(reads) => format!("(begin {} {init})", reads.iter().map(|g| self.checker.interner.name(*g)).collect::<Vec<_>>().join(" ")),
        };
        Some((self.checker.interner.name(name).to_string(), ty, init, uses))
    }

    /// The values of globals `names`, in a list, as a `.fasl`'s image
    /// (`crate::fasl::image`).
    fn program_image(&mut self, names: &[String]) -> Result<Vec<u8>, String> {
        let mut cells = Vec::new();
        for n in names {
            cells.push(self.global_cell(n).map_err(|e| e.message)?.ok_or_else(|| format!("`{n}` has no global"))?);
        }
        let adapter = self.native_keeping.as_ref().map(|k| k.adapter_code);
        let mut r = Err(String::new());
        let cellular = self.fasl_cellular;
        self.scheme.make(|m| {
            let values: Vec<fixpt_heap::Value> = cells.iter().map(|c| { let c = m.get(*c); m.heap().bloblet_slot(c, 2) }).collect();
            let heap = m.heap();
            let mut list = fixpt_heap::Value::NULL;
            for v in values.iter().rev() {
                list = heap.cons(*v, list);
            }
            let adapter = adapter.and_then(|a| a(heap).ok());
            r = crate::fasl::image(heap, list, &[], adapter, cellular);
            fixpt_heap::Value::FALSE
        });
        r
    }

    /// The value of hidden global `name` as a `.fasl`'s image, each of
    /// `deps` (the hidden globals of the files its file loads) linked by its
    /// place (`crate::fasl::image`).
    fn fasl_image(&mut self, name: &Sym, deps: &[String]) -> Result<Vec<u8>, String> {
        let shown = self.checker.interner.name(*name).to_string();
        let cell = self.global_cell(&shown).map_err(|e| e.message)?.ok_or_else(|| format!("`{shown}` has no global"))?;
        let mut cells = Vec::new();
        for d in deps {
            cells.push(self.global_cell(d).map_err(|e| e.message)?.ok_or_else(|| format!("`{d}` has no global"))?);
        }
        let adapter = self.native_keeping.as_ref().map(|k| k.adapter_code);
        let mut r = Err(String::new());
        let cellular = self.fasl_cellular;
        self.scheme.make(|m| {
            let value = { let c = m.get(cell); m.heap().bloblet_slot(c, 2) };
            let deps: Vec<(String, fixpt_heap::Value)> = deps.iter().zip(&cells).map(|(d, c)| { let c = m.get(*c); (d.clone(), m.heap().bloblet_slot(c, 2)) }).collect();
            let heap = m.heap();
            let adapter = adapter.and_then(|a| a(heap).ok());
            r = crate::fasl::image(heap, value, &deps, adapter, cellular);
            fixpt_heap::Value::FALSE
        });
        r
    }

    /// Read `text` with the reader written in FX-26, loading it into this
    /// session the first time, rather than with the Rust reader. Reading a
    /// whole file is long work for it, so it reads with no step limit: it
    /// is licensed code, and a text ends.
    pub fn read_with_own_reader(&mut self, text: &str) -> R<Vec<Syntax>> {
        self.load_own_reader()?;
        self.scheme.engine.set_step_limit(None);
        let forms = crate::syn::read_with_fx26_reader(&mut self.scheme, &mut self.checker.interner, FileId(0), text);
        self.scheme.engine.set_step_limit(self.step_limit);
        self.checker.expand_forms(forms?)
    }

    /// Parse `text` with the parser written in FX-26 (and its reader),
    /// loading them the first time: each form's tree, as text.
    pub fn parse_with_own_parser(&mut self, text: &str) -> R<Vec<String>> {
        if !self.scheme.is_bound(&format!("{READER_PREFIX}parse-program")) {
            load_eager_reader(&mut self.scheme).map_err(crate::front_end_failure)?;
        }
        self.scheme.engine.set_step_limit(None);
        let r = crate::syn::parse_with_fx26_parser(&mut self.scheme, FileId(0), text);
        self.scheme.engine.set_step_limit(self.step_limit);
        r
    }

    /// Run `text` with the evaluator written in FX-26, reading and parsing
    /// it with the reader and the parser written in FX-26: its value as
    /// Scheme would write it, or `!! ` and its error.
    pub fn eval_with_own_evaluator(&mut self, text: &str) -> R<String> {
        self.shared_made.clear();
        self.processes_forgotten();
        self.own_pieces()?;
        let standard = self.standard26()?;
        // A whole program: the checker begins again.
        self.own_begun = false;
        self.scheme.engine.set_step_limit(None);
        let r = crate::syn::eval_with_fx26_evaluator(&mut self.scheme, standard, FileId(0), text);
        self.scheme.engine.set_step_limit(self.step_limit);
        r
    }

    /// `text`, one form or more, as the next of this session's program, by
    /// the evaluator written in FX-26: checked after the forms before, and
    /// run with the globals they made, once (`run-checked-more`); its
    /// positions past every text's before. As the compiler's forms are
    /// (`compile_form_showing`), where the evaluator once ran every
    /// definition before again with each form (`TODO.md` §96).
    fn eval_form(&mut self, text: &str) -> R<String> {
        self.own_pieces()?;
        let standard = self.next_standard()?;
        if standard.is_some() {
            self.eval_base = 0;
        }
        let base = self.eval_base;
        self.eval_base += text.chars().count() as i64 + 1;
        self.scheme.engine.set_step_limit(None);
        let r = crate::syn::eval_more_with_fx26_evaluator(&mut self.scheme, standard, FileId(0), text, base);
        self.scheme.engine.set_step_limit(self.step_limit);
        self.own_begun |= !matches!(&r, Ok(out) if out.starts_with("!! check:"));
        r
    }

    /// The prelude whole, for lowered code to call: what a session begun
    /// not lowering left out (`with_backend_preloaded_in`).
    pub fn whole_prelude(&mut self) {
        if std::mem::take(&mut self.prelude_data_pending) {
            self.scheme.eval_str("<prelude>", fixpt_scheme::PRELUDE_DATA).expect("the prelude must load");
        }
    }

    /// The initial environment as the FX-26 reader reads it, read once.
    fn standard26(&mut self) -> R<fixpt_scheme::Handle> {
        if let Some(h) = self.standard26 {
            return Ok(h);
        }
        // Outside any scope, so it lasts as the session does.
        let h = crate::syn::read_standard(&mut self.scheme)?;
        self.standard26 = Some(h);
        Ok(h)
    }

    /// Make the program's convention native, or cellular: what every
    /// subroutine type that names none has, the standard environment's
    /// included, in both checkers. Before any form is checked.
    pub fn set_native_convention(&mut self, on: bool) {
        let syscalls = self.checker.syscalls;
        self.native_convention = on;
        // A checker of that convention already, as one is made for it
        // (`with_backend_preloaded_in`), kept: nothing is checked yet.
        let conv = if on { crate::ast::Conv::Native } else { crate::ast::Conv::Cellular };
        if self.checker.conv_default != conv {
            self.checker = Checker::with_convention(conv);
        }
        self.checker.globals_effects = self.globals_effects;
        self.checker.defer_reruns = self.defer_reruns;
        self.checker.syscalls = syscalls;
    }

    /// Whether a redefinition that makes a new global leaves the
    /// definitions that use the name out of date, as they were, for
    /// [`rerun_outdated`](Self::rerun_outdated) to run again when asked,
    /// rather than running them again at once: in both checkers
    /// (`Checker::defer_reruns`). What the REPL does, so that a load does
    /// not run again what it is about to define again.
    pub fn set_defer_reruns(&mut self, on: bool) {
        self.defer_reruns = on;
        self.checker.defer_reruns = on;
    }

    /// The definitions out of date (`set_defer_reruns`), oldest first: the
    /// names each defines, and those it uses that were defined again since.
    pub fn outdated(&self) -> Vec<(Vec<String>, Vec<String>)> {
        let names = |ns: &[Sym]| ns.iter().map(|n| self.checker.interner.name(*n).to_string()).collect();
        self.checker.outdated().iter().map(|(ns, since, _)| (names(ns), names(since))).collect()
    }

    /// Each definition out of date run again, oldest first, as though
    /// written again, until none is left that has not been tried: one may
    /// leave others out of date in its turn. Each one's names, and what
    /// running it did; one that does not check stays out of date.
    pub fn rerun_outdated(&mut self) -> Vec<(Vec<String>, R<Outcome>)> {
        let mut tried: Vec<Vec<Sym>> = Vec::new();
        let mut outs = Vec::new();
        while let Some((ns, _, form)) = self.checker.outdated().into_iter().find(|(ns, _, _)| !tried.contains(ns)) {
            let out = self.run(&form);
            outs.push((ns.iter().map(|n| self.checker.interner.name(*n).to_string()).collect(), out));
            tried.push(ns);
        }
        outs
    }

    /// Whether naming a global reads it, `(read (globals g))`, in both
    /// checkers (`Checker::globals_effects`).
    pub fn set_globals_effects(&mut self, on: bool) {
        self.globals_effects = on;
        self.checker.globals_effects = on;
    }

    /// A checker with no program in it yet, set as this session's is.
    pub fn fresh_checker(&self) -> Checker {
        let mut c = Checker::with_convention(if self.native_convention { crate::ast::Conv::Native } else { crate::ast::Conv::Cellular });
        c.globals_effects = self.globals_effects;
        c.base_dir = self.checker.base_dir.clone();
        c.syscalls = self.checker.syscalls;
        c
    }

    /// The front end's entry points the Rust side calls by name
    /// (`READER_PREFIX`), each rebound by [`Self::front_end_as_register_code`].
    pub const FRONT_ENTRIES: [&'static str; 36] = [
        "read-text-at", "check-program", "check-more", "checked-tops", "checked-extracts", "checked-effects", "check-conv-native!", "checked-withs!", "checked-reshapes!",
        "check-globals-effects!", "check-defer-reruns!", "check-hold-breaks!", "check-lines!", "parse-program", "loaded-files!", "includes-given!", "run-checked", "run-checked-more", "compile-program", "compile-checked", "compile-registers!", "compile-conv-native!",
        "compile-global-cell", "compile-new-global", "compile-name-word!", "compile-defining!", "compile-keep-global!", "compile-note-inline!", "compile-forget-globals!", "native-assemble",
        "check-built-in!", "check-syscalls!",
        "native-assemble-x64", "native-assemble-x64-regs", "native-adapter-x64", "native-compile-x64-proc",
    ];

    /// The front end's checker and compilers run as register code, not as
    /// lowered Scheme on the engine (about 28 times as fast): the front
    /// end compiled by the Rust compiler, with register code, and run once
    /// to give its entry points; each `READER_PREFIX` global the Rust side
    /// calls then calls its entry point by `%run-front-end` (the runtime's
    /// `front_end_run_word`, which the caller installs: a machine that
    /// runs register code). The reader lowered is loaded only for an eager
    /// reader (`load_own_reader`).
    /// Where `front_end_native`, checked in the native convention, so that
    /// the closures it makes are native procedures, compiled as they are
    /// made (`TODO.md` §126).
    fn front_end_as_register_code(&mut self) -> R<()> {
        // Checked and compiled once for this executable and this front end,
        // then kept (`front_end_cache`); read back from there after.
        self.as_register_code("the front end", &crate::front_end(), &Self::FRONT_ENTRIES, "fx26-native:", "fx26-reader:", true, crate::front_end_error)
            .map_err(crate::front_end_failure)
    }

    /// Program `text` compiled by the Rust compiler, with register code, and
    /// run once, as the front end is (`front_end_as_register_code`): each of
    /// its globals `entries`, a procedure, then called by `PREFIX:NAME` from
    /// Scheme, run on the runtime's `front_end_run_word`. For a test that
    /// calls a program written in FX-26 many times (lowered, on the
    /// bytecode VM, some 30 times as slow). Not kept between runs.
    pub fn program_as_register_code(&mut self, text: &str, entries: &[&str], prefix: &str) -> R<()> {
        let fail = |m: String| FxError::at(Span::new(FileId(0), 0, 0), m);
        self.as_register_code("the program", text, entries, &format!("{prefix}-native:"), &format!("{prefix}:"), false, |e| e).map_err(fail)
    }

    /// The two above: `text` (`what`) and its `entries` as a product, checked
    /// (its errors said by `read_error`), compiled, kept in the cache if
    /// `keep`, and run; each entry in global `{native}{name}`, and called by
    /// `{prefix}{name}`.
    #[allow(clippy::too_many_arguments)]
    fn as_register_code(
        &mut self,
        what: &str,
        text: &str,
        entries: &[&str],
        native: &str,
        prefix: &str,
        keep: bool,
        read_error: fn(FxError) -> FxError,
    ) -> Result<(), String> {
        let text = register_text(text, entries);
        // The front end's own: from no source of the program's.
        fixpt_heap::regcode::set_source(0);
        // The front end in the native convention where its closures are
        // made native code, kept apart from the cellular one.
        let as_native = keep && self.front_end_native;
        let cache = if keep { front_end_cache(&text, as_native) } else { None };
        let image = cache.as_ref().and_then(|(p, key)| {
            let b = fixpt_heap::Mapped::open(p).ok()?;
            (b.get(..8)? == key.to_le_bytes()).then_some(b)
        });
        // Native, the cache keeps the front end as its first run left it,
        // native code and all (`TODO.md` §126): neither checked, compiled
        // nor run again, where it can be read back.
        let keeping = self.native_keeping.filter(|_| as_native);
        // Read in already, before the runtime was (`with_backend_preloaded`).
        if keeping.is_some()
            && let Some(r) = self.scheme.runtime_unrooted().preloaded.take()
        {
            let standard = self.scheme.make(|m| {
                let both = m.heap().root_at(r);
                let (pieces, st) = (m.heap().car(both), m.heap().cdr(both));
                set_entries(m.heap(), pieces, entries, native);
                st
            });
            self.keep_standard(standard);
            return self.define_entries(entries, native, prefix);
        }
        let (cached, kept) = match keeping {
            Some(_) => (None, image),
            None => (image.and_then(|b| fixpt_heap::image::load_trusted(b.get(CACHE_IMAGE_AT..)?).ok()), None),
        };
        if let (Some(from), Some(k)) = (&kept, &keeping) {
            let mut loaded = false;
            let standard = self.scheme.make(|_| fixpt_heap::Value::FALSE);
            self.scheme.scope(|sc| {
                sc.replace(standard, |m| {
                    let Some(both) = load_native_front_end(k, m.heap(), from) else { return fixpt_heap::Value::FALSE };
                    let (pieces, st) = (m.heap().car(both), m.heap().cdr(both));
                    set_entries(m.heap(), pieces, entries, native);
                    loaded = true;
                    st
                })
            });
            if loaded {
                self.keep_standard(standard);
                return self.define_entries(entries, native, prefix);
            }
        }
        let mut checked = None;
        if cached.is_none() {
            let mut c = if as_native { Checker::with_convention(crate::ast::Conv::Native) } else { Checker::new() };
            let forms = c.read_in(FileId(0), &text).map_err(|e| read_error(e).message)?;
            let done = c.declare_ahead(&forms).map_err(|e| read_error(e).message)?;
            let mut tops = Vec::new();
            for (f, done) in forms.iter().zip(done) {
                if !done {
                    tops.extend(c.top_all(f).map_err(|e| read_error(e).message)?);
                }
            }
            checked = Some((c, tops));
        }
        let limit = self.step_limit();
        self.scheme.engine.set_step_limit(None);
        // The pieces the front end's run made, kept past the scope: the
        // cache is saved once the entries can read the standard environment.
        let made = self.scheme.make(|_| fixpt_heap::Value::FALSE);
        let pieces: Result<(), String> = self.scheme.scope(|sc| {
            let mut compiled = Err(String::new());
            let word = sc.make(|m| {
                if let Some(from) = &cached {
                    compiled = Ok(m.heap().copy_graph_from(from, from.roots_slice()[0]));
                } else if let Some((c, tops)) = &checked {
                    let mut comp = crate::cellular::Compiler::new(m.heap(), c, &text);
                    comp.registers = true;
                    compiled = comp.program(tops);
                    if let (Ok(w), Some((path, key)), None) = (&compiled, &cache, keeping) {
                        save_front_end(m.heap(), *w, path, *key);
                    }
                }
                compiled.clone().unwrap_or(fixpt_heap::Value::FALSE)
            });
            compiled.map_err(|e| format!("{what} as register code: {e}"))?;
            let none = sc.make(|_| fixpt_heap::Value::NULL);
            let pieces = sc.call_global("%run-front-end", &[word, none]).map_err(|e| e.to_string())?;
            sc.replace(made, |m| {
                let p = m.get(pieces);
                set_entries(m.heap(), p, entries, native);
                p
            });
            Ok(())
        });
        self.scheme.engine.set_step_limit(limit);
        pieces?;
        self.define_entries(entries, native, prefix)?;
        if let (Some((path, key)), Some(_)) = (&cache, &keeping) {
            let standard = self.standard26().map_err(|e| e.message)?;
            self.scheme.make(|m| {
                let (p, st) = (m.get(made), m.get(standard));
                save_native_front_end(m.heap(), p, st, path, *key);
                fixpt_heap::Value::NULL
            });
        }
        self.scheme.replace(made, |_| fixpt_heap::Value::NULL);
        Ok(())
    }

    /// Take `standard`, read back with the front end, as the standard
    /// environment read (`standard26`), if the cache kept one.
    fn keep_standard(&mut self, standard: fixpt_scheme::Handle) {
        if self.standard26.is_none() && self.scheme.view(|v| !v.get(standard).is_false()) {
            self.standard26 = Some(standard);
        }
    }

    /// The names the Rust side calls, `{prefix}{name}`, made to call each
    /// entry point in its global (`set_entries`).
    fn define_entries(&mut self, entries: &[&str], native: &str, prefix: &str) -> Result<(), String> {
        self.scheme.eval_str("<register code>", &entry_defines(entries, native, prefix)).map_err(|e| e.to_string())?;
        Ok(())
    }

    /// The reader written in FX-26, for an eager reader to attach to: the
    /// reader alone if the checker and compilers run as register code (they
    /// are loaded at the first form), else the whole front end lowered, as
    /// the session will run it. Not again if it is loaded.
    pub fn load_own_reader(&mut self) -> R<()> {
        if self.scheme.is_bound(&format!("{READER_PREFIX}eager-start-fx26")) {
            return Ok(());
        }
        let load = if self.front_end_compiled { load_reader_alone } else { load_eager_reader };
        load(&mut self.scheme).map_err(crate::front_end_failure)?;
        // Loaded after the front end's register code, whose entries it
        // shares names with (`read-text-at`, `parse-program`): theirs again.
        if self.front_end_compiled && self.scheme.is_bound("fx26-native:check-program") {
            let defines = entry_defines(&Self::FRONT_ENTRIES, "fx26-native:", READER_PREFIX);
            self.scheme.eval_str("<register code>", &defines).map_err(|e| crate::front_end_failure(e.to_string()))?;
        }
        Ok(())
    }

    /// The pieces written in FX-26 (reader, checker, compilers), loaded if
    /// they are not yet.
    pub fn load_own_pieces(&mut self) -> R<()> {
        self.own_pieces()
    }

    /// The pieces written in FX-26, loaded if they are not yet, and told the
    /// program's convention.
    fn own_pieces(&mut self) -> R<()> {
        let fail = crate::front_end_failure;
        // A `load-module`'s path is from where the Rust checker's is.
        crate::syn::set_load_base(self.checker.base_dir.clone());
        crate::syn::set_shared_made(self.shared_made.clone());
        let fasls = self.checker.shared_files.values().filter_map(|f| Some((f.key.clone(), f.fasl.as_ref()?.1.clone()))).collect();
        crate::syn::set_fasl_used(fasls);
        // The reader lowered is the eager reader's alone, loaded when it is
        // wanted (`load_own_reader`): the register code reads.
        if self.front_end_compiled {
            if !self.scheme.is_bound("fx26-native:check-program") {
                self.front_end_as_register_code()?;
            }
        } else if !self.scheme.is_bound(&format!("{READER_PREFIX}check-program")) {
            load_eager_reader(&mut self.scheme).map_err(fail)?;
        }
        // The handles below are this call's: released at its end (what
        // was loaded above stays, made before the mark).
        let mark = self.scheme.root_mark();
        let r = (|| {
            let on = self.scheme.make(|_| fixpt_heap::Value::boolean(self.native_convention));
            self.scheme.call_global(&format!("{READER_PREFIX}check-conv-native!"), &[on]).map_err(|e| fail(e.to_string()))?;
            self.scheme.call_global(&format!("{READER_PREFIX}compile-conv-native!"), &[on]).map_err(|e| fail(e.to_string()))?;
            let on = self.scheme.make(|_| fixpt_heap::Value::boolean(self.globals_effects));
            self.scheme.call_global(&format!("{READER_PREFIX}check-globals-effects!"), &[on]).map_err(|e| fail(e.to_string()))?;
            let on = self.scheme.make(|_| fixpt_heap::Value::boolean(self.defer_reruns));
            self.scheme.call_global(&format!("{READER_PREFIX}check-defer-reruns!"), &[on]).map_err(|e| fail(e.to_string()))?;
            let on = self.scheme.make(|_| fixpt_heap::Value::boolean(self.checker.syscalls));
            self.scheme.call_global(&format!("{READER_PREFIX}check-syscalls!"), &[on]).map_err(|e| fail(e.to_string()))?;
            Ok(())
        })();
        self.scheme.release_to(mark);
        r
    }

    /// The value of the global `name`, as the forms defined so far make it,
    /// compiled by the compiler written in FX-26 with register code: given
    /// to `f`, with the runtime (see [`crate::syn::with_last_value`]).
    pub fn with_global_value<T>(&mut self, name: &str, f: impl FnOnce(&mut fixpt_runtime::Runtime, fixpt_heap::Value) -> T) -> R<Result<T, String>> {
        self.with_last_value(&format!("{name}\n"), None, f)
    }

    /// The same for the value of expression `exp` (text) as a procedure of
    /// no arguments that computes it.
    pub fn with_thunk<T>(&mut self, exp: &str, f: impl FnOnce(&mut fixpt_runtime::Runtime, fixpt_heap::Value) -> T) -> R<Result<T, String>> {
        self.with_last_value(&format!("(lambda () {exp})\n"), None, f)
    }

    /// The same, for the native runner: the thunk compiled first by the
    /// compiler written in FX-26, if it compiles them (`native_fx`).
    fn with_native_thunk<T>(&mut self, exp: &str, f: impl FnOnce(&mut fixpt_runtime::Runtime, fixpt_heap::Value) -> T) -> R<Result<T, String>> {
        self.with_last_value(&format!("(lambda () {exp})\n"), self.native_fx, f)
    }

    /// Whether a definition of `x` names its word for its global, as the
/// compilers do (`name_word_for`, `c-name-for!`): a `lambda`, through a
/// `the` or a convention, not a region's.
fn names_its_word(c: &Checker, mut x: crate::ast::ExpId) -> bool {
    use crate::ast::Exp;
    loop {
        match c.arena.exp_at(x) {
            Exp::PLambda { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } => x = *body,
            Exp::Lambda { .. } => return true,
            _ => return false,
        }
    }
}

/// `form` (text), a definition of `name` whose value is `init` (text),
    /// in the native convention: checked, as the next form; `name`'s global
    /// made by the compiler written in FX-26; `init` run as a procedure of
    /// no arguments, by `run`; and its value put in the global. What `run`
    /// did instead, if anything else.
    fn native_define(&mut self, name: &str, form: &str, init: &str, lambda: bool, run: NativeRunner) -> R<Result<(), NativeRun>> {
        self.own_pieces()?;
        let standard = self.next_standard()?;
        // What is loaded is loaded, above; the handles below are this
        // definition's, released at its end: kept, the global's cell would
        // keep each old definition alive, its code with it.
        let mark = self.scheme.root_mark();
        let r = self.native_define_in(standard, name, form, init, lambda, run);
        self.scheme.release_to(mark);
        r
    }

    fn native_define_in(
        &mut self,
        standard: Option<fixpt_scheme::Handle>,
        name: &str,
        form: &str,
        init: &str,
        lambda: bool,
        run: NativeRunner,
    ) -> R<Result<(), NativeRun>> {
        // The Rust checker took the form: the checker written in FX-26
        // refusing it is the two disagreeing, said, not a reason to run it
        // another way, which would hide it (`TODO.md` §97).
        if let Err(why) = crate::syn::check_only(&mut self.scheme, standard, FileId(0), form)? {
            return Err(FxError::at(Span::new(FileId(0), 0, 0), format!("the checkers disagree: the Rust checker takes `{name}`'s definition, and the one written in FX-26 refuses it: {why}")));
        }
        // The value is checked again below, as an expression (and, if the
        // native compiler declines it, the definition as cellular code):
        // under the breaks as this check began, so that a definition this
        // one broke is not refused where its new body calls it.
        self.hold_breaks(true)?;
        self.own_begun = true;
        let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
        let sym = self.scheme.make(|m| m.heap().intern(name));
        let cell = self.scheme.call_global(&format!("{READER_PREFIX}compile-new-global"), &[sym]).map_err(fail)?;
        // The global, kept where a collection updates it while `init` runs.
        let mut at = 0;
        self.scheme.make(|m| {
            let c = m.get(cell);
            at = m.heap().push_root(c);
            c
        });
        let fuel = self.step_limit.unwrap_or(u64::MAX >> 1);
        // A lambda's word named for the global, as a definition compiled
        // is (`c-define-lambda`), not for where it is in the thunk: so that
        // a profile, a disassembly or a fault says which procedure. The
        // thunk's, compiled first, `define NAME`. The names let go after,
        // if nothing took them. The lambda so named is the definition's
        // (`compile-defining!`), whose global is written once after: so its
        // calls of itself in tail position loop, as they do in a definition
        // compiled whole.
        let name_word = |s: &mut Self, named: bool| {
            let ns = s.scheme.make(|m| {
                let h = m.heap();
                if named {
                    let (thunk, n) = (h.intern(&format!("define {name}")), h.intern(name));
                    let tail = h.cons(n, fixpt_heap::Value::NULL);
                    h.cons(thunk, tail)
                } else {
                    fixpt_heap::Value::NULL
                }
            });
            s.scheme.call_global(&format!("{READER_PREFIX}compile-name-word!"), &[ns])?;
            let defining = s.scheme.make(|m| {
                let h = m.heap();
                if named {
                    let n = h.intern(name);
                    h.cons(n, fixpt_heap::Value::NULL)
                } else {
                    fixpt_heap::Value::NULL
                }
            });
            s.scheme.call_global(&format!("{READER_PREFIX}compile-defining!"), &[defining]).map(|_| ())
        };
        if lambda {
            name_word(self, true).map_err(fail)?;
        }
        let r = self.with_native_thunk(init, |rt, clo| match {
            let (start, compiled) = (std::time::Instant::now(), rt.compile_nanos);
            let ran = run(rt, clo, fuel);
            rt.run_nanos += (start.elapsed().as_nanos() as u64).saturating_sub(rt.compile_nanos - compiled);
            ran
        } {
            NativeRun::Ran(Ok(v)) => {
                let g = rt.heap.root_at(at);
                rt.heap.set_bloblet_slot(g, 2, v);
                // A write, as `global!`'s, which the guards count: the
                // global may be one kept, defined again.
                let w = fixpt_heap::layout::cellular::GLOBAL_WRITES;
                let n = rt.heap.bloblet_slot(g, w).as_fixnum();
                rt.heap.set_bloblet_slot(g, w, fixpt_heap::Value::fixnum(n + 1));
                Ok(())
            }
            other => Err(other),
        });
        self.scheme.runtime_unrooted().heap.pop_roots_to(at);
        if lambda {
            name_word(self, false).map_err(fail)?;
        }
        if matches!(r, Ok(Ok(Ok(())))) {
            // A lambda, noted for inlining, as a definition compiled is.
            let sym = self.scheme.make(|m| m.heap().intern(name));
            self.scheme.call_global(&format!("{READER_PREFIX}compile-note-inline!"), &[sym]).map_err(fail)?;
        }
        Ok(match r? {
            Ok(done) => done,
            Err(why) => Err(NativeRun::Declined(why)),
        })
    }

    /// Global `name`'s value, if a cellular closure, compiled by `compile`
    /// to a native closure, which the global then holds; or why not.
    /// The globals whose code has a call of global `name` inlined, behind
    /// a guard that `name` still holds what it held when they were
    /// compiled (`,inliners`): what a redefinition of `name` sends back to
    /// calling it. Nothing need be compiled again; it is for knowing.
    pub fn inliners(&mut self, name: &str) -> R<Result<Vec<String>, String>> {
        if self.strategy != Strategy::Cellular {
            return Ok(Err("only compiled code inlines: not on rs-scheme-vm or fx-ast-eval".into()));
        }
        self.own_pieces()?;
        let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
        let cell_of = |s: &mut Self, n: &str| -> R<Option<fixpt_scheme::Handle>> {
            let sym = s.scheme.make(|m| m.heap().intern(n));
            let cells = s.scheme.call_global(&format!("{READER_PREFIX}compile-global-cell"), &[sym]).map_err(fail)?;
            let mut found = false;
            let g = s.scheme.make(|m| {
                let cells = m.get(cells);
                found = cells.is_pair();
                if found { m.heap().car(cells) } else { fixpt_heap::Value::FALSE }
            });
            Ok(found.then_some(g))
        };
        let Some(target) = cell_of(self, name)? else { return Ok(Err(format!("`{name}` has no global"))) };
        let mut out = Vec::new();
        let names: Vec<String> = self.checker.value_names().into_iter().map(|n| self.checker.interner.name(n).to_string()).collect();
        // Its own calls of itself, guarded too, are not counted: redefined,
        // it is not called by what it was.
        for n in names.into_iter().filter(|n| n != name) {
            let Some(g) = cell_of(self, &n)? else { continue };
            let mut inlines = false;
            self.scheme.make(|m| {
                let (g, t) = (m.get(g), m.get(target));
                let heap = m.heap();
                inlines = fixpt_runtime::disasm::inlines_global(heap, heap.bloblet_slot(g, 2), t);
                fixpt_heap::Value::FALSE
            });
            if inlines {
                out.push(n);
            }
        }
        out.sort();
        Ok(Ok(out))
    }

    /// Global `name`'s procedure compiled natively, if it holds one:
    /// whether it did (a value of no procedure, such as a module, is let be),
    /// or why it could not be.
    fn compile_global_natively(&mut self, name: Sym, compile: NativeCompiler) -> R<Result<bool, String>> {
        self.released(|s| {
        let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
        let text = s.checker.interner.name(name).to_string();
        let sym = s.scheme.make(|m| m.heap().intern(&text));
        let cells = s.scheme.call_global(&format!("{READER_PREFIX}compile-global-cell"), &[sym]).map_err(fail)?;
        let (mut r, mut nanos, mut fx) = (Ok(false), 0, None);
        s.scheme.make(|m| {
            let cells = m.get(cells);
            if !cells.is_pair() {
                r = Err(format!("`{text}` has no global"));
                return fixpt_heap::Value::FALSE;
            }
            let heap = m.heap();
            let g = heap.car(cells);
            let v = heap.bloblet_slot(g, 2);
            // A cellular closure; or, in the native convention, what
            // cellular code makes, a native closure that adapts one
            // (`nclosure`), which the compiler sees through (any other
            // native closure it gives back as it is).
            let kind = |k| v.is_bloblet() && heap.bloblet_kind(v) == fixpt_heap::layout::kind(k);
            if !(kind("cellular-closure") || kind("native-closure")) {
            } else if s.native_fx.is_some() {
                // By the compiler written in FX-26, below: the global and
                // its value rooted while it runs.
                fx = Some((g, v));
            } else {
                let start = std::time::Instant::now();
                let compiled = compile(heap, v);
                nanos = start.elapsed().as_nanos() as u64;
                // The same procedure, in the other convention: not counted
                // as a write, so that what was compiled assuming the global
                // holds it still holds (`global-guard`).
                match compiled {
                    Ok(native) => {
                        heap.set_bloblet_slot(g, 2, native);
                        r = Ok(true);
                    }
                    Err(why) => r = Err(why),
                }
            }
            fixpt_heap::Value::FALSE
        });
        if let (Some(compile_fx), Some((g, v))) = (s.native_fx, fx) {
            let (g, v) = (s.scheme.make(|_| g), s.scheme.make(|_| v));
            let start = std::time::Instant::now();
            let compiled = compile_fx(&mut s.scheme, v);
            nanos = start.elapsed().as_nanos() as u64;
            match compiled {
                Ok(native) => {
                    s.scheme.make(|m| {
                        let (g, native) = (m.get(g), m.get(native));
                        m.heap().set_bloblet_slot(g, 2, native);
                        fixpt_heap::Value::FALSE
                    });
                    r = Ok(true);
                }
                Err(why) => r = Err(why),
            }
        }
        s.scheme.runtime_unrooted().compile_nanos += nanos;
        Ok(r)
        })
    }

    /// Run `f`, then release the handles it made (and the roots it pushed):
    /// for work done for one form, whose handles would otherwise root what
    /// they hold for the rest of the session. Anything that must last (what
    /// a lazy load makes, `standard26`) is made before.
    fn released<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let mark = self.scheme.root_mark();
        let r = f(self);
        self.scheme.release_to(mark);
        r
    }

    /// `text` checked and compiled as the next form of this session's
    /// program, and run: its value, to `f`.
    fn with_last_value<T>(&mut self, text: &str, native: Option<NativeFx>, f: impl FnOnce(&mut fixpt_runtime::Runtime, fixpt_heap::Value) -> T) -> R<Result<T, String>> {
        self.own_pieces()?;
        self.scheme.engine.set_step_limit(None);
        let standard = self.next_standard()?;
        self.released(|s| {
        let on = s.scheme.make(|_| fixpt_heap::Value::TRUE);
        let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
        s.scheme.call_global(&format!("{READER_PREFIX}compile-registers!"), &[on]).map_err(fail)?;
        // Its register code said to come from `text`, a source
        // (`crate::sources`): what this compile queues, made after, too, so
        // until the next.
        fixpt_heap::regcode::set_source(s.source_of(text));
        let r = crate::syn::with_last_value(&mut s.scheme, standard, FileId(0), text, native, f);
        s.own_begun |= !matches!(&r, Ok(Err(m)) if m.starts_with("check:"));
        let off = s.scheme.make(|_| fixpt_heap::Value::boolean(s.register_code));
        s.scheme.call_global(&format!("{READER_PREFIX}compile-registers!"), &[off]).map_err(fail)?;
        s.scheme.engine.set_step_limit(s.step_limit);
        r
        })
    }

    /// Check `text` with the checker written in FX-26 (read and parsed in
    /// FX-26 too): see [`crate::syn::check_with_fx26_checker`].
    pub fn check_with_own_checker(&mut self, text: &str) -> R<crate::syn::Checked26> {
        self.shared_made.clear();
        self.own_pieces()?;
        // Generous, but a checker that loops is an error, not a hang.
        self.scheme.engine.set_step_limit(Some(2_000_000_000));
        let standard = self.standard26()?;
        let r = crate::syn::check_with_fx26_checker(&mut self.scheme, standard, FileId(0), text);
        self.scheme.engine.set_step_limit(self.step_limit);
        r
    }

    /// What the checker written in FX-26 noted of the effects of what it
    /// last checked (`checked-effects`): each expression's start, end (in
    /// characters) and effect summary, newest first; two at one span apart.
    pub fn own_effect_summaries(&mut self) -> R<Vec<(i64, i64, i64)>> {
        self.released(|s| {
        let fail = |e: fixpt_scheme::SessionError| FxError::at(Span::new(FileId(0), 0, 0), e.to_string());
        let notes = s.scheme.call_global(&format!("{READER_PREFIX}checked-effects"), &[]).map_err(fail)?;
        let mut out = Vec::new();
        s.scheme.make(|m| {
            let mut l = m.get(notes);
            let heap = m.heap();
            while l.is_pair() {
                let p = heap.car(l);
                // Its expression's identity (`k-at`), and the summary
                // (`n-summary`, a sum, its value a product of one field).
                let (at, noted) = (heap.bloblet_slot(p, 2), heap.bloblet_slot(p, 3));
                let summary = heap.bloblet_slot(heap.bloblet_slot(noted, 3), 2).as_fixnum();
                out.push((heap.bloblet_slot(at, 2).as_fixnum(), heap.bloblet_slot(at, 3).as_fixnum(), summary));
                l = heap.cdr(l);
            }
            fixpt_heap::Value::FALSE
        });
        Ok(out)
        })
    }

    /// Compile `text` to a cellular word with the compiler written in FX-26
    /// (read and parsed in FX-26 too), and run it on the cellular machine:
    /// its value as Scheme would write it, or `!! ` and why not.
    pub fn compile_with_own_compiler(&mut self, text: &str) -> R<String> {
        self.compile_with_own_compiler_showing(text, false).map(|(out, _)| out)
    }

    /// The checker's start for the next form of this session's program:
    /// the initial environment, if it has not begun; else none, so that the
    /// form is checked after the ones before.
    fn next_standard(&mut self) -> R<Option<fixpt_scheme::Handle>> {
        if self.own_begun { Ok(None) } else { self.standard26().map(Some) }
    }

    /// `text`, one form, as the next of this session's program: checked
    /// after the forms before, compiled against the globals they made, and
    /// run; as [`compile_with_own_compiler_showing`](Self::compile_with_own_compiler_showing).
    fn compile_form_showing(&mut self, text: &str, show: bool) -> R<(String, Option<String>)> {
        self.own_pieces()?;
        let standard = self.next_standard()?;
        let r = self.compile_showing_in(standard, text, show);
        self.own_begun |= !matches!(&r, Ok((out, _)) if out.starts_with("!! check:"));
        r
    }

    /// The same, and, if `show`, the words it made, disassembled. A whole
    /// program: the checker begins again.
    pub fn compile_with_own_compiler_showing(&mut self, text: &str, show: bool) -> R<(String, Option<String>)> {
        self.shared_made.clear();
        self.processes_forgotten();
        self.own_pieces()?;
        let standard = self.standard26()?;
        self.own_begun = false;
        // The compiler, too, sees none of the globals made before.
        self.scheme
            .call_global(&format!("{READER_PREFIX}compile-forget-globals!"), &[])
            .map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), e.to_string()))?;
        self.compile_showing_in(Some(standard), text, show)
    }

    fn compile_showing_in(&mut self, standard: Option<fixpt_scheme::Handle>, text: &str, show: bool) -> R<(String, Option<String>)> {
        self.own_pieces()?;
        self.released(|s| {
        s.scheme.engine.set_step_limit(None);
        let on = s.scheme.make(|_| fixpt_heap::Value::boolean(s.register_code));
        s.scheme
            .call_global(&format!("{READER_PREFIX}compile-registers!"), &[on])
            .map_err(|e| FxError::at(Span::new(FileId(0), 0, 0), e.to_string()))?;
        let r = crate::syn::compile_with_fx26_compiler_showing(&mut s.scheme, standard, FileId(0), text, show, s.step_limit);
        s.scheme.engine.set_step_limit(s.step_limit);
        r
        })
    }

    /// [`run_program`](Self::run_program), reading with the reader written
    /// in FX-26: nothing of the Rust reader on the way.
    pub fn run_program_read_by_fx26(&mut self, text: &str) -> R<Result<String, String>> {
        let forms = self.read_with_own_reader(text)?;
        let mut last = Ok(String::new());
        for out in self.run_forms(&forms)? {
            let out = out?;
            match out.value {
                Ok(Some(v)) => last = Ok(v),
                Ok(None) => {}
                Err(e) => return Ok(Err(e)),
            }
        }
        Ok(last)
    }

    /// Run a whole program, and the value of its last expression. Its
    /// definitions may refer to each other in any order: see
    /// `Checker::declare_ahead`.
    pub fn run_program(&mut self, text: &str) -> R<Result<String, String>> {
        let forms = self.checker.read_in(FileId(0), text)?;
        let mut last = Ok(String::new());
        for out in self.run_forms(&forms)? {
            let out = out?;
            match out.value {
                Ok(Some(v)) => last = Ok(v),
                Ok(None) => {}
                Err(e) => return Ok(Err(e)),
            }
        }
        Ok(last)
    }
}

/// A built-in module file's text as a `module`, if `init` loads one that
/// takes no parameters (`(load-module "fx26:processes.fx")`): what a
/// hidden global of a load is defined as natively, so that the file's
/// procedures are in the convention the program's are. Loaded, they would
/// be compiled apart, as cellular code, and a continuation captured in one
/// called from the program (a process's `receive`) could not be taken
/// across the call between the conventions.
fn built_in_load(init: &Syntax, c: &Checker) -> Option<String> {
    let fixpt_read::Datum::List { items, tail: None } = &init.datum else { return None };
    let [head, path] = &items[..] else { return None };
    if !head.as_symbol().is_some_and(|h| c.interner.name(h) == "load-module") {
        return None;
    }
    let fixpt_read::Datum::Str(path) = &path.datum else { return None };
    let text = crate::built_in_module(path)?;
    (!text.contains("(module-parameters")).then(|| format!("(module\n{text}\n)"))
}

/// A definition's type, if it says one, and initializer, when `form` is
/// `(define name [type] init)` of `name`; not one of the forms that define
/// names of their own (`define-generative`'s coercions, say).
fn definition_init<'f>(form: &'f Syntax, c: &Checker, name: Sym) -> Option<(Option<&'f Syntax>, &'f Syntax)> {
    let fixpt_read::Datum::List { items, tail: None } = &form.datum else { return None };
    let is = |s: &Syntax, n: &str| s.as_symbol().is_some_and(|x| c.interner.name(x) == n);
    if !((is(items.first()?, "define") || is(items.first()?, "define*")) && is(items.get(1)?, c.interner.name(name))) {
        return None;
    }
    match items.len() {
        3 => Some((None, &items[2])),
        4 => Some((Some(&items[2]), &items[3])),
        _ => None,
    }
}

/// The path of `(compile-file "path")`, if `form` is one, and whether it
/// is `(compile-file "path" program)`, a program's file.
fn compile_file_form(form: &Syntax, c: &Checker) -> Option<(String, bool)> {
    let fixpt_read::Datum::List { items, tail: None } = &form.datum else { return None };
    let (head, path, program) = match &items[..] {
        [head, path] => (head, path, false),
        [head, path, kind] if kind.as_symbol().is_some_and(|k| c.interner.name(k) == "program") => (head, path, true),
        _ => return None,
    };
    if !head.as_symbol().is_some_and(|h| c.interner.name(h) == "compile-file") {
        return None;
    }
    let fixpt_read::Datum::Str(path) = &path.datum else { return None };
    Some((path.clone(), program))
}
