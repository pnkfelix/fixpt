//! `.fasl` files: a module file checked and compiled once, and loaded after
//! without either (`docs/research/fasl.md`; the user's, 2026-10-28).
//!
//! A load of a file is one value, its hidden global's (`%shared:key`,
//! `TODO.md` §68). A `.fasl` beside the file keeps what a load needs of it:
//! the type the load is checked at, the files it loads itself, and the
//! value, a heap graph of its procedures and data. A load whose `.fasl` is
//! fresh is checked as `(the T %fasl-value)` after the loads of the files
//! the file loads, and its hidden global is
//! given the value read, linked to the session it is loaded into: each
//! global cell its code names found by name, as Larceny's `#^G` is
//! (`src/Asm/Shared/makefasl.sch`), and each value of a file it loads by
//! that load.
//!
//! The file: a line `#fasl(fixpt-fasl 1)`, a header of lines `word value`,
//! then `image N` and the image's `N` bytes (`fixpt_heap::image`). Fresh is
//! by digest, not by date: the file's text and the stamps of the files it
//! loads, each the digest of its text and of its loads' stamps, so that a
//! change anywhere below makes it stale; and by the executable, the
//! architecture and the program's convention.

use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD, CODE_SOURCE, GLOBAL_FIELDS, GLOBAL_NAME, PRIMITIVES, ROUTINE_DOCOL, WORD_ENTRY};
use fixpt_heap::{CodePart, Heap, ObjType, Value};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

/// A `.fasl`'s first line.
pub const MARK: &str = "#fasl(fixpt-fasl 1)";

/// What a `.fasl` says of itself before its image.
#[derive(Clone, Debug, PartialEq)]
pub struct Header {
    /// The executable that made it ([`build`]).
    pub build: u64,
    /// The architecture its code's stubs are for.
    pub arch: String,
    /// Whether it was compiled in the native convention.
    pub native: bool,
    /// What the file is to what reads it.
    pub kind: Kind,
    /// The file's text's digest ([`digest`]).
    pub source: u64,
    /// Its stamp ([`stamp`]).
    pub stamp: u64,
    /// The files it loads, in the order it first loads them.
    pub deps: Vec<Dep>,
    /// The type a load of it is checked at, each file it loads that the
    /// type names `%fasl-dep:i`, `i` its place in `deps`: a module file's.
    pub ty: String,
    /// Or, a maker's (a file of a `lambda` of the modules it is given), the
    /// expression its load is checked as (`Checker::fasl_made`), so named.
    pub made: String,
    /// A program's file's definitions kept, each a procedure's, the `i`th
    /// the image's value `i`.
    pub defs: Vec<Def>,
    /// The type abbreviations its types name, each with what it is.
    pub aliases: Vec<(String, String)>,
}

/// What a `.fasl`'s file is: a module file, a `load-input` file (its key
/// `input:`), or a program's, whose forms run where it is loaded (`,load`,
/// `fixpt run`).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Kind {
    Module,
    Input,
    Program,
}

impl Kind {
    fn word(self) -> &'static str {
        match self {
            Kind::Module => "module",
            Kind::Input => "input",
            Kind::Program => "program",
        }
    }
}

/// A program's definition of a procedure kept in its `.fasl`: which of the
/// file's forms it is, the name it defines, its type, and each global its
/// code uses with the type it had (`Fx26Session::program_fasl_fresh`).
#[derive(Clone, Debug, PartialEq)]
pub struct Def {
    pub form: usize,
    /// Whether it is a binding of a `define-rec`, whose bindings are its
    /// form's `Def`s, in order.
    pub rec: bool,
    pub name: String,
    pub ty: String,
    /// The expression its declaration has the type by ([`fasl_value_at`]).
    pub init: String,
    pub uses: Vec<(String, String)>,
    /// What its definition said as it was made, a line each (that the
    /// native compiler declined it, say), said again where it is loaded.
    pub said: Vec<String>,
    /// The type abbreviations its type names (`Header::aliases`).
    pub types: Vec<String>,
}

/// A file a `.fasl`'s file loads: as its load wrote it, and the stamp it had.
#[derive(Clone, Debug, PartialEq)]
pub struct Dep {
    pub path: String,
    pub input: bool,
    pub stamp: u64,
}

/// A file loaded, as the checker keeps it by its hidden global
/// (`Checker::shared_files`): what its `.fasl` is made of, and, read from
/// one, the `.fasl` and the expression its load was checked as.
#[derive(Clone, Debug)]
pub struct SharedFile {
    /// Its key (`input:` before a `load-input`'s), as `%shared:key` names it.
    pub key: String,
    /// The file.
    pub path: PathBuf,
    pub input: bool,
    /// Its text's digest, and its stamp.
    pub source: u64,
    pub stamp: u64,
    /// The files it loads, in the order it first loads them: each path as
    /// its load wrote it, whether a `load-input`, and its hidden global.
    pub deps: Vec<(String, bool, fixpt_read::Sym)>,
    /// The type its load is checked at, once checked.
    pub ty: Option<crate::ast::TyId>,
    /// The `.fasl` it was read from, and the expression its load was.
    pub fasl: Option<(PathBuf, String)>,
}

/// The name a type in a `.fasl` gives the hidden global of its `i`th load.
pub fn dep_name(i: usize) -> String {
    format!("%fasl-dep:{i}")
}

/// The `.fasl` beside the file at `source`.
pub fn path_for(source: &Path) -> PathBuf {
    source.with_extension("fasl")
}

/// A digest of `text`.
pub fn digest(text: &str) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    ("fixpt-fasl", text).hash(&mut h);
    h.finish()
}

/// A file's stamp: its text's digest and its loads' stamps, in order.
pub fn stamp(source: u64, deps: &[u64]) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    (source, deps).hash(&mut h);
    h.finish()
}

/// This executable, by its size and time, as the front end's cache keys
/// it (`session::front_end_cache`): a `.fasl` another made is stale.
pub fn build() -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    if let Some(meta) = std::env::current_exe().ok().and_then(|e| std::fs::metadata(e).ok()) {
        (meta.len(), meta.modified().ok()).hash(&mut h);
    }
    h.finish()
}

impl Header {
    /// The file: this header, then `image`.
    pub fn file(&self, image: &[u8]) -> Vec<u8> {
        let mut out = format!("{MARK}\nbuild {:016x}\narch {}\nconv {}\nkind {}\nsource {:016x}\nstamp {:016x}\n",
            self.build, self.arch, if self.native { "native" } else { "cellular" }, self.kind.word(), self.source, self.stamp);
        for d in &self.deps {
            out.push_str(&format!("dep {} {:016x} {}\n", if d.input { "input" } else { "module" }, d.stamp, d.path));
        }
        if self.kind != Kind::Program {
            out.push_str(&format!("type {}\n", self.ty));
        }
        if !self.made.is_empty() {
            out.push_str(&format!("made {}\n", self.made));
        }
        for (n, t) in &self.aliases {
            out.push_str(&format!("alias {n} {t}\n"));
        }
        for d in &self.defs {
            out.push_str(&format!("{} {} {} {}\ninit {}\n", if d.rec { "rec" } else { "def" }, d.form, d.name, d.ty, d.init));
            for (n, t) in &d.uses {
                out.push_str(&format!("use {n} {t}\n"));
            }
            for l in &d.said {
                out.push_str(&format!("said {l}\n"));
            }
            if !d.types.is_empty() {
                out.push_str(&format!("types {}\n", d.types.join(" ")));
            }
        }
        out.push_str(&format!("image {}\n", image.len()));
        let mut bytes = out.into_bytes();
        bytes.extend_from_slice(image);
        bytes
    }

    /// The header of `.fasl` file `bytes`, and its image; or what is wrong.
    pub fn read(bytes: &[u8]) -> Result<(Header, &[u8]), String> {
        let mut rest = bytes;
        let mut line = || -> Result<&str, String> {
            let n = rest.iter().position(|b| *b == b'\n').ok_or("it ends in its header")?;
            let l = std::str::from_utf8(&rest[..n]).map_err(|_| "its header is not text")?;
            rest = &rest[n + 1..];
            Ok(l)
        };
        if line()? != MARK {
            return Err(format!("it does not begin `{MARK}`"));
        }
        let hex = |s: &str| u64::from_str_radix(s, 16).map_err(|_| format!("`{s}` is not a digest"));
        let mut h = Header { build: 0, arch: String::new(), native: false, kind: Kind::Module, source: 0, stamp: 0, deps: Vec::new(), ty: String::new(), made: String::new(), defs: Vec::new(), aliases: Vec::new() };
        loop {
            let l = line()?;
            let (word, value) = l.split_once(' ').ok_or_else(|| format!("a header line `{l}`"))?;
            match word {
                "build" => h.build = hex(value)?,
                "arch" => h.arch = value.to_string(),
                "conv" => h.native = value == "native",
                "kind" => {
                    h.kind = match value {
                        "input" => Kind::Input,
                        "program" => Kind::Program,
                        _ => Kind::Module,
                    }
                }
                "source" => h.source = hex(value)?,
                "stamp" => h.stamp = hex(value)?,
                "dep" => {
                    let mut parts = value.splitn(3, ' ');
                    let (Some(kind), Some(st), Some(path)) = (parts.next(), parts.next(), parts.next()) else {
                        return Err(format!("a header line `{l}`"));
                    };
                    h.deps.push(Dep { path: path.to_string(), input: kind == "input", stamp: hex(st)? });
                }
                "type" => h.ty = value.to_string(),
                "made" => h.made = value.to_string(),
                "def" | "rec" => {
                    let mut parts = value.splitn(3, ' ');
                    let (Some(form), Some(name), Some(ty)) = (parts.next(), parts.next(), parts.next()) else {
                        return Err(format!("a header line `{l}`"));
                    };
                    let form = form.parse().map_err(|_| format!("a header line `{l}`"))?;
                    let rec = word == "rec";
                    h.defs.push(Def { form, rec, name: name.to_string(), ty: ty.to_string(), init: String::new(), uses: Vec::new(), said: Vec::new(), types: Vec::new() });
                }
                "types" => h.defs.last_mut().ok_or_else(|| format!("a header line `{l}` before any `def`"))?.types = value.split(' ').map(str::to_string).collect(),
                "said" => h.defs.last_mut().ok_or_else(|| format!("a header line `{l}` before any `def`"))?.said.push(value.to_string()),
                "init" => h.defs.last_mut().ok_or_else(|| format!("a header line `{l}` before any `def`"))?.init = value.to_string(),
                "alias" => {
                    let (name, ty) = value.split_once(' ').ok_or_else(|| format!("a header line `{l}`"))?;
                    h.aliases.push((name.to_string(), ty.to_string()));
                }
                "use" => {
                    let (name, ty) = value.split_once(' ').ok_or_else(|| format!("a header line `{l}`"))?;
                    h.defs.last_mut().ok_or_else(|| format!("a header line `{l}` before any `def`"))?.uses.push((name.to_string(), ty.to_string()));
                }
                "image" => {
                    let n: usize = value.parse().map_err(|_| format!("a header line `{l}`"))?;
                    if rest.len() != n {
                        return Err(format!("its image is {} bytes, and it says {n}", rest.len()));
                    }
                    return Ok((h, rest));
                }
                _ => return Err(format!("a header line `{l}`")),
            }
        }
    }
}

/// What a `.fasl`'s value links to in the session that loads it, not kept
/// in it: a global's cell by its name (the standard environment's), or the
/// cell of the hidden global of the file's `i`th load; or that load's value.
#[derive(Clone, Debug, PartialEq)]
pub enum Link {
    Global(String),
    DepCell(usize),
    DepValue(usize),
}

/// A global's cell (`layout::cellular::GLOBAL_*`, `%fx26-make-global`): its
/// name, if `v` is one.
fn global_name(heap: &Heap, v: Value) -> Option<String> {
    if !v.is_bloblet() || heap.obj_type(v).is_some() || heap.bloblet_kind(v) != const { fixpt_heap::layout::kind("bloblet") } {
        return None;
    }
    let h = heap.bloblet_head(v);
    if h.fields != GLOBAL_FIELDS + 1 || h.bytes != 0 {
        return None;
    }
    let n = heap.bloblet_slot(v, GLOBAL_NAME);
    (n.is_bloblet() && heap.obj_type(n) == Some(ObjType::Symbol)).then(|| heap.symbol_name(n))
}

/// What `v` reaches, each object once, by `visit`, which says whether to go
/// into it (a pair's car and cdr; a bloblet's fields).
fn walk(heap: &Heap, root: Value, mut visit: impl FnMut(&Heap, Value) -> Result<bool, String>) -> Result<(), String> {
    let mut seen = std::collections::HashSet::new();
    let mut todo = vec![root];
    while let Some(v) = todo.pop() {
        if !v.is_ref() {
            continue;
        }
        let v = if v.is_suffix_ref() { heap.suffix_ref_owner(v) } else { v };
        if !seen.insert(v.raw()) || !visit(heap, v)? {
            continue;
        }
        if v.is_pair() {
            todo.extend([heap.car(v), heap.cdr(v)]);
        } else if heap.obj_type(v) != Some(ObjType::Symbol) {
            let trailer = heap.bloblet_has_trailer(v) as usize;
            todo.extend(((1 + trailer)..=heap.bloblet_head(v).fields).map(|k| heap.bloblet_slot(v, k)));
        }
    }
    Ok(())
}

/// Value `value`, a load's, in `heap`, as a `.fasl`'s image: copied into a
/// heap of its own but for what it links to (`Link`): each global cell
/// (`deps`' hidden globals' by their place, `deps[i].0` its name), each of
/// `deps`' values (`deps[i].1`). A native closure is kept as the cellular
/// one it was made from, which the code area runs in either convention
/// (`docs/research/code-stubs.md`): an adapter (`adapter`'s code) as the
/// closure it adapts; one compiled, as a cellular closure of its code's
/// word over the same values. Each word's compiled entry (a machine's slot
/// number, this process's) is let go, so that the loader's machine
/// compiles it again. Any other native code is refused: it calls by
/// numbers and addresses that are this process's.
pub fn image(heap: &mut Heap, value: Value, deps: &[(String, Value)], adapter: Option<Value>) -> Result<Vec<u8>, String> {
    let closure_kind = const { fixpt_heap::layout::kind("native-closure") };
    let mut links: Vec<(Value, Link)> = Vec::new();
    // Each native closure, and what it is kept as: the closure an adapter
    // adapts, or a cellular closure to make of a word over values.
    let mut adapted: Vec<(Value, Value)> = Vec::new();
    let mut compiled: Vec<(Value, Value, Vec<Value>)> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let mut todo = vec![value];
    while let Some(v) = todo.pop() {
        if !v.is_ref() {
            continue;
        }
        let v = if v.is_suffix_ref() { heap.suffix_ref_owner(v) } else { v };
        if !seen.insert(v.raw()) {
            continue;
        }
        if let Some(name) = global_name(heap, v) {
            let link = match deps.iter().position(|(n, _)| *n == name) {
                Some(i) => Link::DepCell(i),
                None => Link::Global(name),
            };
            links.push((v, link));
            continue;
        }
        if let Some(i) = deps.iter().position(|(_, d)| d.raw() == v.raw()) {
            links.push((v, Link::DepValue(i)));
            continue;
        }
        if v.is_pair() {
            todo.extend([heap.car(v), heap.cdr(v)]);
            continue;
        }
        if heap.obj_type(v) == Some(ObjType::Symbol) {
            continue;
        }
        // Native code: not gone into, its words being what is kept. If it
        // is reached but through a closure kept as a cellular one, the copy
        // refuses it.
        if heap.code_part(v) == Some(CodePart::Native) {
            continue;
        }
        let fields = heap.bloblet_head(v).fields;
        if heap.obj_type(v).is_none() && heap.bloblet_kind(v) == closure_kind {
            let code = heap.bloblet_slot(v, CLOSURE_WORD);
            let free: Vec<Value> = (CLOSURE_FREE0..=fields).map(|k| heap.bloblet_slot(v, k)).collect();
            todo.extend(free.iter().copied());
            if Some(code) == adapter {
                adapted.push((v, free[0]));
                continue;
            }
            let word = heap.bloblet_slot(code, CODE_SOURCE);
            if !(word.is_bloblet() && heap.is_cellular_word(word)) {
                return Err("it holds a native procedure compiled from no cellular word".into());
            }
            todo.push(word);
            compiled.push((v, word, free));
            continue;
        }
        let trailer = heap.bloblet_has_trailer(v) as usize;
        todo.extend(((1 + trailer)..=fields).map(|k| heap.bloblet_slot(v, k)));
    }
    let mut redirect: HashMap<u64, Value> = adapted.iter().map(|(c, f)| (c.raw(), *f)).collect();
    let cellular_kind = const { fixpt_heap::layout::kind("cellular-closure") };
    for (c, word, free) in &compiled {
        let k = heap.make_bloblet(cellular_kind, free.len() + 1, 0, true);
        heap.set_bloblet_slot(k, CLOSURE_WORD, *word);
        for (i, x) in free.iter().enumerate() {
            heap.set_bloblet_slot(k, CLOSURE_FREE0 + i, *x);
        }
        redirect.insert(c.raw(), k);
    }
    let mut alone = Heap::new();
    let mut given = HashMap::new();
    let mut placeholders = Value::NULL;
    for (v, link) in links.iter().rev() {
        let (kind, arg) = match link {
            Link::Global(name) => (0, alone.make_string(name)),
            Link::DepCell(i) => (1, Value::fixnum(*i as i64)),
            Link::DepValue(i) => (2, Value::fixnum(*i as i64)),
        };
        let p = alone.cons(Value::fixnum(kind), arg);
        given.insert(v.raw(), p);
        placeholders = alone.cons(p, placeholders);
    }
    // Native code reached, but for the closures kept as cellular ones.
    let mut native = false;
    let (copy, made) = alone.copy_graph_redirected(heap, value, |_| false, &given, &redirect);
    for (k, c) in &made {
        if given.contains_key(k) {
            continue;
        }
        native |= c.is_bloblet() && alone.code_part(*c) == Some(CodePart::Native);
    }
    if native {
        return Err("it holds native code that is not a procedure's".into());
    }
    // Each word's compiled entry let go: a stack word runs its cells again;
    // a register word is compiled again.
    let words: Vec<Value> = made.values().copied().filter(|w| w.is_bloblet() && (alone.is_cellular_word(*w) || alone.is_register_word(*w))).collect();
    for w in words {
        let entry = alone.bloblet_slot(w, WORD_ENTRY).as_fixnum();
        if alone.is_register_word(w) {
            alone.set_bloblet_slot(w, WORD_ENTRY, Value::fixnum(0));
        } else if entry >= PRIMITIVES as i64 {
            alone.set_bloblet_slot(w, WORD_ENTRY, Value::fixnum(ROUTINE_DOCOL as i64));
        }
    }
    // The closures that were native, now cellular: for the loader to make
    // native again, and no other (one of `(conv cellular)` stays so).
    let mut natives = Value::NULL;
    for to in redirect.values() {
        if let Some(c) = made.get(&to.raw()) {
            natives = alone.cons(*c, natives);
        }
    }
    let rest = alone.cons(placeholders, natives);
    let root = alone.cons(copy, rest);
    alone.push_root(root);
    Ok(fixpt_heap::image::dump(&alone))
}

/// `value`, just copied in from a `.fasl` (so all of it new), with each of
/// its closures that was native where it was made (`natives`, raw) made the
/// native closure `compile` makes of it, wherever it is reached but in
/// words (whose literals stay as they are): what the program's convention
/// made of them. One `compile` declines stays cellular.
pub fn native_procedures(heap: &mut Heap, value: Value, compile: crate::session::NativeCompiler, natives: &std::collections::HashSet<u64>) -> Value {
    let inside = |h: &Heap, v: Value| !(v.is_bloblet() && (h.is_cellular_word(v) || h.is_register_word(v) || h.code_part(v).is_some()));
    let mut made: HashMap<u64, Value> = HashMap::new();
    for &c in natives {
        if let Ok(n) = compile(heap, Value::from_raw(c)) {
            made.insert(c, n);
        }
    }
    if made.is_empty() {
        return value;
    }
    // Every reference to one made its native closure, the native closures'
    // own included (a group's calls of each other).
    let mut objects = Vec::new();
    let _ = walk(heap, value, |h, v| {
        objects.push(v);
        Ok(inside(h, v))
    });
    for n in made.values() {
        let _ = walk(heap, *n, |h, v| {
            objects.push(v);
            Ok(inside(h, v))
        });
    }
    for v in objects {
        if v.is_pair() {
            if let Some(n) = made.get(&heap.car(v).raw()) {
                heap.set_car(v, *n);
            }
            if let Some(n) = made.get(&heap.cdr(v).raw()) {
                heap.set_cdr(v, *n);
            }
        } else if inside(heap, v) && heap.obj_type(v) != Some(ObjType::Symbol) {
            let trailer = heap.bloblet_has_trailer(v) as usize;
            for k in (1 + trailer)..=heap.bloblet_head(v).fields {
                if let Some(n) = made.get(&heap.bloblet_slot(v, k).raw()) {
                    heap.set_bloblet_slot(v, k, *n);
                }
            }
        }
    }
    made.get(&value.raw()).copied().unwrap_or(value)
}

/// A `.fasl`'s image read: its heap, its value, each object of it that
/// stands for what it links to (`image`), with what, and the closures that
/// were native.
pub type Read = (Heap, Value, Vec<(Value, Link)>, Vec<Value>);

/// A `.fasl`'s image `bytes` read ([`Read`]).
pub fn read_image(bytes: &[u8]) -> Result<Read, String> {
    let heap = fixpt_heap::image::load(bytes).map_err(|e| format!("its image: {e:?}"))?;
    let root = *heap.roots_slice().first().ok_or("its image has no root")?;
    if !root.is_pair() {
        return Err("its image's root is not a pair".into());
    }
    let (value, rest) = (heap.car(root), heap.cdr(root));
    if !rest.is_pair() {
        return Err("its image's root is not a list of three".into());
    }
    let (mut l, mut n) = (heap.car(rest), heap.cdr(rest));
    let mut natives = Vec::new();
    while n.is_pair() {
        natives.push(heap.car(n));
        n = heap.cdr(n);
    }
    let mut links = Vec::new();
    while l.is_pair() {
        let p = heap.car(l);
        let (kind, arg) = (heap.car(p), heap.cdr(p));
        let link = match kind.as_fixnum() {
            0 => Link::Global(heap.string_to_rust(arg)),
            1 => Link::DepCell(arg.as_fixnum() as usize),
            _ => Link::DepValue(arg.as_fixnum() as usize),
        };
        links.push((p, link));
        l = heap.cdr(l);
    }
    Ok((heap, value, links, natives))
}

/// `s` as an FX-26 string literal.
pub(crate) fn string_literal(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

/// Whether `name` reads back as one symbol.
fn symbol_reads(name: &str) -> bool {
    !name.chars().any(|c| c.is_whitespace() || matches!(c, '(' | ')' | '"' | ';' | '\'' | '`' | ',' | '|' | '#'))
}

impl crate::check::Checker {
    /// The load of the file at `at` (`path` as written, key `key`, its text's
    /// digest `source`) read from the `.fasl` beside it, if there is one and
    /// it is fresh: the files it loads loaded first, as it loaded them, and
    /// its load the expression `(begin (load-module "dep") … (the T
    /// %fasl-value))`, `T` the type the
    /// `.fasl` says, read and parsed as the file's module would be. None if
    /// there is none; a note why not if it is stale (`fasl_notes`), as
    /// Larceny's `require` warns ("loading source in favor of stale fasl
    /// file"). What the files it loads find wrong is said as their loads'.
    pub(crate) fn fasl_load(&mut self, span: fixpt_read::Span, key: &str, path: &str, at: &Path, input: bool, source: u64) -> crate::R<Option<crate::ast::ExpId>> {
        let fasl = path_for(at);
        let Ok(bytes) = std::fs::read(&fasl) else { return Ok(None) };
        let stale = |c: &mut Self, why: &str| {
            c.fasl_notes.push(format!("`{}` is stale ({why}): `{path}` is loaded from its source", fasl.display()));
            Ok(None)
        };
        let header = match Header::read(&bytes) {
            Ok((h, _)) => h,
            Err(e) => return stale(self, &e),
        };
        let native = self.conv_default == crate::ast::Conv::Native;
        if header.build != build() {
            return stale(self, "another fixpt made it");
        }
        if header.arch != std::env::consts::ARCH {
            return stale(self, &format!("it is for {}", header.arch));
        }
        if header.native != native {
            return stale(self, if header.native { "it is for the native convention" } else { "it is for the cellular convention" });
        }
        let kind = if input { Kind::Input } else { Kind::Module };
        // A program's file's, for `,load`: nothing to say of it here.
        if header.kind == Kind::Program {
            return Ok(None);
        }
        if header.kind != kind {
            return stale(self, &format!("it is a {} file's", header.kind.word()));
        }
        if header.source != source {
            return stale(self, "its source changed");
        }
        // Each standard type it names here what it was (a program may have
        // defined one of their names again).
        for (n, t) in &header.aliases {
            let a = self.interner.intern(n);
            if self.fasl_alias_expansion(a).as_deref() != Some(t.as_str()) {
                return stale(self, &format!("the type `{n}` is not what it was"));
            }
        }
        // The files it loads, each loaded as the file loads it, from its
        // directory: from their own `.fasl`s, if fresh.
        let dir = at.parent().map(|d| d.to_path_buf());
        let outer = std::mem::replace(&mut self.base_dir, dir.clone());
        let names: crate::R<Vec<fixpt_read::Sym>> = header.deps.iter().map(|d| self.load_name(span, &d.path, d.input)).collect();
        self.base_dir = outer;
        let names = names?;
        for (d, n) in header.deps.iter().zip(&names) {
            if self.shared_files.get(n).map(|f| f.stamp) != Some(d.stamp) {
                return stale(self, &format!("`{}` changed", d.path));
            }
        }
        let mut ty = if header.made.is_empty() { format!("(the {} %fasl-value)", header.ty) } else { header.made.clone() };
        for (i, n) in names.iter().enumerate().rev() {
            let name = self.interner.name(*n).to_string();
            if !symbol_reads(&name) {
                return stale(self, &format!("`{}` has a name that does not read as a symbol", header.deps[i].path));
            }
            ty = ty.replace(&dep_name(i), &name);
        }
        let loads: String = header
            .deps
            .iter()
            .map(|d| format!("({} {}) ", if d.input { "load-input" } else { "load-module" }, string_literal(&d.path)))
            .collect();
        let text = format!("(begin {loads}{ty})");
        // Read and parsed as the file's module would be: in the standard
        // environment, its loads from its directory.
        self.files_read += 1;
        let file = fixpt_read::FileId(self.files_read + 1000);
        self.load_sites.insert(file, (span, path.to_string(), text.as_str().into()));
        let (depth, standard) = (self.dscope.len(), self.standard_dscope);
        let outer = self.hidden.replace(((0, 0), (standard, depth)));
        let outer_dir = std::mem::replace(&mut self.base_dir, dir);
        let e = self.read_module_file(file, &text).and_then(|forms| self.parse_exp(&forms[0]));
        self.base_dir = outer_dir;
        self.dscope.truncate(depth);
        self.hidden = outer;
        // A type that does not read back here: the file read as it is, its
        // number given back, so that the two parsers number files alike.
        let e = match e {
            Ok(e) => e,
            Err(e) => {
                self.files_read -= 1;
                self.load_sites.remove(&file);
                return stale(self, &format!("its type does not read back: {}", e.message));
            }
        };
        let deps = header.deps.iter().zip(names).map(|(d, n)| (d.path.clone(), d.input, n)).collect();
        let name = self.interner.intern(&format!("%shared:{key}"));
        if std::env::var_os("FIXPT_FASL_SAY").is_some() {
            self.fasl_notes.push(format!("`{path}` is read from `{}`", fasl.display()));
        }
        let kept = SharedFile { key: key.to_string(), path: at.to_path_buf(), input, source, stamp: header.stamp, deps, ty: None, fasl: Some((fasl, text)) };
        self.shared_files.insert(name, kept);
        Ok(Some(e))
    }
}

/// `s` with each `from` that stands as a symbol of its own (after `(` or a
/// space, before `)`, a space or the end) made `to`.
fn replace_symbol(s: &str, from: &str, to: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    while let Some(i) = rest.find(from) {
        let (head, tail) = (&rest[..i], &rest[i + from.len()..]);
        out.push_str(head);
        let alone = (out.is_empty() || out.ends_with(['(', ' '])) && (tail.is_empty() || tail.starts_with([')', ' ']));
        out.push_str(if alone { to } else { from });
        rest = tail;
    }
    out.push_str(rest);
    out
}

impl crate::check::Checker {
    /// For a maker's file (`maker`, its one expression: `(plambda (b …)
    /// (lambda ((m T) …) body))`, or the `lambda` alone), the expression
    /// its load `name` is checked as in its `.fasl`: `(module (define input
    /// (plambda (b …) (lambda ((m T) …) ((the (subr E () R) %fasl-effects))))))`,
    /// its parameters as the source wrote them, so that their types are
    /// made from the files they name as they would be from the source (and
    /// shared, not written out, which for a file of many such parameters is
    /// most of its type), `E` and `R` the maker's effect and result. Named
    /// as `fasl_type` names a file loaded. None if `maker` is not so.
    pub fn fasl_made(&self, name: fixpt_read::Sym, maker: &fixpt_read::Syntax) -> Option<String> {
        use crate::ast::Ty;
        let f = self.shared_files.get(&name)?;
        let Ty::Module { vals, .. } = self.arena.get(self.arena.resolve(f.ty?)).clone() else { return None };
        let [(_, mut t)] = vals[..] else { return None };
        let w = |s: &fixpt_read::Syntax| fixpt_read::write_syntax(s, &self.interner);
        let is = |s: &fixpt_read::Syntax, h: &str| s.as_symbol().is_some_and(|x| self.interner.name(x) == h);
        let mut syn = maker;
        let mut binders = None;
        if let Some([head, bs, body]) = syn.as_proper_list()
            && is(head, "plambda")
        {
            let Ty::Poly { body: inner, .. } = self.arena.get(self.arena.resolve(t)).clone() else { return None };
            binders = Some(w(bs));
            (syn, t) = (body, inner);
        }
        let [head, params, _body] = syn.as_proper_list()? else { return None };
        if !is(head, "lambda") {
            return None;
        }
        let Ty::Subr { effect, params: ptys, result, spec: None, .. } = self.arena.get(self.arena.resolve(t)).clone() else { return None };
        let names: Vec<String> = params.as_proper_list()?.iter().map(|p| Some(w(p.as_proper_list()?.first()?))).collect::<Option<_>>()?;
        if names.len() != ptys.len() {
            return None;
        }
        let mut vars = HashMap::new();
        for (i, (_, _, d)) in f.deps.iter().enumerate() {
            if let Some(g) = self.global_type(*d)
                && let Ty::Module { abs, .. } = self.arena.get(self.arena.resolve(g))
            {
                for (n, v) in abs {
                    vars.insert(*v, format!("(select {} {})", dep_name(i), self.interner.name(*n)));
                }
            }
        }
        // Each description of a parameter's module by its select, as the
        // source names it, not written out at each of its uses.
        let mut tys = HashMap::new();
        for (p, n) in ptys.iter().zip(&names) {
            if let Ty::Module { descs, .. } = self.arena.get(self.arena.resolve(*p)) {
                for (d, x) in descs {
                    let x = self.arena.resolve(*x);
                    if self.abbreviates(x) {
                        tys.entry(x).or_insert_with(|| format!("(select {n} {})", self.interner.name(*d)));
                    }
                }
            }
        }
        *self.print_for_fasl.borrow_mut() = Some(vars);
        *self.print_params.borrow_mut() = Some(names);
        *self.print_tys.borrow_mut() = tys;
        let shown = format!("(subr {} () {})", self.show_effect(&effect), self.show_ty(result));
        self.print_tys.borrow_mut().clear();
        *self.print_params.borrow_mut() = None;
        *self.print_for_fasl.borrow_mut() = None;
        let lambda = format!("(lambda {} ((the {shown} %fasl-effects)))", w(params));
        let made = match binders {
            Some(bs) => format!("(plambda {bs} {lambda})"),
            None => lambda,
        };
        let mut text = format!("(module (define input {made}))");
        for (i, (_, _, d)) in f.deps.iter().enumerate() {
            text = replace_symbol(&text, self.interner.name(*d), &dep_name(i));
        }
        (!text.contains('\n')).then_some(text)
    }

    /// The type file `name`'s load (its hidden global) is checked at, as a
    /// `.fasl` keeps it, to be read where it is loaded: no name in scope
    /// used for a type; each abstract type of a file it loads a `select` of
    /// that load, and that load's hidden global named by its place, each
    /// `%fasl-dep:i` ([`dep_name`]), which the loader names as it names it.
    pub fn fasl_type(&self, name: fixpt_read::Sym) -> Result<String, String> {
        use crate::ast::Ty;
        let f = self.shared_files.get(&name).ok_or("it was not loaded")?;
        let ty = f.ty.ok_or("its load was not checked")?;
        let mut vars = HashMap::new();
        for (i, (_, _, d)) in f.deps.iter().enumerate() {
            if let Some(t) = self.global_type(*d)
                && let Ty::Module { abs, .. } = self.arena.get(self.arena.resolve(t))
            {
                for (n, v) in abs {
                    vars.insert(*v, format!("(select {} {})", dep_name(i), self.interner.name(*n)));
                }
            }
        }
        *self.print_for_fasl.borrow_mut() = Some(vars);
        let mut shown = self.show_ty(ty);
        *self.print_for_fasl.borrow_mut() = None;
        for (i, (_, _, d)) in f.deps.iter().enumerate() {
            shown = replace_symbol(&shown, self.interner.name(*d), &dep_name(i));
        }
        if shown.contains('\n') {
            return Err("its type prints on more than one line".into());
        }
        Ok(shown)
    }
}

impl crate::check::Checker {
    /// Type `t` as a program's `.fasl` keeps it, to be read back where the
    /// program is loaded: no name a program defines used for a type but a
    /// module's, each abstract type of a module a global holds `(select
    /// global t)`. Also how the types of the globals its code uses are
    /// compared (`Fx26Session::program_fasl`).
    pub fn fasl_program_type(&self, t: crate::ast::TyId) -> Result<String, String> {
        use crate::ast::Ty;
        let mut vars = HashMap::new();
        for n in self.value_names() {
            if let Some(g) = self.global_type(n)
                && let Ty::Module { abs, .. } = self.arena.get(self.arena.resolve(g))
            {
                for (a, v) in abs {
                    vars.entry(*v).or_insert_with(|| format!("(select {} {})", self.interner.name(n), self.interner.name(*a)));
                }
            }
        }
        *self.print_for_fasl.borrow_mut() = Some(vars);
        let shown = self.show_ty(t);
        *self.print_for_fasl.borrow_mut() = None;
        if shown.contains('\n') {
            return Err("its type prints on more than one line".into());
        }
        Ok(shown)
    }

    /// The globals `name`'s latest definition uses (`defs`): its code's.
    pub fn uses_of(&self, name: fixpt_read::Sym) -> Vec<fixpt_read::Sym> {
        self.defs.iter().rev().find(|d| d.names.contains(&name)).map(|d| d.uses.clone()).unwrap_or_default()
    }

    /// `name`, just defined from a program's `.fasl` as a declaration, made
    /// what its definition `form` would have made of it for a redefinition
    /// (`defs`): that form, which is checked again if a global it uses is
    /// redefined, and the globals it uses.
    pub fn fasl_defined(&mut self, name: fixpt_read::Sym, form: std::rc::Rc<fixpt_read::Syntax>, uses: Vec<fixpt_read::Sym>) {
        if let Some(d) = self.defs.iter_mut().rev().find(|d| d.names.contains(&name)) {
            d.form = form;
            d.uses = uses;
        }
    }
}

impl crate::check::Checker {
    /// Type `text`, read and printed back as a program's `.fasl` prints
    /// one (`fasl_program_type`): what it reads as here, or none if it does
    /// not read. A type kept must read back as itself.
    pub fn fasl_reads_back(&mut self, text: &str) -> Option<String> {
        let t = self.fasl_parse_type(text)?;
        self.fasl_program_type(t).ok()
    }

    /// Type `text` read here, if it reads.
    pub fn fasl_parse_type(&mut self, text: &str) -> Option<crate::ast::TyId> {
        let forms = self.read_module_file(fixpt_read::FileId(0), text).ok()?;
        let depth = self.dscope.len();
        let t = self.parse_type(forms.first()?);
        self.dscope.truncate(depth);
        t.ok()
    }
}

/// The `lambda` a `define-rec`'s declaration of a procedure of type `ty`
/// (printed) has it by: `(lambda (x …) (the R %fasl-value))`, its result
/// `R`, its parameters named as `ty` names them where a type after selects
/// from one (`(%p.1 : T)`), under a `plambda` of each `poly`'s binders.
/// None if `ty` is no procedure's of a result alone (a specification's
/// clauses after it, say).
pub fn fasl_lambda_at(ty: &fixpt_read::Syntax, interner: &fixpt_read::Interner) -> Option<String> {
    let w = |s: &fixpt_read::Syntax| fixpt_read::write_syntax(s, interner);
    let items = ty.as_proper_list()?;
    let head = interner.name(items.first()?.as_symbol()?);
    match (head, items) {
        ("poly", [_, binders, body]) => Some(format!("(plambda {} {})", w(binders), fasl_lambda_at(body, interner)?)),
        ("subr", [_, _, params, result]) | ("subr", [_, _, _, params, result]) => {
            let names: Vec<String> = params
                .as_proper_list()?
                .iter()
                .enumerate()
                .map(|(i, p)| match p.as_proper_list() {
                    Some([n, colon, _]) if colon.as_symbol().is_some_and(|c| interner.name(c) == ":") => w(n),
                    _ => format!("%a{}", i + 1),
                })
                .collect();
            Some(format!("(lambda ({}) (the {} %fasl-value))", names.join(" "), w(result)))
        }
        _ => None,
    }
}

/// The expression a declaration of a value of type `ty` (printed) is made
/// to have it: `(the T %fasl-value)`, under a `plambda` of each `poly`'s
/// binders, which `the` takes apart.
pub fn fasl_value_at(ty: &fixpt_read::Syntax, interner: &fixpt_read::Interner) -> String {
    let written = fixpt_read::write_syntax(ty, interner);
    match ty.as_proper_list() {
        Some([head, binders, body]) if head.as_symbol().is_some_and(|h| interner.name(h) == "poly") => {
            format!("(plambda {} {})", fixpt_read::write_syntax(binders, interner), fasl_value_at(body, interner))
        }
        _ => format!("(the {written} %fasl-value)"),
    }
}

impl crate::check::Checker {
    /// The type abbreviations a program's `.fasl` may name a type by, for
    /// its file's `forms`: those the file defines once (declared ahead
    /// where it is loaded, as here) and the standard ones.
    pub fn fasl_allowed_aliases(&self, forms: &[fixpt_read::Syntax]) -> Vec<fixpt_read::Sym> {
        let again: Vec<fixpt_read::Sym> = self.types_defined_again(forms).into_iter().map(|(n, _)| n).collect();
        let mut out: Vec<fixpt_read::Sym> = self.type_abbreviations(forms).into_iter().map(|(n, _)| n).filter(|n| !again.contains(n)).collect();
        for n in self.fasl_standard_aliases() {
            if !out.contains(&n) {
                out.push(n);
            }
        }
        out
    }

    /// The standard type abbreviations: what a module file's `.fasl` may
    /// name a type by, as the file sees them alone. So `datum`, written out
    /// at each use, is not a new recursive type each time where it is read.
    pub fn fasl_standard_aliases(&self) -> Vec<fixpt_read::Sym> {
        let mut out = Vec::new();
        for (n, d) in &self.dscope[..self.standard_dscope.min(self.dscope.len())] {
            if matches!(d, crate::parse::DScope::Rec(_)) && !out.contains(n) {
                out.push(*n);
            }
        }
        out
    }

    /// While types are printed for a program's `.fasl`: `allowed` may name
    /// them ([`fasl_allowed_aliases`](Self::fasl_allowed_aliases)).
    pub fn fasl_aliases_begin(&self, allowed: Vec<fixpt_read::Sym>) {
        *self.print_aliases.borrow_mut() = Some((allowed, Vec::new()));
    }

    /// Printing so done: the abbreviations that named a type.
    pub fn fasl_aliases_end(&self) -> Vec<fixpt_read::Sym> {
        self.print_aliases.borrow_mut().take().map(|(_, used)| used).unwrap_or_default()
    }

    /// What abbreviation `n` is here, written out with no name for any
    /// part: what a `.fasl` that names a type by it keeps, to compare.
    pub fn fasl_alias_expansion(&self, n: fixpt_read::Sym) -> Option<String> {
        let t = self.type_named(n)?;
        let kept = self.print_aliases.borrow_mut().take();
        let shown = self.fasl_program_type(t).ok();
        *self.print_aliases.borrow_mut() = kept;
        shown
    }
}

/// The symbols of type `text`, as printed: its words between parentheses
/// and spaces.
pub fn symbols_in(text: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for w in text.split(['(', ')', ' ']).filter(|w| !w.is_empty()) {
        if !out.iter().any(|o| o == w) {
            out.push(w.to_string());
        }
    }
    out
}
