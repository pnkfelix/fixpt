//! FX-26's `syn` (`eager-reader-types.fx`) in the heap: what the Rust
//! reader builds as it reads (`fixpt_read::Build`), what the Rust expander
//! takes and makes, and what the front end written in FX-26 parses, handed
//! to it as it is, with no text between (`docs/research/heap-syntax.md`).
//! Laid out as FX-26 makes it: a frozen sum whose tag is `atom`, `lst`,
//! `dotted` or `vec` and whose payload is a frozen product of the variant's
//! fields; each piece's plain datum beside it, made once, from its parts';
//! its place, characters past its file's base; and its expansion, the use of
//! a macro that made it (`fixpt_read::expansion`), 0 for what was read.
//!
//! Raw values: the heap collects only at safepoints, never in an
//! allocation, so a reading, an expansion and a parse hold them ([`Rd`],
//! [`Mk`]); what lasts past code that runs is held by a handle.

use fixpt_heap::layout::kind;
use fixpt_heap::{Heap, ObjType, Value};
use fixpt_read::{Build, Datum, FileId, Interner, Num, Place, Span, Sym};
use std::sync::Arc;

/// A piece of `syn`, in the heap; and, in a build with debug assertions,
/// the heap's collections when it was taken, so that one held past a
/// collection is caught where it is used, not read as what moved there.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Syn(pub Value, Era);

/// How many collections the heap had made when a [`Syn`] was taken: a
/// build with debug assertions's, nothing in another.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Era {
    #[cfg(debug_assertions)]
    n: u64,
}

impl Era {
    #[inline(always)]
    fn of(_heap: &Heap) -> Era {
        Era {
            #[cfg(debug_assertions)]
            n: _heap.collections(),
        }
    }
}

impl Syn {
    /// `v`, a piece of `syn` in `heap`, taken now.
    #[inline(always)]
    pub fn of(heap: &Heap, v: Value) -> Syn {
        Syn(v, Era::of(heap))
    }

    /// Its value, which `heap` holds still: a panic, in a build with debug
    /// assertions, if a collection came since it was taken.
    #[inline(always)]
    fn value(self, _heap: &Heap) -> Value {
        #[cfg(debug_assertions)]
        assert_eq!(self.1.n, _heap.collections(), "a piece of syntax held past a collection: hold it by a handle (`Kept`)");
        self.0
    }
}

/// Where a piece of `syn` is: characters past its file's base, start and end,
/// and the use of a macro that made it, 0 if none did.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct At {
    pub start: i64,
    pub end: i64,
    pub expansion: u32,
}

impl From<At> for Span {
    fn from(at: At) -> Span {
        span_of(at)
    }
}

impl From<Span> for At {
    fn from(s: Span) -> At {
        at_of(s)
    }
}

impl At {
    /// Where it is, as the checker says it ([`span_of`]).
    pub fn span(self) -> Span {
        span_of(self)
    }
    /// This place, of what a use of a macro, `expansion`, made.
    pub fn in_expansion(self, expansion: u32) -> At {
        At { expansion, ..self }
    }
    /// This place's start, of no width: a piece made where this is.
    pub fn synthetic(self) -> At {
        At { end: self.start, ..self }
    }
}

/// A piece of `syn`, looked at: its datum, its parts as `syn`.
#[derive(Clone, Debug, PartialEq)]
pub enum V {
    Bool(bool),
    Number(Num),
    Char(char),
    Str(String),
    Symbol(Sym),
    Keyword(Sym),
    Nil,
    List { items: Vec<Syn>, tail: Option<Syn> },
    Vector(Vec<Syn>),
    Bytevector(Vec<u8>),
}

/// The heap's symbols as the checker's: by each symbol's global slot,
/// which is its own and never moves. Filled where syntax is given a
/// symbol (the reader's builder, [`Mk`]), so that every symbol in syntax is
/// here: one missing is a symbol made past them, which [`Rd::sym`] says.
#[derive(Default, Clone)]
pub struct SymTable {
    /// By global slot, which are dense: no hashing.
    by_slot: Vec<Option<Sym>>,
    /// `syn`'s four tags, interned, and the collections when they were:
    /// good until the next.
    tags: Option<(u64, [Value; 4])>,
    /// Each symbol given to syntax, the heap's, by its number, and the
    /// collections when they were: good until the next.
    by_sym: (u64, Vec<Option<Value>>),
    /// The slots of the forms held in this heap ([`Form`]): those whose
    /// last copy dropped, let go at the next lending, and those let go.
    forms: std::rc::Rc<FormSlots>,
}

/// The slots of a heap's forms ([`SymTable::forms`]).
#[derive(Default)]
struct FormSlots {
    dropped: std::cell::RefCell<Vec<usize>>,
    free: std::cell::RefCell<Vec<usize>>,
}

impl SymTable {
    /// The heap's symbol of `s`, `interner`'s: interned, and noted.
    pub fn heap_symbol(&mut self, heap: &mut Heap, interner: &Interner, s: Sym) -> Value {
        let now = heap.collections();
        if self.by_sym.0 != now {
            self.by_sym = (now, Vec::new());
        }
        if let Some(Some(v)) = self.by_sym.1.get(s.0 as usize) {
            return *v;
        }
        let name = interner.name(s);
        debug_assert_eq!(interner.get(name), Some(s), "an uninterned symbol in syntax: `{name}`");
        let v = heap.intern(name);
        let slot = heap.symbol_global_slot(v);
        if self.by_slot.len() <= slot {
            self.by_slot.resize(slot + 1, None);
        }
        self.by_slot[slot] = Some(s);
        let k = s.0 as usize;
        if self.by_sym.1.len() <= k {
            self.by_sym.1.resize(k + 1, None);
        }
        self.by_sym.1[k] = Some(v);
        v
    }
}

// ------------------------------------------------------------------ places

thread_local! {
    /// The texts places are in that are not all ASCII, by their bases: the
    /// program's, a module file's, a text read on the side
    /// (`docs/research/heap-syntax.md`). An ASCII text's characters are its
    /// bytes, so it needs none.
    static TEXTS: std::cell::RefCell<Vec<Text>> = const { std::cell::RefCell::new(Vec::new()) };
    /// The side texts read so far ([`side_base`]).
    static SIDES: std::cell::Cell<i64> = const { std::cell::Cell::new(0) };
}

/// A text places are in: its base, and the byte where each of its
/// characters starts, and its end.
struct Text {
    base: i64,
    starts: Vec<u32>,
}

/// The base of file `file`'s places: the program's 0; a module file's, its
/// number past 1000 times a billion (`syn.rs`'s `LOAD_BASE_STEP`).
pub fn base_of(file: FileId) -> i64 {
    if file.0 > 1000 { (file.0 as i64 - 1000) * 1_000_000_000 } else { 0 }
}

/// How far apart side texts' bases are, below every file's and below
/// [`UNPLACED`]: a side text is under 4 GiB, as a `Span` says.
const SIDE_STEP: i64 = 1 << 32;
/// The base of what is placed nowhere a message says ([`read_syn_unplaced`]).
const UNPLACED: i64 = -1_000_000_000;

/// A base no text has had: a side text's, read apart from the program,
/// whose spans are file 0's, in it.
fn side_base() -> i64 {
    SIDES.with(|n| {
        n.set(n.get() + 1);
        -n.get() * SIDE_STEP
    })
}

/// Text `text`, of file `file`, the one its places are in from now on.
pub fn note_text(file: FileId, text: Arc<str>) {
    note_at(base_of(file), &text);
}

/// Text `text`, the one the places past `base` are in.
fn note_at(base: i64, text: &str) {
    TEXTS.with(|t| {
        let mut t = t.borrow_mut();
        t.retain(|x| x.base != base);
        if !text.is_ascii() {
            let starts = text.char_indices().map(|(b, _)| b as u32).chain([text.len() as u32]).collect();
            t.push(Text { base, starts });
        }
    });
}

/// The base of the text place `p` is in ([`file_base_at`]); the unplaced's,
/// if none.
pub fn base_at(p: i64) -> i64 {
    file_base_at(p).map_or(UNPLACED, |(_, b)| b)
}

/// The file and base of place `p`: a module file's past a billion; file
/// 0's, the program's, below; a side text's, below that; and else the
/// unplaced, which are file 0's start.
fn file_base_at(p: i64) -> Option<(FileId, i64)> {
    if p >= 1_000_000_000 {
        let k = p / 1_000_000_000;
        Some((FileId(1000 + k as u32), k * 1_000_000_000))
    } else if p >= 0 {
        Some((FileId(0), 0))
    } else if p < -SIDE_STEP {
        Some((FileId(0), p.div_euclid(SIDE_STEP) * SIDE_STEP))
    } else {
        None
    }
}

/// Place `at`'s span: its file, by its base, and its bytes there. A place
/// is a character past its file's base, as FX-26's reader counts; a span,
/// bytes, as Rust's does: the same in an ASCII text, else by the text's
/// table ([`note_text`]). [`at_of`]'s inverse.
pub fn span_of(at: At) -> Span {
    let Some((file, base)) = file_base_at(at.start) else {
        return Span { file: FileId(0), start: 0, end: 0, expansion: at.expansion };
    };
    let (start, end) = TEXTS.with(|t| {
        let t = t.borrow();
        let byte = |p: i64| {
            let c = (p - base).clamp(0, u32::MAX as i64);
            match t.iter().find(|x| x.base == base) {
                Some(x) => x.starts[(c as usize).min(x.starts.len() - 1)],
                None => c as u32,
            }
        };
        (byte(at.start), byte(at.end.max(at.start)))
    });
    Span { file, start, end, expansion: at.expansion }
}

// ------------------------------------------------------------------ reading

/// What syntax is read with: the heap it is in, and the checker's names.
#[derive(Clone, Copy)]
pub struct Rd<'a> {
    pub heap: &'a Heap,
    pub syms: &'a SymTable,
}

impl<'a> Rd<'a> {
    /// Which of `syn`'s variants `s` is, and its payload: by its tag, a
    /// word's look, where the tags are known now (`SymTable::tags`), and
    /// else by its payload's length, whose header is found by looking past
    /// its fields.
    #[inline(always)]
    fn variant(self, s: Syn) -> (Variant, Value) {
        let v = s.value(self.heap);
        let p = self.heap.sum_payload(v);
        if let Some((n, tags)) = self.syms.tags
            && n == self.heap.collections()
        {
            let t = self.heap.sum_tag(v);
            let k = if t == tags[ATOM] {
                Variant::Atom
            } else if t == tags[LST] {
                Variant::Lst
            } else if t == tags[DOTTED] {
                Variant::Dotted
            } else {
                Variant::Vec
            };
            return (k, p);
        }
        let k = match self.heap.bloblet_len(p) {
            4 => Variant::Atom,
            6 => Variant::Dotted,
            _ if self.heap.is_a(self.heap.product_field(p, 2), ObjType::Vector) => Variant::Vec,
            _ => Variant::Lst,
        };
        (k, p)
    }

    /// `s`'s plain datum.
    #[inline(always)]
    pub fn datum(self, s: Syn) -> Value {
        let (k, p) = self.variant(s);
        self.heap.product_field(p, k.len() - 3)
    }

    /// Where `s` is.
    #[inline(always)]
    pub fn at(self, s: Syn) -> At {
        let (k, p) = self.variant(s);
        let n = k.len();
        At {
            start: self.heap.product_field(p, n - 2).as_fixnum(),
            end: self.heap.product_field(p, n - 1).as_fixnum(),
            expansion: self.heap.product_field(p, n).as_fixnum() as u32,
        }
    }

    /// Where `s` is, as the checker says it ([`span_of`]).
    #[inline(always)]
    pub fn span(self, s: Syn) -> Span {
        span_of(self.at(s))
    }

    /// Symbol `v`, the checker's.
    #[inline(always)]
    pub fn sym_of(self, v: Value) -> Sym {
        let slot = self.heap.symbol_global_slot(v);
        match self.syms.by_slot.get(slot).copied().flatten() {
            Some(s) => s,
            None => panic!("a symbol in syntax that no builder made: `{}`", self.heap.symbol_name(v)),
        }
    }

    /// Whether `s` is an atom, and its datum if so.
    #[inline(always)]
    fn atom(self, s: Syn) -> Option<Value> {
        let (k, p) = self.variant(s);
        (k == Variant::Atom).then(|| self.heap.product_field(p, 1))
    }

    /// `s`'s symbol, if it is one.
    #[inline(always)]
    pub fn sym(self, s: Syn) -> Option<Sym> {
        let d = self.atom(s)?;
        self.heap.is_a(d, ObjType::Symbol).then(|| self.sym_of(d))
    }

    /// A proper list's items (none for `()`), or none.
    pub fn list(self, s: Syn) -> Option<Vec<Syn>> {
        match self.view_shallow(s) {
            Shallow::List(items, None) => Some(items),
            _ => None,
        }
    }

    /// Whether `s` is `()`.
    #[inline(always)]
    pub fn is_nil(self, s: Syn) -> bool {
        matches!(self.view_shallow(s), Shallow::List(items, None) if items.is_empty())
    }

    fn items_of(self, l: Value) -> Vec<Syn> {
        let mut out = Vec::new();
        let mut x = l;
        while x.is_pair() {
            out.push(Syn::of(self.heap, self.heap.car(x)));
            x = self.heap.cdr(x);
        }
        out
    }

    fn view_shallow(self, s: Syn) -> Shallow {
        let (k, p) = self.variant(s);
        match k {
            Variant::Atom => Shallow::Atom,
            Variant::Dotted => Shallow::List(self.items_of(self.heap.product_field(p, 1)), Some(Syn::of(self.heap, self.heap.product_field(p, 2)))),
            Variant::Vec => Shallow::Vector(self.items_of(self.heap.product_field(p, 1))),
            Variant::Lst => Shallow::List(self.items_of(self.heap.product_field(p, 1)), None),
        }
    }

    /// `s`, looked at.
    pub fn view(self, s: Syn) -> V {
        match self.view_shallow(s) {
            Shallow::List(items, None) if items.is_empty() => V::Nil,
            Shallow::List(items, tail) => V::List { items, tail },
            Shallow::Vector(items) => V::Vector(items),
            Shallow::Atom => {
                let h = self.heap;
                let d = self.atom(s).expect("an atom");
                if d == Value::TRUE || d == Value::FALSE {
                    V::Bool(d == Value::TRUE)
                } else if d.is_char() {
                    V::Char(d.as_char())
                } else if d.is_fixnum() {
                    V::Number(Num::Int(d.as_fixnum()))
                } else if h.is_a(d, ObjType::Symbol) {
                    V::Symbol(self.sym_of(d))
                } else if h.is_a(d, ObjType::String) {
                    V::Str(h.string_to_rust(d))
                } else if h.is_a(d, ObjType::Bytevector) {
                    V::Bytevector((0..h.bytevector_len(d)).map(|i| h.bytevector_ref(d, i)).collect())
                } else if h.is_a(d, ObjType::Flonum) {
                    V::Number(Num::Real(h.flonum_value(d)))
                } else if h.is_a(d, ObjType::Bignum) {
                    // As the Rust reader has an integer: a word's if it
                    // fits one, a fixnum's or not.
                    let w = fixpt_runtime::write_value(h, d);
                    if let Ok(n) = w.parse::<i64>() {
                        return V::Number(Num::Int(n));
                    }
                    let (negative, digits) = match w.strip_prefix('-') {
                        Some(x) => (true, x.to_string()),
                        None => (false, w.clone()),
                    };
                    V::Number(Num::Big { negative, digits, radix: 10 })
                } else if h.is_keyword(d) {
                    V::Keyword(self.sym_of(h.keyword_symbol(d)))
                } else {
                    unreachable!("an atom FX-26 does not read: {}", fixpt_runtime::write_value(h, d))
                }
            }
        }
    }
}

impl Rd<'_> {
    /// What `s` is, looked at no deeper ([`Shape`]).
    #[inline(always)]
    pub fn shape(self, s: Syn) -> Shape {
        let (k, p) = self.variant(s);
        match k {
            Variant::Atom => {
                let d = self.heap.product_field(p, 1);
                if self.heap.is_a(d, ObjType::Symbol) {
                    Shape::Symbol(self.sym_of(d))
                } else if self.heap.is_keyword(d) {
                    Shape::Keyword(self.sym_of(self.heap.keyword_symbol(d)))
                } else {
                    Shape::Atom
                }
            }
            Variant::Dotted => Shape::Dotted,
            Variant::Vec => Shape::Vector,
            Variant::Lst if self.heap.product_field(p, 1).is_pair() => Shape::List,
            Variant::Lst => Shape::Nil,
        }
    }

    /// A list's first part, proper or dotted, if it has one.
    #[inline(always)]
    pub fn head(self, s: Syn) -> Option<Syn> {
        let (k, p) = self.variant(s);
        if matches!(k, Variant::Atom | Variant::Vec) {
            return None;
        }
        let l = self.heap.product_field(p, 1);
        l.is_pair().then(|| Syn::of(self.heap, self.heap.car(l)))
    }

    /// A list's parts, proper or dotted (`()`'s none), and its tail, read
    /// where they are ([`Items`]).
    #[inline(always)]
    pub fn parts(self, s: Syn) -> Option<(Items, Option<Syn>)> {
        let (k, p) = self.variant(s);
        let items = Items { rest: Syn::of(self.heap, self.heap.product_field(p, 1)) };
        match k {
            Variant::Atom | Variant::Vec => None,
            Variant::Dotted => Some((items, Some(Syn::of(self.heap, self.heap.product_field(p, 2))))),
            Variant::Lst => Some((items, None)),
        }
    }
}

/// What a piece of syntax is, looked at no deeper: a name's, a keyword's,
/// or the kind of list or atom it is. Made with nothing allocated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    Symbol(Sym),
    Keyword(Sym),
    /// `()`.
    Nil,
    /// A proper list of one part or more.
    List,
    /// A dotted list.
    Dotted,
    Vector,
    /// Any other atom.
    Atom,
}

impl Shape {
    /// Its symbol, if it is a name's.
    pub fn sym(self) -> Option<Sym> {
        match self {
            Shape::Symbol(s) => Some(s),
            _ => None,
        }
    }
}

/// A list's parts, each read as it is reached, from the conses the list
/// holds them in: none copied out. Within the lending they are read in,
/// as any syntax (the heap does not collect meanwhile).
#[derive(Clone, Copy)]
pub struct Items {
    /// The conses left, held as syntax is, so that one held past a
    /// collection is caught ([`Syn::value`]).
    rest: Syn,
}

impl Iterator for Items {
    type Item = Syn;
    #[inline(always)]
    fn next(&mut self) -> Option<Syn> {
        heap(|h| {
            let rest = self.rest.value(h);
            if !rest.is_pair() {
                return None;
            }
            self.rest = Syn::of(h, h.cdr(rest));
            Some(Syn::of(h, h.car(rest)))
        })
    }
}

/// One of `syn`'s variants ([`Rd::variant`]).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Variant {
    Atom,
    Lst,
    Dotted,
    Vec,
}

impl Variant {
    /// Its payload's length: its parts, its datum, and its place's three.
    #[inline(always)]
    fn len(self) -> usize {
        match self {
            Variant::Atom => 4,
            Variant::Lst | Variant::Vec => 5,
            Variant::Dotted => 6,
        }
    }
}

enum Shallow {
    Atom,
    List(Vec<Syn>, Option<Syn>),
    Vector(Vec<Syn>),
}

/// `syn` `s`'s plain datum: in every variant, the field before its place
/// and its expansion, the last three.
pub fn datum_of(heap: &Heap, s: Value) -> Value {
    let p = heap.sum_payload(s);
    heap.product_field(p, heap.bloblet_len(p) - 3)
}

// ----------------------------------------------------------------- building

/// What syntax is made with: the heap, and the checker's names (which a
/// symbol made is said by).
pub struct Mk<'a> {
    pub heap: &'a mut Heap,
    pub interner: Option<&'a Interner>,
    pub syms: &'a mut SymTable,
    tags: [Value; 4],
}

impl<'a> Mk<'a> {
    pub fn new(heap: &'a mut Heap, interner: &'a Interner, syms: &'a mut SymTable) -> Mk<'a> {
        Mk::with(heap, Some(interner), syms)
    }

    /// Making, with no names: of lists and vectors, and atoms not symbols.
    fn with(heap: &'a mut Heap, interner: Option<&'a Interner>, syms: &'a mut SymTable) -> Mk<'a> {
        let now = heap.collections();
        let tags = match syms.tags {
            Some((n, tags)) if n == now => tags,
            _ => {
                let tags = ["atom", "lst", "dotted", "vec"].map(|t| heap.intern(t));
                syms.tags = Some((now, tags));
                tags
            }
        };
        Mk { heap, interner, syms, tags }
    }

    fn names(&self) -> &'a Interner {
        self.interner.expect("a symbol made with the names said")
    }

    /// Reading, now.
    pub fn rd(&self) -> Rd<'_> {
        Rd { heap: self.heap, syms: self.syms }
    }

    fn syn(&mut self, tag: usize, at: At, fields: &[Value]) -> Syn {
        // Its parts and datum, at most three, then its place's three.
        let mut all = [Value::NULL; 6];
        let n = fields.len();
        all[..n].copy_from_slice(fields);
        all[n..n + 3].copy_from_slice(&[Value::fixnum(at.start), Value::fixnum(at.end), Value::fixnum(at.expansion as i64)]);
        let payload = self.heap.make_frozen(const { kind("product") }, &all[..n + 3]);
        let s = self.heap.make_frozen(const { kind("sum") }, &[self.tags[tag], payload]);
        Syn::of(self.heap, s)
    }

    /// An atom of `v`, at `at`.
    pub fn atom(&mut self, at: At, v: &V) -> Syn {
        let d = match v {
            V::Bool(b) => Value::boolean(*b),
            V::Char(c) => Value::char(*c),
            V::Number(n) => fixpt_runtime::num_in_heap(self.heap, n),
            V::Str(s) => self.heap.make_string(s),
            V::Symbol(s) => self.syms.heap_symbol(self.heap, self.names(), *s),
            V::Keyword(s) => {
                let sym = self.syms.heap_symbol(self.heap, self.names(), *s);
                self.heap.make_keyword(sym)
            }
            V::Bytevector(b) => self.heap.make_bytevector(b),
            V::Nil => return self.list(at, &[], None),
            V::List { items, tail } => return self.list(at, items, *tail),
            V::Vector(items) => return self.vector(at, items),
        };
        self.syn(ATOM, at, &[d])
    }

    /// Symbol `s`, at `at`.
    pub fn sym(&mut self, at: At, s: Sym) -> Syn {
        self.atom(at, &V::Symbol(s))
    }

    /// A list of `items`, and `tail` if dotted, at `at`: `()` if neither.
    pub fn list(&mut self, at: At, items: &[Syn], tail: Option<Syn>) -> Syn {
        let mut d = match tail {
            Some(t) => self.rd().datum(t),
            None => Value::NULL,
        };
        for i in items.iter().rev() {
            let x = self.rd().datum(*i);
            d = self.heap.cons(x, d);
        }
        let mut l = Value::NULL;
        for i in items.iter().rev() {
            l = self.heap.cons(i.value(self.heap), l);
        }
        match tail {
            Some(t) => {
                let t = t.value(self.heap);
                self.syn(DOTTED, at, &[l, t, d])
            }
            None => self.syn(LST, at, &[l, d]),
        }
    }

    /// A vector of `items`, at `at`.
    pub fn vector(&mut self, at: At, items: &[Syn]) -> Syn {
        let ds: Vec<Value> = items.iter().map(|i| self.rd().datum(*i)).collect();
        let d = self.heap.vector_from(&ds);
        let mut l = Value::NULL;
        for i in items.iter().rev() {
            l = self.heap.cons(i.value(self.heap), l);
        }
        self.syn(VEC, at, &[l, d])
    }

    /// `s`, at `at`: the same parts, placed anew (shared, not copied).
    pub fn at(&mut self, s: Syn, at: At) -> Syn {
        let v = s.value(self.heap);
        let tag = self.heap.sum_tag(v);
        let p = self.heap.sum_payload(v);
        let n = self.heap.bloblet_len(p);
        let mut all: Vec<Value> = (1..=n - 3).map(|k| self.heap.product_field(p, k)).collect();
        all.extend([Value::fixnum(at.start), Value::fixnum(at.end), Value::fixnum(at.expansion as i64)]);
        let payload = self.heap.make_frozen(const { kind("product") }, &all);
        let s = self.heap.make_frozen(const { kind("sum") }, &[tag, payload]);
        Syn::of(self.heap, s)
    }

    /// `s` and each part of it, their places moved by `by` (a file's base
    /// for another's), each made again but for its datum, which holds no
    /// place and is shared; `placed` of each expansion met.
    pub fn moved(&mut self, s: Syn, by: i64, placed: &mut impl FnMut(u32)) -> Syn {
        let (k, p) = self.rd().variant(s);
        let v = s.value(self.heap);
        let tag = self.heap.sum_tag(v);
        let n = k.len();
        let field = |h: &Heap, i: usize| h.product_field(p, i);
        let at = At {
            start: field(self.heap, n - 2).as_fixnum() + by,
            end: field(self.heap, n - 1).as_fixnum() + by,
            expansion: field(self.heap, n).as_fixnum() as u32,
        };
        if at.expansion != 0 {
            placed(at.expansion);
        }
        let mut all = [Value::NULL; 6];
        match k {
            Variant::Atom => all[0] = field(self.heap, 1),
            Variant::Lst | Variant::Vec | Variant::Dotted => {
                // Its parts moved, in order, then their list.
                let mut parts = Vec::new();
                let mut x = field(self.heap, 1);
                while x.is_pair() {
                    parts.push(Syn::of(self.heap, self.heap.car(x)));
                    x = self.heap.cdr(x);
                }
                let moved: Vec<Value> = parts.into_iter().map(|i| self.moved(i, by, placed).value(self.heap)).collect();
                let l = moved.iter().rev().fold(Value::NULL, |l, &i| self.heap.cons(i, l));
                all[0] = l;
                if k == Variant::Dotted {
                    let t = Syn::of(self.heap, field(self.heap, 2));
                    all[1] = self.moved(t, by, placed).value(self.heap);
                }
            }
        }
        // The datum, and then the place (fields are counted from 1).
        all[n - 4] = field(self.heap, n - 3);
        all[n - 3..n].copy_from_slice(&[Value::fixnum(at.start), Value::fixnum(at.end), Value::fixnum(at.expansion as i64)]);
        let payload = self.heap.make_frozen(const { kind("product") }, &all[..n]);
        let s = self.heap.make_frozen(const { kind("sum") }, &[tag, payload]);
        Syn::of(self.heap, s)
    }

    /// `s`, each part placed at `place` of where it is: a part whose place
    /// and parts are all as they were is itself, shared, not made again
    /// (TODO §241).
    pub fn replaced(&mut self, s: Syn, place: &mut impl FnMut(&mut Heap, At) -> At) -> Syn {
        let (k, p) = self.rd().variant(s);
        let v = s.value(self.heap);
        let n = k.len();
        let field = |h: &Heap, i: usize| h.product_field(p, i);
        let was = At {
            start: field(self.heap, n - 2).as_fixnum(),
            end: field(self.heap, n - 1).as_fixnum(),
            expansion: field(self.heap, n).as_fixnum() as u32,
        };
        let at = place(self.heap, was);
        let mut all = [Value::NULL; 6];
        let mut same = at == was;
        match k {
            Variant::Atom => all[0] = field(self.heap, 1),
            Variant::Lst | Variant::Vec | Variant::Dotted => {
                let mut parts = Vec::new();
                let mut x = field(self.heap, 1);
                while x.is_pair() {
                    parts.push(self.heap.car(x));
                    x = self.heap.cdr(x);
                }
                let placed: Vec<Value> = parts.iter().map(|&i| self.replaced(Syn::of(self.heap, i), place).value(self.heap)).collect();
                if placed == parts {
                    all[0] = field(self.heap, 1);
                } else {
                    same = false;
                    all[0] = placed.iter().rev().fold(Value::NULL, |l, &i| self.heap.cons(i, l));
                }
                if k == Variant::Dotted {
                    let t = field(self.heap, 2);
                    all[1] = self.replaced(Syn::of(self.heap, t), place).value(self.heap);
                    same &= all[1] == t;
                }
            }
        }
        if same {
            return s;
        }
        let tag = self.heap.sum_tag(v);
        all[n - 4] = field(self.heap, n - 3);
        all[n - 3..n].copy_from_slice(&[Value::fixnum(at.start), Value::fixnum(at.end), Value::fixnum(at.expansion as i64)]);
        let payload = self.heap.make_frozen(const { kind("product") }, &all[..n]);
        let s = self.heap.make_frozen(const { kind("sum") }, &[tag, payload]);
        Syn::of(self.heap, s)
    }

    /// A list's first part and its rest, the rest where the list is; a
    /// dotted list of no parts its tail's. The rest shares the list's
    /// conses, so a list is taken apart a part at a time in steps of one
    /// allocation, not of the list's length.
    pub fn split(&mut self, s: Syn) -> Option<(Syn, Syn)> {
        let p = self.heap.sum_payload(s.value(self.heap));
        let n = self.heap.bloblet_len(p);
        let l = self.heap.product_field(p, 1);
        let dotted = n == 6;
        if n == 4 || (n == 5 && self.heap.is_a(self.heap.product_field(p, 2), ObjType::Vector)) {
            return None;
        }
        if !l.is_pair() {
            return if dotted { self.split(Syn::of(self.heap, self.heap.product_field(p, 2))) } else { None };
        }
        let first = Syn::of(self.heap, self.heap.car(l));
        let rest = self.heap.cdr(l);
        let at = self.rd().at(s);
        let rest = if dotted {
            let t = self.heap.product_field(p, 2);
            if rest.is_pair() {
                let d = self.heap.cdr(self.heap.product_field(p, 3));
                self.syn(DOTTED, at, &[rest, t, d])
            } else {
                Syn::of(self.heap, t)
            }
        } else {
            let d = self.heap.cdr(self.heap.product_field(p, 2));
            self.syn(LST, at, &[rest, d])
        };
        Some((first, rest))
    }
}

const ATOM: usize = 0;
const LST: usize = 1;
const DOTTED: usize = 2;
const VEC: usize = 3;

// ------------------------------------------------------------ the reader's

/// The reader's builder of `syn` ([`fixpt_read::Build`]), its places
/// counted from `base`: [`Mk`]'s.
pub struct HeapSyn<'h> {
    pub heap: &'h mut Heap,
    pub syms: &'h mut SymTable,
    pub base: i64,
}

impl<'h> HeapSyn<'h> {
    pub fn new(heap: &'h mut Heap, syms: &'h mut SymTable, base: i64) -> HeapSyn<'h> {
        HeapSyn { heap, syms, base }
    }

    fn at(&self, at: Place) -> At {
        At { start: self.base + at.start as i64, end: self.base + at.end as i64, expansion: 0 }
    }

    fn mk<'b>(&'b mut self, interner: &'b Interner) -> Mk<'b> {
        Mk::new(self.heap, interner, self.syms)
    }
}

impl Build for HeapSyn<'_> {
    type Node = Syn;
    // Its places are characters (`At`), as FX-26's reader counts them.
    const CHARS: bool = true;

    fn atom(&mut self, interner: &mut Interner, at: Place, datum: &Datum) -> Syn {
        let at = self.at(at);
        let v = match datum {
            Datum::Bool(b) => V::Bool(*b),
            Datum::Number(n) => V::Number(n.clone()),
            Datum::Char(c) => V::Char(*c),
            Datum::Str(s) => V::Str(s.clone()),
            Datum::Symbol(s) => V::Symbol(*s),
            Datum::Keyword(s) => V::Keyword(*s),
            Datum::Bytevector(b) => V::Bytevector(b.clone()),
            Datum::Nil => V::Nil,
            Datum::List { .. } | Datum::Vector(_) => unreachable!("built from its items"),
        };
        self.mk(interner).atom(at, &v)
    }

    fn list(&mut self, interner: &mut Interner, at: Place, items: Vec<Syn>, tail: Option<Syn>) -> Syn {
        let at = self.at(at);
        self.mk(interner).list(at, &items, tail)
    }

    fn vector(&mut self, interner: &mut Interner, at: Place, items: Vec<Syn>) -> Syn {
        let at = self.at(at);
        self.mk(interner).vector(at, &items)
    }
}

// ------------------------------------------------------------- lent, held

/// `f`, with `heap` and `syms` lent to it (`fixpt_memmgmt::lend`): where
/// [`Syn`]'s methods reach them, a front end's phase.
pub fn with_syntax<R>(heap: &mut Heap, syms: &mut SymTable, f: impl FnOnce() -> R) -> R {
    // The forms let go since the last: their slots emptied, to be held
    // again.
    let dropped = std::mem::take(&mut *syms.forms.dropped.borrow_mut());
    if !dropped.is_empty() {
        let v = kept_vector(heap);
        for &i in &dropped {
            heap.obj_set(v, i, Value::FALSE);
        }
        syms.forms.free.borrow_mut().extend(dropped);
    }
    fixpt_memmgmt::lend::lend_pair(heap, syms, f)
}

/// Whether syntax may be read and made now ([`with_syntax`]).
pub fn lent() -> bool {
    fixpt_memmgmt::lend::is_lent_pair::<Heap, SymTable>()
}

/// `f` of the syntax's reading, lent.
#[inline(always)]
pub fn rd<R>(f: impl FnOnce(Rd) -> R) -> R {
    fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, R>(|heap, syms| f(Rd { heap, syms }))
}

/// `f` of the syntax's making, lent, symbols said by `interner`.
pub fn mk<R>(interner: &Interner, f: impl FnOnce(&mut Mk) -> R) -> R {
    fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, R>(|heap, syms| f(&mut Mk::new(heap, interner, syms)))
}

/// The heap lent, as [`with_syntax`] lends it.
#[inline(always)]
fn heap<R>(f: impl FnOnce(&mut Heap) -> R) -> R {
    fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, R>(|heap, _| f(heap))
}

impl Syn {
    /// Where it is.
    #[inline(always)]
    pub fn at(self) -> At {
        rd(|r| r.at(self))
    }

    /// Where it is, as the checker says it.
    #[inline(always)]
    pub fn span(self) -> Span {
        span_of(self.at())
    }

    /// Its symbol, if it is one.
    #[inline(always)]
    pub fn sym(self) -> Option<Sym> {
        rd(|r| r.sym(self))
    }

    /// A proper list's items (none for `()`), or none.
    #[inline(always)]
    pub fn list(self) -> Option<Vec<Syn>> {
        rd(|r| r.list(self))
    }

    /// Whether it is `()`.
    #[inline(always)]
    pub fn is_nil(self) -> bool {
        rd(|r| r.is_nil(self))
    }

    /// It, looked at.
    pub fn view(self) -> V {
        rd(|r| r.view(self))
    }

    /// What it is, looked at no deeper ([`Shape`]).
    #[inline(always)]
    pub fn shape(self) -> Shape {
        rd(|r| r.shape(self))
    }

    /// Its first part, if it is a list, proper or dotted, of one or more.
    #[inline(always)]
    pub fn head(self) -> Option<Syn> {
        rd(|r| r.head(self))
    }

    /// Its first part's symbol, if it is a proper list whose first part is
    /// one: a form's head, as `list()` would find it.
    #[inline(always)]
    pub fn head_sym(self) -> Option<Sym> {
        rd(|r| if r.shape(self) == Shape::List { r.head(self).and_then(|h| r.sym(h)) } else { None })
    }

    /// Its parts, if it is a proper list (`()`'s none), read as they are
    /// reached ([`Items`]).
    #[inline(always)]
    pub fn items(self) -> Option<Items> {
        match rd(|r| r.parts(self))? {
            (items, None) => Some(items),
            _ => None,
        }
    }

    /// Its parts and its tail, if it is a list, proper or dotted.
    #[inline(always)]
    pub fn parts(self) -> Option<(Items, Option<Syn>)> {
        rd(|r| r.parts(self))
    }

    /// Whether it is `(head …)`, of symbol `head`.
    pub fn is_form(self, head: Sym) -> bool {
        self.list().and_then(|l| l.first().copied()).and_then(Syn::sym) == Some(head)
    }

    /// An atom, or a list or vector, of `v`, at `at`.
    pub fn new(at: impl Into<At>, v: V, interner: &Interner) -> Syn {
        mk(interner, |m| m.atom(at.into(), &v))
    }

    /// An atom of `v`, not a symbol nor a keyword (no names said), or a
    /// list or vector, at `at`.
    pub fn datum(at: impl Into<At>, v: V) -> Syn {
        fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, Syn>(|heap, syms| Mk::with(heap, None, syms).atom(at.into(), &v))
    }

    /// A vector of `items`, at `at`.
    pub fn vector(at: impl Into<At>, items: &[Syn]) -> Syn {
        fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, Syn>(|heap, syms| Mk::with(heap, None, syms).vector(at.into(), items))
    }

    /// `()`, at `at`.
    pub fn nil(at: impl Into<At>) -> Syn {
        Syn::of_list(at, &[], None)
    }

    /// A proper list of `items`, at `at`.
    pub fn lst(at: impl Into<At>, items: Vec<Syn>) -> Syn {
        Syn::of_list(at, &items, None)
    }

    /// Symbol `s`, at `at`.
    pub fn symbol(at: impl Into<At>, s: Sym, interner: &Interner) -> Syn {
        mk(interner, |m| m.sym(at.into(), s))
    }

    /// The symbol named `name`, interned, at `at`.
    pub fn named(at: impl Into<At>, name: &str, interner: &mut Interner) -> Syn {
        let s = interner.intern(name);
        Syn::symbol(at, s, interner)
    }

    /// A list of `items`, dotted with `tail` if given, at `at`.
    pub fn of_list(at: impl Into<At>, items: &[Syn], tail: Option<Syn>) -> Syn {
        fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, Syn>(|heap, syms| Mk::with(heap, None, syms).list(at.into(), items, tail))
    }

    /// [`Mk::moved`] of it.
    pub fn moved(self, by: i64, placed: &mut impl FnMut(u32)) -> Syn {
        fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, _>(|heap, syms| Mk::with(heap, None, syms).moved(self, by, placed))
    }

    /// It as the front end written in FX-26 is handed it, in the heap that
    /// runs that front end (`docs/research/heap-syntax.md`): a part a
    /// macro's template made placed at its provenance's id, its template's
    /// place and each use's, out (`fixpt_heap::provenance`), as the Rust
    /// compiler places its code (`place_of`), so that code either compiler
    /// makes of it says the same; and no expansion, which numbers the Rust
    /// expander's, none of FX-26's. What no macro made is itself.
    pub fn handed(self) -> Syn {
        fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, _>(|heap, syms| {
            Mk::with(heap, None, syms).replaced(self, &mut |heap, at| {
                if at.expansion == 0 {
                    return at;
                }
                let mut chain = vec![at.start];
                chain.extend(fixpt_read::expansion_trace(span_of(at)).iter().map(|e| at_of(e.at).start));
                let id = heap.provenance.id(&chain);
                At { start: id, end: id, expansion: 0 }
            })
        })
    }

    /// [`Mk::split`] of it.
    pub fn split(self) -> Option<(Syn, Syn)> {
        fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, _>(|heap, syms| Mk::with(heap, None, syms).split(self))
    }

    /// The list it is, its parts now `items` and `tail` where they were
    /// `was`: itself if each is the very one it was (`eq?`), so that what
    /// a walk leaves as it is is shared, not made again; else a list anew,
    /// where it is (TODO §241).
    pub fn with_parts(self, was: (&[Syn], Option<Syn>), items: &[Syn], tail: Option<Syn>) -> Syn {
        if was.0 == items && was.1 == tail { self } else { Syn::of_list(self.at(), items, tail) }
    }

    /// It, at `at`: its parts the same.
    pub fn placed(self, at: At) -> Syn {
        fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, Syn>(|heap, syms| Mk::with(heap, None, syms).at(self, at))
    }

    /// It as the Rust reader's `Syntax`, spans and all.
    pub fn to_syntax(self) -> fixpt_read::Syntax {
        let span = self.span();
        let datum = match self.view() {
            V::Bool(b) => Datum::Bool(b),
            V::Number(n) => Datum::Number(n),
            V::Char(c) => Datum::Char(c),
            V::Str(s) => Datum::Str(s),
            V::Symbol(s) => Datum::Symbol(s),
            V::Keyword(s) => Datum::Keyword(s),
            V::Nil => Datum::Nil,
            V::List { items, tail } => Datum::List { items: items.into_iter().map(Syn::to_syntax).collect(), tail: tail.map(|t| Box::new(t.to_syntax())) },
            V::Vector(items) => Datum::Vector(items.into_iter().map(Syn::to_syntax).collect()),
            V::Bytevector(b) => Datum::Bytevector(b),
        };
        fixpt_read::Syntax::new(span, datum)
    }

    /// `Syntax` `s` as `syn`, at its places ([`at_of`]).
    pub fn from_syntax(s: &fixpt_read::Syntax, interner: &Interner) -> Syn {
        let at = at_of(s.span);
        let v = match &s.datum {
            Datum::Bool(b) => V::Bool(*b),
            Datum::Number(n) => V::Number(n.clone()),
            Datum::Char(c) => V::Char(*c),
            Datum::Str(x) => V::Str(x.clone()),
            Datum::Symbol(x) => V::Symbol(*x),
            Datum::Keyword(x) => V::Keyword(*x),
            Datum::Nil => V::Nil,
            Datum::Bytevector(b) => V::Bytevector(b.clone()),
            Datum::List { items, tail } => {
                let items: Vec<Syn> = items.iter().map(|i| Syn::from_syntax(i, interner)).collect();
                let tail = tail.as_deref().map(|t| Syn::from_syntax(t, interner));
                return Syn::of_list(at, &items, tail);
            }
            Datum::Vector(items) => {
                let items: Vec<Syn> = items.iter().map(|i| Syn::from_syntax(i, interner)).collect();
                return mk(interner, |m| m.vector(at, &items));
            }
        };
        Syn::new(at, v, interner)
    }
}

/// Span `s`'s place: its file's base, and its characters past it
/// ([`span_of`]).
pub fn at_of(s: Span) -> At {
    let base = base_of(s.file);
    let (start, end) = TEXTS.with(|t| {
        let t = t.borrow();
        let char_at = |b: u32| match t.iter().find(|x| x.base == base) {
            Some(x) => x.starts.partition_point(|&s| s <= b).max(1) as i64 - 1,
            None => b as i64,
        };
        (char_at(s.start), char_at(s.end))
    });
    At { start: base + start, end: base + end, expansion: s.expansion }
}

/// A piece of syntax held past code that runs: its place in a vector the
/// heap holds as a global, `%syntax-kept`, which a collection updates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Kept(usize);

const KEPT: &str = "%syntax-kept";

impl Kept {
    /// `s`, held.
    pub fn new(s: Syn) -> Kept {
        heap(|heap| {
            let v = s.value(heap);
            Kept(kept_push(heap, v))
        })
    }

    /// What is held.
    pub fn get(self) -> Syn {
        heap(|heap| {
            let kept = kept_vector(heap);
            let v = heap.obj_ref(kept, self.0);
            Syn::of(heap, v)
        })
    }
}

/// The vector the held syntax is in, `%syntax-kept`'s value, made the
/// first time: slot 0 says how many slots are taken.
fn kept_vector(heap: &mut Heap) -> Value {
    let sym = heap.intern(KEPT);
    let slot = heap.symbol_global_slot(sym);
    let v = heap.global(slot);
    if heap.is_a(v, ObjType::Vector) {
        return v;
    }
    let v = heap.make_vector(64, Value::FALSE);
    heap.obj_set(v, 0, Value::fixnum(0));
    heap.set_global(slot, v);
    v
}

/// `x` held in a slot of its own, the vector grown if it is full: the
/// slot's number.
fn kept_push(heap: &mut Heap, x: Value) -> usize {
    let mut v = kept_vector(heap);
    let n = heap.obj_ref(v, 0).as_fixnum() as usize;
    if n + 1 >= heap.obj_len(v) {
        let len = heap.obj_len(v);
        let w = heap.make_vector(len * 2, Value::FALSE);
        for i in 0..len {
            let y = heap.obj_ref(v, i);
            heap.obj_set(w, i, y);
        }
        let sym = heap.intern(KEPT);
        let slot = heap.symbol_global_slot(sym);
        heap.set_global(slot, w);
        v = w;
    }
    heap.obj_set(v, n + 1, x);
    heap.obj_set(v, 0, Value::fixnum(n as i64 + 1));
    n + 1
}

/// A form held past code that runs, as long as a copy of it is: a slot
/// of `%syntax-kept` ([`Kept`]), which a collection updates, let go when
/// the last copy drops, at its heap's next lending ([`with_syntax`]); and
/// where it is, which needs no heap to say (`docs/research/heap-syntax.md`).
#[derive(Clone)]
pub struct Form(std::rc::Rc<Held>);

struct Held {
    slot: usize,
    at: At,
    /// Its heap's slots ([`SymTable::forms`]): which heap it is in.
    slots: std::rc::Rc<FormSlots>,
}

impl Drop for Held {
    fn drop(&mut self) {
        self.slots.dropped.borrow_mut().push(self.slot);
    }
}

impl std::fmt::Debug for Form {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Form({}, {:?})", self.0.slot, self.0.at)
    }
}

impl Form {
    /// `s`, held, in the heap lent.
    pub fn new(s: Syn) -> Form {
        fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, _>(|heap, syms| {
            let (v, at) = (s.value(heap), Rd { heap, syms }.at(s));
            let freed = syms.forms.free.borrow_mut().pop();
            let slot = match freed {
                Some(i) => {
                    let kept = kept_vector(heap);
                    heap.obj_set(kept, i, v);
                    i
                }
                None => kept_push(heap, v),
            };
            Form(std::rc::Rc::new(Held { slot, at, slots: syms.forms.clone() }))
        })
    }

    /// What is held: refused in another heap's lending.
    pub fn get(&self) -> Syn {
        fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, _>(|heap, syms| {
            assert!(std::rc::Rc::ptr_eq(&syms.forms, &self.0.slots), "a form of another heap's syntax");
            let kept = kept_vector(heap);
            let v = heap.obj_ref(kept, self.0.slot);
            Syn::of(heap, v)
        })
    }

    /// Where it is.
    pub fn at(&self) -> At {
        self.0.at
    }

    /// Where it is, as the checker says it ([`span_of`]).
    pub fn span(&self) -> Span {
        span_of(self.0.at)
    }
}

/// How many pieces of syntax `heap` holds ([`Kept`]).
pub fn kept_count(heap: &Heap) -> usize {
    let Some(sym) = heap.interned(KEPT) else { return 0 };
    let v = heap.global(heap.symbol_global_slot(sym));
    if heap.is_a(v, ObjType::Vector) { heap.obj_ref(v, 0).as_fixnum() as usize } else { 0 }
}

/// `text`, of file `file`, read into `syn` by the Rust reader, its places
/// past `file`'s base ([`base_of`]); its text noted ([`note_text`]).
pub fn read_syn(text: &str, file: FileId, interner: &mut Interner) -> fixpt_read::ReadResult<Vec<Syn>> {
    read_syn_from(text, file, 0, interner)
}

/// [`read_syn`] of the forms from byte `start` on, their places in all of
/// `text`.
pub fn read_syn_from(text: &str, file: FileId, start: usize, interner: &mut Interner) -> fixpt_read::ReadResult<Vec<Syn>> {
    note_text(file, Arc::from(text));
    read_syn_unnoted(text, file, start, interner)
}

/// [`read_syn_from`], its text noted already.
fn read_syn_unnoted(text: &str, file: FileId, start: usize, interner: &mut Interner) -> fixpt_read::ReadResult<Vec<Syn>> {
    read_at(text, base_of(file), file, start, interner)
}

/// `text` read into `syn` from byte `start` on, its places past `base`.
fn read_at(text: &str, base: i64, file: FileId, start: usize, interner: &mut Interner) -> fixpt_read::ReadResult<Vec<Syn>> {
    fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, _>(|heap, syms| {
        let mut r = fixpt_read::Reader::with_builder(text, file, fixpt_read::SyntaxProfile::FX26, interner, HeapSyn::new(heap, syms, base));
        r.seek(start);
        r.read_all_built()
    })
}

/// `text` read into `syn` on the side, apart from the program (a type
/// written for the checker's tables, an expression a test checks, a file
/// looked at before it is loaded): its places past a base of its own, its
/// spans file 0's, in it, which leaves the program's where they are.
pub fn read_syn_side(text: &str, interner: &mut Interner) -> fixpt_read::ReadResult<Vec<Syn>> {
    let base = side_base();
    note_at(base, text);
    read_at(text, base, FileId(0), 0, interner)
}

/// `f` of `text` read into `syn` on the side ([`read_syn_side`]), while
/// its places are known; its text forgotten after, so that what is read
/// again and again (a module file's loads, each form) keeps nothing.
pub fn read_syn_passing<T>(text: &str, interner: &mut Interner, f: impl FnOnce(&[Syn], &Interner) -> T) -> fixpt_read::ReadResult<T> {
    let base = side_base();
    note_at(base, text);
    let r = read_at(text, base, FileId(0), 0, interner).map(|forms| f(&forms, interner));
    TEXTS.with(|t| t.borrow_mut().retain(|x| x.base != base));
    r
}

/// `text`'s first form read into `syn` on the side ([`read_syn_side`]):
/// for what looks at a file's beginning only.
pub fn read_syn_first(text: &str, interner: &mut Interner) -> fixpt_read::ReadResult<Option<Syn>> {
    let base = side_base();
    note_at(base, text);
    fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, _>(|heap, syms| {
        let mut r = fixpt_read::Reader::with_builder(text, FileId(0), fixpt_read::SyntaxProfile::FX26, interner, HeapSyn::new(heap, syms, base));
        r.read_built()
    })
}

/// `f`, with syntax lent from a heap and table of its own: for reading a
/// piece of text with an interner of its own, no checker's, whose symbols
/// are no world's. Nothing made in it outlives it.
pub fn aside<R>(f: impl FnOnce() -> R) -> R {
    let (mut heap, mut syms) = (Heap::new(), SymTable::default());
    with_syntax(&mut heap, &mut syms, f)
}

/// `text` read into `syn`, placed nowhere a message says (data, not a
/// program's text: the macros' kernel's tables).
pub fn read_syn_unplaced(text: &str, interner: &mut Interner) -> fixpt_read::ReadResult<Vec<Syn>> {
    fixpt_memmgmt::lend::with_lent_pair::<Heap, SymTable, _>(|heap, syms| {
        let mut r = fixpt_read::Reader::with_builder(text, FileId(0), fixpt_read::SyntaxProfile::FX26, interner, HeapSyn::new(heap, syms, UNPLACED));
        r.read_all_built()
    })
}
