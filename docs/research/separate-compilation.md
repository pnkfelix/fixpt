# Separate compilation for FX-26

A research note, 2026-09-29. Nothing here is implemented. It answers four
questions: what separate compilation FX-26 can do as it stands; which small
changes would enable more of it without losing FX-26's character; what FX-91
and FX-87 had, and what later systems do; and a staged plan with open
questions for the user. The sources are listed at the end. Each on-disk
paper is cited by path and PDF page (in the FX-91 report and Sheldon's
thesis, the PDF page is the printed page). Repository files are cited by
path and line, as of commit `eaab38f`.

**In brief.** FX-26 has no units today, but it has most of what a unit
system needs:
- an incremental REPL that checks and compiles one form against a summary
  of the forms before it (the checker's environment, the compiler's global
  cells);
- a redefinition rule that already decides when dependents must be checked
  again;
- inlining guarded by the identity of the global's closure, so it never has
  to be recompiled for correctness;
- an initial environment written as `(name type)` text, which is an
  interface file in all but name.

What it lacks is identity that is not "a name in one flat program". Global
regions are keyed by `Sym`, generative types by their index in the checker,
and the compiler's facts by byte offsets in one text. Three things are also
not persisted: checked state, compiled words, and native code.

The recommendation runs in four stages:
1. Cache first, with no language change: an image of the loaded front end,
   and snapshots of the checker at file boundaries.
2. Fix position-keyed facts, which also fixes the known "inlined `extract`
   gets field -1" bug.
3. Add a small, optional `unit` header with imports and exports. Interfaces
   are written by the checker in the standard environment's own format, and
   linking reuses the redefinition rule as a cutoff test.
4. Later, carry compiled units as fragments, the C10 of
   `type-and-effect-directions.md`.

From FX-91, adopt `input`'s idea of a closed file stamped for identity, and
abstract effects, bounded. Skip first-class modules for now.

**Examples.** Each idea below comes with a toy: two tiny "files", a module
(a stack, a counter, a tally) and a client, a few lines each, and beside it
the same thing in the language the idea is drawn from (FX-91, FX-87, SML,
OCaml, Haskell, Rust, Racket). Two kinds of FX-26 code are kept apart:
- **FX-26 today**: in a file under `docs/research/examples/separate-compilation/`,
  checked with `fixpt check FILE` (both checkers agree on each) and run
  with `fixpt eval FILE`, with `target/release/fixpt` as of 2026-09-29
  (commit `e623b23`, plus uncommitted work in the tree). There are no
  units yet, so each file holds both "files" one after the other, marked
  `;;; ---- name.fx ----`, joined as the front end joins its files today.
  A file named `*-rejected.fx` is meant to be refused, and is.
- **Proposed**: syntax that does not exist, marked so, kept close to
  FX-26's forms. Not checked, since nothing can check it.

| Example file (FX-26 today)   | What it shows                                               | Result of `fixpt eval` | Section |
| ---------------------------- | ----------------------------------------------------------- | ---------------------- | ------- |
| `stack-record.fx`            | a module as a product of procedures; a client generic in it | `2`                    | §1      |
| `stack-abstract-rejected.fx` | that client cannot take the stack apart                     | refused, as meant      | §1      |
| `counter-generative.fx`      | an abstract type as a generative type                       | `3`, then `0`          | §1, §2  |
| `counter-opaque-rejected.fx` | a counter is not an int outside its conversions             | refused, as meant      | §1      |
| `set-functor.fx`             | a functor as a polymorphic procedure over products          | `#t`                   | §1      |
| `tally-effects.fx`           | an export's effect names the module's private region        | `2`                    | §2.3    |
| `tally-effect-poly.fx`       | a client polymorphic in the module's effect                 | `2`                    | §2.3    |
| `relink-compatible.fx`       | a new implementation at the same type: no re-check          | `20`                   | §2.4    |
| `relink-broken-rejected.fx`  | at another type: the client is broken                       | refused, as meant      | §2.4    |
| `inline-guard.fx`            | a call inlined behind a guard (`fixpt compile`)             | `2`                    | §2.5    |
| `hook-icell.fx`              | a knot across files through an I-cell                       | `12`                   | §2.6    |

The FX-91 snippets are the FX-91 implementation's own test programs where
one fits (`extracted/fx91/tests.fx`), and were run with fixpt's FX-91 port
(`fixpt --dialect fx91 eval`), which says whether each checks. The Rust
snippet was compiled with `rustc`. The SML, OCaml, Haskell and Racket
snippets are written for this note and were not compiled: no compiler for
them is installed here.

| Example | Idea                                      | FX-26 today             | Proposed FX-26         | Beside it                          |
| ------- | ----------------------------------------- | ----------------------- | ---------------------- | ---------------------------------- |
| 1       | a module value; a generic client          | `stack-record.fx`       | none                   | SML signature, functor; FX-91      |
| 2       | an abstract type                          | `counter-generative.fx` | none                   | FX-91; OCaml `.mli`; Haskell; Rust |
| 3       | a functor                                 | `set-functor.fx`        | none                   | SML functor                        |
| 4       | a unit header, export list                | Example 2               | `unit`, `import`       | Haskell, OCaml, FX-91              |
| 5       | an interface written by the checker       | `fixpt check` output    | `counter.fxi`          | FX-91 `load` and `.fxt`            |
| 6       | precise globals across units              | `fixpt check` output    | options (a)–(c)        | none                               |
| 7       | effects, regions, abstract effects        | `tally-effect*.fx`      | `abstract-effect`      | FX-91 `(abs ticks effect)`         |
| 8       | linking as redefinition (cutoff)          | `relink-*.fx`           | stamps in `.fxi`       | SML/NJ CM                          |
| 9       | cross-unit inlining under a guard         | `inline-guard.fx`       | `unfolding`, link word | GHC `INLINE`                       |
| 10      | initialization order; a knot across units | `hook-icell.fx`         | `import`, `export`     | Racket `require`                   |
| 11      | a compiled file of types and values       | none                    | a C10 fragment         | FX-87 `.fxfasl`                    |

The sketch of options 2 and 3 of §1 (the image, prefix snapshots) is
proposed tooling over today's files.

## 1. Today

### What a program is

A program is one sequence of top-level forms: `define`, `define*`,
`define-rec`, `define-type`, `define-effect`, `define-generative`,
`private-regions`, and expressions (`crates/fixpt-fx26/src/top.rs`
lines 1–24). Types and effect abbreviations are declared ahead, in a first
pass over the whole text (`declare_ahead`, `top.rs` 766–786). Values are
not: "a definition sees only the definitions before it" (`docs/fx26.md`
87–100). The soundness note models a program's definitions as nested
`let` and `letrec` (`docs/research/soundness.md` 60).

The front end written in FX-26 is twelve files, 13,545 lines by `wc -l`
today (about 1,550 top-level forms). `lib.rs` joins them into one text
(`front_end`, `FRONT_END_FILES`) and checks that text as a single program;
`front_end_location` maps an offset in it back to `file:line:col`. A scan of
top-level names shows the files form a DAG:
- the leaves are `eager-reader`, `table`, `layout`, `standard`, `arm64` and
  `native-layout`;
- `native.fx` uses `parser`, `layout`, `compile`, `arm64` and
  `native-layout`, but not `check`;
- the only forward "references" the scan finds are names used as locals
  (`items`, `top`, `env`, `code`), which the checker should confirm.

The files keep their names apart by prefix, by hand: `k-` for the checker,
`c-` for the compiler, `r-` for register code, `n-` for native, and so on.
Their state lives in shared region constants (`@t`, `@k`), and they declare
`(read @globals)` throughout (`docs/fx26.md` 207–210). That is a module
system by convention.

### What the REPL keeps between forms

The REPL is incremental, "as Larceny's is: each form is checked after the
ones before (`check-more`) and compiled alone against the globals' cells
the compiler keeps; nothing is replayed" (`PLAN.md` 1830–1832). So the
REPL already compiles a unit, one form, against a summary of everything
before it. The summary is not a file, though. It is live state in several
places:

| State kept                                             | Where                                                                                                                            | Keyed by                                  |
| ------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------- |
| each global's type                                     | Rust `Checker::env`, `global_slots` (`check.rs` 44–148); FX-26 `k-env`, `k-global`                                               | name (`Sym` / symbol), newest wins        |
| type, family and effect abbreviations                  | `dscope`                                                                                                                         | name                                      |
| generative types                                       | `Checker::generatives`, a `Vec`; comparison by index                                                                             | index in this checker                     |
| which conversions see inside, and which are identities | `inside`, `transparent`, `conversions`                                                                                           | name, index                               |
| lemmas, used by subtyping                              | `lemmas`                                                                                                                         | order proved                              |
| known procedures (a call runs code the checker saw)    | `known`                                                                                                                          | (name, place in `env`)                    |
| private regions                                        | `private_regions`, uninterned fresh regions                                                                                      | identity of the fresh region              |
| definitions and their free globals, for redefinition   | `defs` (`top.rs` 60–67, 234–265), `broken`                                                                                       | name                                      |
| facts for lowering and compiling                       | Rust `NodeFacts` by `ExpId`; FX-26 `k-facts` by `(start end)` byte offsets (`check.fx` 529–553)                                  | expression, or offset in the current text |
| globals' cells, with order of creation                 | `c-genv-index` (`compile.fx` 215–222), `c-push-global` (1623)                                                                    | name, then creation count                 |
| inlinable and specializable bodies                     | `c-inlines`, `c-specials` (`compile.fx` 1381–1420, `c-record-inline` 1563): parser tree, word, `c-genv-now`                      | name                                      |
| native code's bindings                                 | each code bloblet's fields: global cells, closures of globals' procedures bound when compiling (`native-conventions.md` 258–280) | heap address                              |
| the front end itself                                   | checked by Rust and lowered to Scheme text on every load (`session.rs` 193–199, `compile_program_as` 170–183)                    | nothing: redone each session              |

### What a compiled form depends on

- **Types and effects of what it names.** Types print and read back,
  recursive ones as `(mu %d …)` (`docs/fx26.md` 221–232). The initial
  environment is already a list of `(name type-text)` (`standard.rs`
  `ENTRIES`), and both checkers read it: FX-26's `check-program` takes it
  as `standard`. A summary of a checked prefix could be written the same
  way.
- **Precise globals lists.** A type may say `(read (globals below limit))`
  (`docs/fx26.md` 173–219). These are names, meaningful only in one flat
  namespace. They count towards redefinition compatibility ("what it reads
  is within what the old one read", 212–215). They also drive
  `no_reaching_itself` (`top.rs` 163–190).
- **Inlined bodies and specializations.** A call of a small global is
  inlined in register code behind a guard that the global still holds the
  closure it was compiled from, "so a redefinition needs no recompiling"
  (`PLAN.md` 1866–1874). The body is a parser tree whose free names resolve
  against the globals as they were (`c-genv-now`). Its facts are looked up
  by byte offset. That is why "an inlined `extract` from an earlier form
  gets field -1" (`PLAN.md` 91): `check-more` resets `k-extracts` per
  batch (`check.fx` 6371–6379), so an earlier form's offsets are gone.
  (Since this note was first written, commit `ee79c5e` fixed that symptom
  for extracts: the kept body is rewritten when kept,
  `c-resolve-extracts`, each extract made the bloblet-ref of its field.
  Other facts are still keyed by offset.)
- **Field indices and datatype layouts.** These are fixed by types.
  Products are compared label for label with equal lengths (`check.rs`
  1683–1685), and a sum's tag is a symbol at run time. A type-compatible
  change therefore never moves a field.
- **Effect summaries** (0–3 per expression, `docs/fx26.md` 292–304) decide
  where versions and folding are sound. They are per-expression facts too,
  keyed like the extracts.
- **Native code** reads globals through their cells, but binds a cell that
  holds a cellular closure when compiling (`native-conventions.md`
  270–274). Images hold no machine code
  (`type-and-effect-directions.md` 296). FX-26 programs run cellular are
  not dumpable yet (297; C9).

### Separate-compilation options as FX-26 stands

1. **Concatenation.** This is what the front end does now. It is correct
   but not separate: an edit anywhere means reading, checking and lowering
   all twelve files again. The self-compile's check phase is about 0.5 s of
   0.7 s (`docs/performance.md` 1900–1910), and loading the pieces costs
   0.11 s before a program runs (128).
2. **An image of the loaded front end.** `fixpt dump-heap` already writes a
   Scheme session's heap, compiled code included (`PLAN.md` 312–335). The
   pieces are loaded lowered into a Scheme session under `fx26-reader:`.
   Dumping that session once, keyed by a hash of the twelve texts and of the
   binary, gives separate compilation's most common benefit (not
   re-checking what did not change) with no language change. The
   `standard26` reading, "read once, as it takes the reader a while"
   (`session.rs` 664–672), belongs in the same image.
3. **Snapshots at file boundaries.** The Rust checker's state after file
   *k* depends only on files 1..*k*. Keyed by the hash of that prefix, it
   can be kept: in memory for the test suite, where every test that loads
   the pieces pays today, or on disk once it can be
   serialized. An edit to `regcode.fx` then re-checks only `regcode.fx`
   and what follows it. This is prefix caching, the SML "build linearly in
   strict bottom-up order" model (Leroy 1994, p. 109). It is sound by
   construction, since it is the same program. The FX-26 checker's state
   is heap data, so its snapshot is an image.
4. **The REPL's `check-more` as a linker.** Loading a file at the REPL
   already checks it against the session's summary and compiles it against
   the kept cells. What is missing is a way to skip the check when the file
   was checked before against the same summary. That is exactly what an
   interface stamp gives (§2).

**Sketch: options 2 and 3 on three toy files** (proposed; no language
change, so the files are today's FX-26):

```
;; stack.fx    (define-type (stack-ops (s type)) …)       snapshot K1 = checker after stack.fx,  key hash(stack.fx)
;; impl.fx     (define list-stack (stack-ops …) …)         snapshot K2 = checker after impl.fx,   key hash(stack.fx impl.fx)
;; client.fx   (define use-stack …) (use-stack list-stack)  edited: start from K2, check client.fx alone

;; option 2, the image: the same idea one level up, for the whole front end
;;   key = hash(eager-reader.fx … native-layout.fx, fixpt binary)
;;   hit:  load front-end-<key>.img (lowered, compiled, standard26 read)
;;   miss: load the twelve pieces as today, then dump the session to front-end-<key>.img
```

An edit to `client.fx` costs one file's check; an edit to `stack.fx` costs
all three, as today. That is the whole of prefix caching: it is exact
because it is the same program, and it saves nothing below an edit.

### Modules FX-26 can already write

FX-26 has no module forms, but a module *value* can be written today, in
FX-91's spirit: a product of procedures is a structure, a `define-type` of
one is a signature, a client that is `poly` in the representation cannot
see it, and a `poly` procedure from one product to another is a functor.
None of this helps separate compilation by itself, since the files are
still one text; but it is what a unit's exports would look like as a
value, and it shows what the checker already enforces.

**Example 1: a stack module and a client.** FX-26 today
(`stack-record.fx`; checked; runs to `2`):

```
;;; ---- stack.fx : the interface (a type) and one implementation ----
(define-type (stack-ops (s type))
  (productof (empty s)
             (push (subr pure (int s) s))
             (top  (subr pure (s) int))))

(define list-stack (stack-ops (listof int acyclic))
  (product (empty nil)
           (push (lambda (x s) (cons x s)))
           (top  (lambda (s) (if (null? s) 0 (car s))))))

;;; ---- client.fx : written for any s, so it cannot see the list ----
(define use-stack (poly ((s type)) (subr pure ((stack-ops s)) int))
  (plambda ((s type))
    (lambda (m) ((extract m top) ((extract m push) 2 ((extract m push) 1 (extract m empty)))))))

(use-stack list-stack)                    ; 2
```

The same client doing `(car (extract m empty))` is refused, "argument 1 is
a s, where a (pairof int t2 r) is expected" (`stack-abstract-rejected.fx`).
So `poly` gives abstraction, but on the client's side: the client is
checked once for every `s`, which is the universal half of an existential.

In SML the abstraction sits on the module's side instead, by opaque
ascription (`:>`), and a client generic in the stack is a functor:

```sml
signature STACK = sig
  type stack
  val empty : stack
  val push  : int * stack -> stack
  val top   : stack -> int
end
structure ListStack :> STACK = struct
  type stack = int list
  val empty = []
  fun push (x, s) = x :: s
  fun top [] = 0 | top (x :: _) = x
end
functor UseStack (S : STACK) = struct
  val two = S.top (S.push (2, S.push (1, S.empty)))
end
structure Two = UseStack (ListStack)
```

FX-91 is closest to the FX-26 version: a client is a `lambda` whose
parameter's type is a `moduleof`, applied to a `module`. From the FX-91
implementation's tests (`extracted/fx91/tests.fx` 142–146; fixpt's FX-91
port checks it):

```
((lambda ((ints (moduleof (abs newint type)
                          (val == (subr pure ((x newint)) bool)))))
   2)
 (module (define-abstraction newint type int)
         (define (== (x newint)) #t)))
```

What FX-26 lacks against FX-91 here is `moduleof`'s `(abs …)`: an
abstract type *inside* the product's type. `stack-ops` has to take `s` as a
parameter, and every client has to be `poly` in it.

**Example 2: an abstract counter.** FX-26 today, with the abstract type a
generative type (`counter-generative.fx`; checked; runs to `3`):

```
;;; ---- counter.fx ----
(define-generative counter int)
(define zero counter (up-counter 0))
(define* incr (subr pure (counter) counter) (lambda (c) (up-counter (+ (down-counter c) 1))))
(define* value (subr pure (counter) int) (lambda (c) (down-counter c)))

;;; ---- client.fx ----
(define* three (subr pure () int) (lambda () (value (incr (incr (incr zero))))))
(three)                                   ; 3
```

`(+ zero 1)` in the client is refused, "a int is expected here, and this is
a counter" (`counter-opaque-rejected.fx`). But `(down-counter zero)` in the
client is accepted: every global is visible to every later form, so the
conversions are too. That is the hiding `define-generative` deferred
(`generative-types.md`), and a unit's export list (§2.1) is what supplies
it.

FX-91's `define-abstraction` is the same idea with the hiding built in: the
`up-`/`down-` conversions exist inside the module only, and the `moduleof`
says `(abs newint type)`. From `extracted/fx91/tests.fx` 148–176 (the
interface is the `moduleof`, the implementation the `module`; abridged to
three operations, and the abridged program checks and runs in fixpt's FX-91
port):

```
((lambda ((ints (moduleof (abs newint type)
                          (val zero newint)
                          (val one newint)
                          (val == (subr pure ((x newint) (y newint)) bool)))))
   (with ints (== one one)))
 (module (define-abstraction newint type int)
         (define zero (up-newint 0))
         (define one (up-newint 1))
         (define (== x y) (= (down-newint x) (down-newint y)))))
```

The hiding is real in the port: `(let ((m (module (define-abstraction t
type int) (define x (up-t 3))))) (with m (down-t x)))` is refused,
"unbound value variable down-t".

OCaml, Haskell and Rust put the same line in the same place, between the
file and its interface:

```ocaml
(* counter.mli *)                       (* counter.ml *)
type t                                   type t = int
val zero  : t                            let zero = 0
val incr  : t -> t                       let incr c = c + 1
val value : t -> int                     let value c = c
```

```haskell
module Counter (Counter, zero, incr, value) where   -- `Counter`, not `Counter(..)`
newtype Counter = C Int
zero = C 0
incr (C n) = C (n + 1)
value (C n) = n
```

```rust
// counter.rs, a crate of its own (compiled with rustc 1.95.0, with a client)
pub struct Counter(i64);                 // the field is private to the crate
pub fn zero() -> Counter { Counter(0) }
pub fn incr(c: Counter) -> Counter { Counter(c.0 + 1) }
pub fn value(c: &Counter) -> i64 { c.0 }
```

**Example 3: a functor.** FX-26 today (`set-functor.fx`; checked; runs to
`#t`). The argument signature, the result signature, and a `poly`
procedure from one to the other:

```
;;; ---- set.fx ----
(define-type (eq-ops (t type)) (productof (eq (subr pure (t t) bool))))
(define-type (set-ops (t type))
  (productof (empty  (listof t acyclic))
             (insert (subr pure (t (listof t acyclic)) (listof t acyclic)))
             (member (subr pure (t (listof t acyclic)) bool))))

(define make-set (poly ((t type)) (subr pure ((eq-ops t)) (set-ops t)))
  (plambda ((t type))
    (lambda (e)
      (product
        (empty nil)
        (insert (lambda (x s) (cons x s)))
        (member (letrec ((mem (subr pure (t (listof t acyclic)) bool)
                           (lambda (x s)
                             (if (null? s) #f
                                 (if ((extract e eq) x (car s)) #t (mem x (cdr s)))))))
                  mem))))))

;;; ---- client.fx : applies the functor, then uses the result ----
(define int-set (set-ops int) (make-set (product (eq (lambda (a b) (= a b))))))
(define* has-two (subr pure () bool)
  (lambda ()
    ((extract int-set member) 2
      ((extract int-set insert) 2 ((extract int-set insert) 1 (extract int-set empty))))))
(has-two)                                 ; #t
```

`member`'s loop is `pure`, not `spin`: size-change sees `(cdr s)` of an
`acyclic` list. SML, for comparison:

```sml
signature EQ = sig type t  val eq : t * t -> bool end
functor MakeSet (E : EQ) = struct
  type set = E.t list
  val empty = []
  fun insert (x, s) = x :: s
  fun member (x, s) = List.exists (fn y => E.eq (x, y)) s
end
structure IntSet = MakeSet (struct type t = int  val eq = op = end)
val hasTwo = IntSet.member (2, IntSet.insert (2, IntSet.insert (1, IntSet.empty)))
```

The FX-26 set is transparent: `int-set`'s type says a set is a
`(listof int acyclic)`. Making it abstract, as `MakeSet (E) :> SET` would,
needs a type the functor makes fresh at each application, which is a
generative type made at run time: the first-class-module territory §3
recommends skipping.

### What checking a file against a summary needs, and what breaks

| Concern                          | Today                                                                                      | What breaks across units                                                                             | Fix                                                                                                         |
| -------------------------------- | ------------------------------------------------------------------------------------------ | ---------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------- |
| global identity                  | a `Sym`; a redefinition makes a new global of the same name                                | two units' private `helper`s collide, and `(globals helper)` means whichever is newest               | a global is (unit, name); a private name never appears unqualified outside its unit                         |
| precise globals effects          | names of any global                                                                        | an export's type names a private global the importer cannot name                                     | widen private names to the unit's globals region in the interface (§2.3)                                    |
| redefinition                     | re-check users by free names (`users_of`)                                                  | users in other units are not in `defs`                                                               | the same rule at unit grain: a changed interface re-checks dependents unless every export fits (§2.4)       |
| `no_reaching_itself`             | a procedure whose effect reads its own global says `spin`                                  | reading a whole unit's region can reach itself only if a unit's globals are redefined from inside it | same rule as `@globals` today (`top.rs` 182–187), applied to the unit region                                |
| generative identity              | index in this checker's `generatives`                                                      | two runs number differently; the index means nothing in a file                                       | (unit, name), with `rep` in the interface, since safety analyses look through the name                      |
| private regions                  | fresh uninterned per program                                                               | an export's type may mention one (the reader's entry points do)                                      | stamped (unit, name) constants, fresh to everyone else, as now                                              |
| lemmas                           | a list subtyping consults                                                                  | an importer's subtyping must see the exporter's lemmas                                               | lemmas are exports; a lemma is a proof, so exporting one is coherent                                        |
| known procedures and conversions | `known`, `conversions` by binding                                                          | size-change and self-application need to know an import is a lambda, or an identity conversion       | a flag per export in the interface                                                                          |
| termination                      | size-change within a `define-rec` group; calls outside trust the callee's `spin`-free type | nothing, as long as a group never spans units                                                        | groups stay in one unit; knots across units use I-cells, as `docs/fx26.md` 443–445 already says             |
| facts                            | FX-26: byte offsets in one text                                                            | offsets repeat across files; `check-more` forgets them                                               | key by (file, offset), or carry facts in the tree; needed anyway for the field -1 bug                       |
| inlining and specialization      | parser tree + word + genv count, guarded by the closure's identity                         | the importer's guard must name the exporter's word, and the body's facts must travel with it         | interfaces carry bodies with facts and an implementation stamp; the guard fails if the stamp differs (§2.5) |
| native code's bound globals      | heap addresses when compiling                                                              | not persistable                                                                                      | keep machine code out of units; regenerate on load, as images already do                                    |
| declared-ahead types             | the whole text's `define-type`s first                                                      | a type in one file may mention a later file's                                                        | ahead only within a unit; across units, only imports (the front end's DAG already fits)                     |
| initialization order             | textual                                                                                    | units must run in an order consistent with imports                                                   | imports form a DAG, run before the importer, as in Racket and Chez                                          |

## 2. Small changes that keep FX-26's character

FX-26 is a REPL-first, Scheme-like, effect-typed language that infers where
it can. Each change below is weighed by what it costs that.

### 2.1 A unit is a file, with an optional header

**Proposed** (nothing here exists):

```
(unit parser
  (import eager-reader table)            ; units this one sees, which run before it
  (export parse-program syn top           ; values and types; everything, if omitted
          (effect parses)                 ; an effect abbreviation, transparent
          (region @p)))                   ; a private region its exports' types mention
```

- A file with no header is a unit that imports the units before it and
  exports everything, which is today's behaviour. The REPL is the
  anonymous last unit.
- Within a unit, nothing changes. Types are declared ahead, and values see
  only what is before them.
- Across units, a unit sees exactly its imports' exports. This is the
  "sees only those before" rule, one level up.
- Names are not qualified in source unless they clash: `(import (table
  as t))` gives `t:make-table`. The prefixes the front end uses by hand
  would become optional.

*Cost:* one form, one more thing the parser reserves (`unit`), and
qualified names in messages. It is not a module language. A unit is not a
value, has no functors, and is not a type.

**Example 4: the counter as two units** (proposed; compare Example 2, which
is the same code today). Only the two headers and the last line are new:

```
;;; counter.fx
(unit counter
  (export counter zero incr value))      ; not up-counter, down-counter
(define-generative counter int)
(define zero counter (up-counter 0))
(define* incr (subr pure (counter) counter) (lambda (c) (up-counter (+ (down-counter c) 1))))
(define* value (subr pure (counter) int) (lambda (c) (down-counter c)))

;;; client.fx
(unit client
  (import counter))
(define* three (subr pure () int) (lambda () (value (incr (incr (incr zero))))))
(three)                                  ; 3
(down-counter zero)                      ; proposed error: `down-counter` is not exported by `counter`
```

With `(import (counter as c))` the client would write `c:zero`, `c:incr`.
Exporting the type name `counter` but not its conversions is Haskell's
`Counter` without `(..)`, OCaml's `type t` in the `.mli`, and FX-91's
`(abs newint type)` (Example 2). The difference from FX-91 is that nothing
is a value: `counter` cannot be passed to a procedure, so Example 1's
`use-stack` still needs the product.

### 2.2 Interfaces written by the checker

The `.fxi` is written by the checker, never by hand (**proposed**). It has
the same shape as `standard.rs`'s `ENTRIES`:
- `(name type)` for each export, in a canonical print, with `maxeff` atoms
  sorted so the two checkers' outputs are byte-equal;
- the unit's type, family and effect abbreviations;
- generative types, with their representation and variance;
- lemmas;
- flags for known lambdas and conversions;
- the private regions exported;
- the stamps of the interfaces it was checked against;
- optionally, unfoldings (§2.5).

The stamp is a hash of the file with the unfoldings left out. This is
GHC's fingerprint (users guide, "Recompilation checking") and Racket's
SHA-1 over the compiled form plus dependencies (`raco make` §1). It is also
Sheldon's fourth option, "compute a checksum for the input file and the
files it inputs" (thesis p. 40).

*Cost:* none to the language. Printing types is already done. Printing
effects canonically is new, since the FX-26 checker's atom order differs
from Rust's today (`docs/fx26.md` 797–799).

**Example 5: what `counter.fxi` would hold** (proposed format). Today,
`fixpt check counter-generative.fx` prints, for the counter's part:

```
define up-counter : (subr pure (int) counter) ! pure
define down-counter : (subr pure (counter) int) ! pure
define zero : counter ! (read (globals up-counter))
define incr : (subr (read (globals down-counter up-counter)) (counter) counter) ! pure
define value : (subr (read (globals down-counter)) (counter) int) ! pure
```

The interface is those lines kept to the exports, with the private globals
widened as §2.3 (b) says, and the rest of the list above:

```
;;; counter.fxi -- written by the checker, never by hand (proposed)
(interface counter
  (stamp "c0ffee…")                             ; hash of counter.fx without unfoldings
  (checked-against)                             ; stamps of its imports' interfaces: none
  (generative counter int)                      ; the rep, for safety analyses; importers see only the name
  (zero  counter)
  (incr  (subr (read (globals-of counter)) (counter) counter))
  (value (subr (read (globals-of counter)) (counter) int))
  (known incr value))                           ; lambdas, for size-change and self-application
```

An importer is checked against these entries as FX-26's checker is
against `standard.rs`'s `ENTRIES` today: each one a global of that type.

The FX-91 implementation did the same with one entry. The first expression
of its `tests.fx` (lines 14–15) is a module, and a later test reads it as a
value (116–117):

```
;; tests.fx
(module (define-abstraction t type int)
        (define x (up-t 3)))

;; elsewhere
(let ((m (load "tests.fx")))
  (with m x))
```

Checking that `load` writes `tests.fxt` with two data, the type and the
effect, and trusts it while `tests.fx`'s write date is unchanged
(`typecheck.scm` 642–690). For this module fixpt's FX-91 port gives the
type `(moduleof (abs t type) (val x t))` and effect `(maxeff)`, i.e. pure;
so the `.fxt` is, up to how `unparse-dexp` prints:

```
(moduleof (abs t type) (val x t))
(maxeff)
```

The `.fxi` above is that, one entry per export, with a content hash in
place of the write date.

### 2.3 Precise globals across units

Options, in increasing cost:

| Option                                      | An export's type says                                                | Cost                                                                                        |
| ------------------------------------------- | -------------------------------------------------------------------- | ------------------------------------------------------------------------------------------- |
| a. qualify                                  | `(read (globals parser:need))` for any global, exported or not       | leaks private names; every internal change of what is read changes the interface            |
| b. widen private names to the unit's region | exported names as they are; the rest as `(read (globals-of parser))` | one new region form, `(globals-of U)` ⊆ `@globals`; precise within the unit, coarse outside |
| c. named abstract effect, bounded           | `parses`, known to importers only as `≤ (read (globals-of parser))`  | abstract effect constants in the checker; the bound is needed for licences and masking      |
| d. effect variable                          | nothing new: `(poly ((e effect)) …)`                                 | no change; only for higher-order code, as today                                             |

Recommend (b). Globals are "only read and written, and never masked"
(`docs/fx26.md` 179–180), so a unit region loses nothing that masking would
have used. `no_reaching_itself` treats it as it treats `@globals`: reading
it needs `spin` only when a global of that unit is redefined from inside
it. Redefinition compatibility stays exact within a unit. Across units it
becomes "still within the unit's region", which is what makes (b) a cutoff:
a unit whose export types did not change does not disturb its importers.

Option (c) is FX-91's `(abs id effect)` (below). Keep it for when a real
client wants to hide what it reads. An unbounded abstract effect could not
be licensed, since the licence has to see regions (`docs/fx26.md` 535–541).

**Example 6: the problem, today.** In Example 2 the client's `three` is a
`define*`, and `fixpt check` gives it

```
define three : (subr (read (globals down-counter incr up-counter value zero)) () int) ! pure
```

So a type in `client.fx` names `down-counter` and `up-counter`, which in
Example 4 `counter` does not export. If `client` exported `three`, its
interface would say, under each option:

| Option | `three` in `client.fxi`                                                                                          |
| ------ | ---------------------------------------------------------------------------------------------------------------- |
| today  | `(subr (read (globals down-counter incr up-counter value zero)) () int)`                                         |
| a      | `(subr (read (globals counter:down-counter counter:incr counter:up-counter counter:value counter:zero)) () int)` |
| b      | `(subr (maxeff (read (globals counter:incr counter:value counter:zero)) (read (globals-of counter))) () int)`    |
| c      | `(subr counter:reads () int)`, with `counter:reads ≤ (read (globals-of counter))` known to importers             |
| d      | not for `three`: it calls known procedures; (d) is Example 7's second half                                       |

Under (a), rewriting `incr` to skip `down-counter` changes `client.fxi`.
Under (b) it does not, which is the cutoff §2.4 needs; and (b) may print
as just `(read (globals-of counter))`, since the three exported names are
within it.

**Example 7: effects and a private region in an export** (FX-26 today).
The module keeps its state in a region no other program can name
(`tally-effects.fx`; checked; runs to `2`):

```
;;; ---- tally.fx ----
(private-regions @tally)
(define count (ref int @tally) (new 0))
(define* tick (subr (maxeff (read @tally) (write @tally)) () int)
  (lambda () (begin (set count (+ (get count) 1)) (get count))))

;;; ---- client.fx : names the module's region, since tick's type does ----
(define* tick-twice (subr (maxeff (read @tally) (write @tally)) () int)
  (lambda () (begin (tick) (tick))))
(tick-twice)                              ; 2
```

`fixpt check` prints `tick : (subr (maxeff (read (globals count)) (read
@tally.1) (write @tally.1)) () int)`: `@tally.1` is the fresh region, and
`count` is a private global the type names. As a unit, `tally` would
`(export tick (region @tally))`, and `count` would become `(globals-of
tally)`. The client has to say `@tally` in its own signature, which is the
coupling (c) or (d) removes. Today (d) does it, with a client polymorphic
in the effect of the operations it is given (`tally-effect-poly.fx`;
checked; runs to `2`):

```
;;; ---- tally.fx : as above, and the interface as a type ----
(define-type (tally-ops (e effect)) (productof (tick (subr e () int))))

;;; ---- client.fx : never names @tally ----
(define tick-twice (poly ((e effect)) (subr e ((tally-ops e)) int))
  (plambda ((e effect)) (lambda (m) (begin ((extract m tick)) ((extract m tick))))))

;;; ---- main.fx : links the two by application ----
(tick-twice (product (tick tick)))        ; 2
```

`tick-twice`'s type is now `(poly ((e effect)) (subr e ((productof (tick
(subr e () int)))) int))`; `@tally` appears only at the application. Option
(c) is the same hiding with the unit's name in place of the `poly`
(proposed):

```
;;; tally.fx (proposed)
(unit tally
  (export tick (abstract-effect ticks)))  ; importers see: ticks ≤ (maxeff (read @tally) (write @tally) (read (globals-of tally)))
(private-regions @tally)
(define-effect ticks (maxeff (read @tally) (write @tally) (read (globals count))))
(define count (ref int @tally) (new 0))
(define tick (subr ticks () int) (lambda () (begin (set count (+ (get count) 1)) (get count))))

;;; client.fx (proposed)
(unit client (import tally))
(define tick-twice (subr (maxeff tally:ticks (read (globals tally:tick))) () int)
  (lambda () (begin (tick) (tick))))
```

The client's type has to add `(read (globals tally:tick))`: calling `tick`
reads the global `tick`, and an importer knows only an upper bound on
`ticks`, so it cannot count that read as within it. Today, in one file,
the `tally.fx` half of this (the `define-effect` and `tick` at `(subr ticks
() int)`) checks; a `tick-twice` declared `(subr ticks () int)` is refused
for exactly this reason, its effect being `(read (globals count tick))`.

FX-91 writes the interface half as a `moduleof` with an abstraction of
kind `effect` (grammar, report pp. 6, 10):

```
(moduleof (abs ticks effect)
          (val tick (subr ticks () int)))
```

The implementation half did not go through in fixpt's FX-91 port. A
`module` with `(define-abstraction ticks effect (maxeff read write))` and
a `define-typed tick (subr ticks () int)` is refused, "effect constraint is
not satisfiable": inside the module, too, `ticks` is opaque, and FX-91 has
no conversions for an effect abstraction (§2.3.11). Whether that is the
report's rule or the port's was not settled here. The bound in (c) is what
avoids the question: an importer knows `ticks` only up to its bound, while
the unit that defines it sees through it, as a `define-effect` is seen
through today.

### 2.4 Linking is redefinition at unit grain

At load, each import's current interface is compared with the one the
dependent was checked against. This is the rule `top_defining` already
applies to a redefinition (`top.rs` 100–133):
- if every export the dependent used has a type that is a subtype of the
  one it was checked at (`fits_old`), the dependent is linked without
  being checked again;
- otherwise it is checked again from source; if it fails, its definitions
  are broken until it is fixed.

This is CM's cutoff recompilation (Blume, CM manual p. 5, citing Adams,
Tichy and Weinert 1994). It is also Sheldon's "illusion that the file
system is immutable" (LFP '90 PDF p. 5), done by stamps rather than times.
No new rule is added to the language, only a larger grain for an old one.

*Cost:* the dependent records which exports it used. `record` already
computes free globals per definition (`top.rs` 252–265).

**Example 8: the rule, today, at the grain of a definition.** Two
versions of the counter's `step`, and a client checked against the first
(`relink-compatible.fx`; checked; runs to `20`):

```
;;; ---- counter.fx, version 1 ----
(define step (subr pure (int) int) (lambda (n) (+ n 1)))

;;; ---- client.fx, checked against version 1 ----
(define* twice (subr pure (int) int) (lambda (n) (step (step n))))
(twice 0)                                 ; 2

;;; ---- counter.fx, version 2: same type, new body ----
(define step (subr pure (int) int) (lambda (n) (+ n 10)))
(twice 0)                                 ; 20: the client sees version 2
```

`twice` is not checked again; `fixpt eval` says "`step` redefined: every
use sees the new one". Change version 2's type to `(subr pure (string)
int)` and `twice` is checked again, fails, and is broken:
"`twice` is broken, since `step` was redefined (argument 1 is a int,
where a string is expected): define it again to use it"
(`relink-broken-rejected.fx`).

At unit grain (proposed), the same two outcomes, decided by the stamps and
entries of `counter.fxi`:

```
client.fx was checked against counter.fxi, stamp A, using: step : (subr pure (int) int)
counter.fx is edited; counter.fxi now has stamp B
  step : (subr pure (int) int)          fits_old → link client as it is (cutoff)
  step : (subr pure (string) int)       does not → check client.fx again; it fails;
                                        its definitions are broken until it is fixed
```

This is the shape of CM's cutoff recompilation (Blume, CM manual p. 5):
an unchanged interface stops the rebuild at the edited unit. The
difference is only that a failing re-check leaves the dependent broken, as
the REPL does now, where a build would stop.

### 2.5 Cross-unit inlining under guards and stamps

An unfolding in the `.fxi` is the parser tree (as `syn`, which both
checkers read) together with its own facts and the exporter's
implementation stamp. The importer inlines it behind the same guard as
today. At link, the guard's expected word is bound to the exporter's word
only if the stamps match. Otherwise it is bound to a sentinel that never
matches, and the call is made normally. So a changed implementation never
forces its importers to be recompiled for correctness, only for speed:
- GHC recompiles importers when an unfolding changes, and offers
  `-fomit-interface-pragmas` to trade that away ("only when M's exports
  change their type");
- OCaml offers `-opaque`;
- FX-26's guards give both at once.

Versions of a body stay sound. They depend on effect summaries of the
body's own expressions, which travel with it, and on the callee being what
the guard checks.

*Cost:* unfoldings grow interfaces. Limit them to what `c-record-inline`
already selects (20 nodes, 60 for specialization).

**Example 9: the guard, today.** The counter's `step` and a client
(`inline-guard.fx`; checked; runs to `2`):

```
;;; ---- counter.fx ----
(define step (subr pure (int) int) (lambda (n) (+ n 1)))

;;; ---- client.fx ----
(define* twice (subr pure (int) int) (lambda (n) (step (step n))))
(twice 0)                                 ; 2
```

`fixpt compile` on it shows `twice`'s register code beginning (both
compilers make the same):

```
  its register code (65 cells, not compiled):
       0: args 1
       2: global-guard step #<cellular-word lambda@296> else → 19
       6: reg 1
       8: op2imm int-add 1
      11: setreg 2
      13: reg 2
      15: op2imm int-add 1
      18: return
      19: …                              ; the calls, made normally
```

Both calls of `step` became `op2imm int-add 1`, behind one check that the
global `step` still holds the word `lambda@296`. That word is a heap
pointer in the compiling session; across units it would come from a link
table instead (proposed):

```
;;; in counter.fxi (proposed)
(unfolding step (stamp "c0ffee…") (lambda (n) (+ n 1)))   ; the tree, with its facts

;;; in client's compiled unit (proposed)
(global-guard step (link counter step "c0ffee…") else → 19)
;; at link: counter's implementation stamp is c0ffee… → the guard's word is counter's `step`
;;          it is not                               → a sentinel no word equals: always the call
```

GHC's version of the same toy carries the unfolding in `Counter.hi`, and
recompiles importers when it changes:

```haskell
module Counter (step) where
{-# INLINE step #-}
step :: Int -> Int
step n = n + 1
```

With `-fomit-interface-pragmas` (GHC) or `-opaque` (OCaml) the body stays
out of the interface and importers are recompiled "only when M's exports
change their type". The guard gives both behaviours from one interface.

### 2.6 Initialization order

A unit's top level runs once, after its imports, as Racket's "Module
requires cannot form cycles" and Chez's "once invoked, the library is not
invoked again" (CSUG §10.5). A cycle between units is an error. A knot
across units is an I-cell or a `ref`, which the types show; this is the
design `recursion-and-initialization.md` already chose for knots that are
not `define-rec` groups.

**Example 10: a knot across files, today** (`hook-icell.fx`; checked; runs
to `12`). `log.fx` runs first and calls a procedure only `app.fx`
supplies:

```
;;; ---- log.fx : runs first; calls a hook it does not define ----
(private-regions @h)
(define hook (icell (subr pure (int) int) @h) (make-icell))
(define* twice-hooked (subr (await @h) (int) int)
  (lambda (n) ((icell-get hook) ((icell-get hook) n))))

;;; ---- app.fx : imports log.fx, and ties the knot ----
(icell-put! hook (lambda ((n int)) (* n 2)))
(twice-hooked 3)                          ; 12
```

`twice-hooked`'s type says `(await @h)`: it reads a cell that may not be
filled yet, and calling it before `app.fx` runs is an error at run time,
not a wrong answer. As units (proposed), `log` would `(export hook
twice-hooked (region @h))`, `app` would `(import log)`, and `log`'s top
level would run once, before `app`'s. If `log` instead imported `app` as
well, that is a cycle, an error when linking. Racket's rule, for
comparison, where a cycle is refused too:

```racket
;; log.rkt                               ;; app.rkt
#lang racket                             #lang racket
(provide hook twice-hooked)              (require "log.rkt")
(define hook (box #f))                   (set-box! hook (lambda (n) (* n 2)))
(define (twice-hooked n)                 (twice-hooked 3)   ; 12
  ((unbox hook) ((unbox hook) n)))
```

### 2.7 Carriers: images, fragments, native code

- Stages 1–2 need only what exists: Scheme heap images of lowered code.
- A unit's compiled cellular words, with an import table (unit, name,
  assumed type) and an export table, is the fragment of C10
  (`type-and-effect-directions.md` 323–333). Its loader's checks are
  already listed there: "imports by name, each host type a subtype of the
  one assumed; … the fragment's regions renamed fresh, as
  `private-regions` does". That is §2.4 for compiled code.
- Machine code is regenerated from cells on load, as images already
  assume. It can be cached later, keyed by stamps, if load time asks for
  it.

## 3. FX-91, FX-87 and later work

### FX-91: what the report actually has

*Report on the FX Programming Language* (Gifford, Jouvelot, Sheldon,
O'Toole; MIT/LCS-TR-531 per `extracted/fx91/README`), at
`~/Dev/LangPlay/GiffordHistory/papers/fx91-report.pdf`:

- **Goal.** FX-91 "provides a module system that supports programming in
  the large [SG90]" (p. 2). "The F X module system permits types and values
  to be packaged as first-class module values. Because modules are
  first-class values, F X does not require a separate configuration
  language" (p. 3).
- **Kinds** are `type | effect | (->> k …)` (§2.1, p. 6), so modules can
  abstract effects.
- **Interfaces are types.** `(moduleof (abs id k) … (desc id dx) … (val id
  tx) …)` is "the type of modules that export the abstract descriptions …,
  the transparent descriptions … and the values" (§2.2.6, p. 10), with
  width and depth subtyping.
- **Modules** are `(module (define-abstraction id k dx) …
  (define-description id dx) … (define id e) … (define-typed id tx e) …)`.
  Values "can be mutually recursive". "For each non-effect abstract
  description", `up-id` and `down-id` convert in and out (§2.3.11, p. 18).
  An effect abstraction has no conversions: it is simply opaque outside.
- **Using a module.** `(select e id)` names an exported description: "The
  effect of e must be pure to prevent type abstraction violation" (§2.2.9,
  p. 11). `(with e0 e1)` opens a pure module expression (§2.3.19, p. 23).
  `(extend e0 e1)` combines modules (§2.3.5, p. 15). Dot notation `id1.id`
  and `id1..id2` are sugar (pp. 27–28).
- **Files.** `(input literal)`: "The expression in the file named literal
  is produced as a value. No free variables are allowed in a input file,
  except if defined in the fx module" (§2.3.8, p. 17). The only unit of
  separate compilation is a closed expression, typically a module, linked
  by ordinary application.
- **The reference implementation** (`extracted/fx91/typecheck.scm` 633–695)
  spells it `load` (`token.scm` 354–360). It caches each loaded file's type
  and effect in `foo.fxt`, checked against the file's write date. It writes
  that cache only if no unification variable is left free. That is an
  interface file of exactly one type, generated by the checker.

Sheldon and Gifford, LFP '90 (`papers/lfp90.pdf`, PDF p. 5, §2.3 "Linking
and Separate Compilation"): "our system … is its own linking language. All
that remains is to provide a means for getting values out of a file system
… The file named in an input form must exist at compile time so that its
type can be known." They need identity for abstract types selected from a
file: "we must provide the illusion that the file system is immutable. Our
current implementation attaches the last update time to the input node."
Sheldon's thesis (`papers/mthesis.pdf`) lists the options for that
identity: compiled files only, user stamps, inferred max-of-stamps, or
checksums (p. 40). It adopts the first as "the simplest", and notes that
"Incremental compilation schemes for FX are the subject of current
research". It suggests interfaces kept in a separate file "packaged as a
transparent binding in another module" (p. 45). It also observes that
second-class systems that unbox by representation "necessitate recompiling
all users of a module when the module changes" (p. 9).

### FX-87

The FX-87 manual (MIT/LCS/TR-407) is not available
(`GiffordHistory/papers/README.md`). The interpreter's port is, at
`~/Dev/LangPlay/GiffordHistory/fx-lang/fx87/private/impl.rkt`:
- `load` reads a file's forms into the top level (7317–7364).
- `compile` writes a "rather crude FX 'compiler' or 'fasloader'" file of
  `(compiled-define name type value)` and `(compiled-pdefine name kind
  value)`: a type per definition and its type-erased value. Loading one
  trusts the types ("very few checks are made"), and compiling "has no
  effect on the current interpreted environment" (7376–7387, 7415–7530).
- Only `define` and `pdefine` are allowed in compiled files (7466).
- Top-level definitions are held until every free name is defined, then
  interned as one group (`try-to-intern`, 7599), which is the opposite of
  FX-26's "sees only those before".

**Example 11: FX-87's compiled file, for the counter's `step`.** The
shape is from the comment and `write-compile-define` (`impl.rkt`
7376–7410); the type is written in FX-87's `(subr F (T…) T)`, which FX-26
kept; the value is elided, since it is whatever the erased code prints as:

```
;; counter.fx                              ;; counter.fxfasl, written by (compile "counter.fx")
(define step (subr pure (int) int)         (compiled-define step (subr pure (int) int) …)
  (lambda ((n int)) (+ n 1)))
```

Loading `counter.fxfasl` binds `step` at that type without checking the
value against it. A C10 fragment (§2.7) is the same line with the value
replaced by cellular words and an import table, checked on link.

### Adopt, adapt, skip

| FX-91 / FX-87 feature                                  | Verdict      | Why                                                                                                                                                                  |
| ------------------------------------------------------ | ------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `input`: a closed file, its type known at compile time | adapt        | a unit is a file; but FX-26's files see their imports, not only `fx`, since the front end's files are not closed                                                     |
| `.fxt` type cache, stamped (FX-91 implementation)      | adopt        | exactly §2.2, with a content hash in place of a write date (Sheldon's own fourth option)                                                                             |
| `moduleof` interfaces as types; width subtyping        | adapt        | the `.fxi` is a list of `(name type)`; linking checks subtyping per export (§2.4); no module *type* yet                                                              |
| `(abs id effect)`: abstract effects                    | adapt, later | as bounded named effects (§2.3 c); unbounded ones would defeat licences                                                                                              |
| `define-abstraction` with `up-`/`down-`                | already      | `define-generative` (`docs/research/generative-types.md`); unit export lists supply the hiding it deferred to `private-regions`                                      |
| `select` needing a pure module expression              | keep in mind | only matters for first-class modules; second-class units are pure by construction                                                                                    |
| first-class modules, `with`, `extend`, dependent types | skip for now | the tooling needs no module values; they would make type identity a run-time matter that both checkers and heap images must agree on (`generative-types.md` 100–104) |
| FX-87 compiled files: types + erased values            | adapt        | a fragment with an import table; FX-87 trusted its types, where FX-26 should check them on link (C10)                                                                |
| FX-87's order-independent top level                    | skip         | FX-26 chose "sees only those before" on purpose (`recursion-and-initialization.md`)                                                                                  |

### Later work

| System                   | What it does                                                                                                                                                                                                                                                                | For FX-26                                                                                                   |
| ------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------- |
| SML modules (Leroy 1994) | SML "is defined as 'an interactive language', implying that users are expected to build their programs linearly in strict bottom-up order" (p. 109); manifest vs abstract types make separate compilation work                                                              | FX-26's REPL is in that tradition; transparent `define-type` across units is Leroy's "manifest" types       |
| SML/NJ CM                | "separate compilation and type-safe linking", "cutoff-recompilation" (manual p. 5); binfiles and stable libraries (§11, p. 31)                                                                                                                                              | §2.4's cutoff; a stable library is the front end's image                                                    |
| OCaml `.cmi`/`.cmx`      | `.cmx` holds "information for cross-module optimization"; `-opaque` drops it, reducing "compilation time, both on clean and incremental builds" (manual ch. "Native-code compilation", options); flambda optimizes across units "so long as the .cmx files … are available" | unfoldings in `.fxi`, optional; guards make `-opaque` unnecessary for correctness                           |
| GHC `.hi`                | interfaces with fingerprints per declaration; `-fomit-interface-pragmas`: importers "recompiled less often (only when M's exports change their type…)"                                                                                                                      | stamps; the trade GHC makes by flag, FX-26's guards make automatically                                      |
| MLton                    | "Whole-program compilation is an integral part of the design of MLton and is not likely to change"; it "often reduces or eliminates the run-time penalty that arises with separate compilation"                                                                             | the bootstrap and `fixpt build` may stay whole-program; separate compilation is for check time and the REPL |
| Chez Scheme libraries    | `enable-cross-library-optimization` includes information "to enable propagation of constants and inlining of procedures defined in the library into dependent libraries" (CSUG 9.5 §12.6); `compile-whole-program`                                                          | the same split: per-unit objects for development, whole program for shipping                                |
| Racket                   | modules instantiated after their requires, no cycles (Reference §1.1.9); recompiled when a dependency's SHA-1 "for its compiled form plus dependencies" changes (`raco make` §1)                                                                                            | initialization order and stamps                                                                             |
| Koka                     | effect types inferred and part of every signature; `alias` declarations name types and effects; `pub` marks exports (spec)                                                                                                                                                  | effect abbreviations as exports (`(effect parses)`), private by default is worth considering                |

Eff was not checked. Koka's handling of effect rows in its compiled
interfaces was not found in its public docs, so nothing here claims how it
works.

## 4. Recommendation

### Stages

| Stage | What                                                                                                           | Language change      | Gives                                                                          |
| ----- | -------------------------------------------------------------------------------------------------------------- | -------------------- | ------------------------------------------------------------------------------ |
| S0    | image of the loaded front end (and `standard26`), keyed by a hash of the twelve texts and the binary           | none                 | each session and test skips the front end's load; the most for the least       |
| S1    | checker snapshots at file boundaries, keyed by prefix hash; in memory first (tests), images for the FX-26 side | none                 | editing `regcode.fx` re-checks two files, not twelve                           |
| S2    | facts keyed by (file, offset) in both checkers and both compilers                                              | none                 | fixes "inlined `extract` gets field -1"; a precondition for everything after   |
| S3    | global and generative identity as (unit, name); `unit` header; `.fxi` written by both checkers, byte-equal     | the header, optional | files checked against summaries; the front end's hand prefixes become optional |
| S4    | link by `fits_old` per export (cutoff); `(globals-of U)` for private globals in interfaces                     | one region form      | an implementation change re-checks nothing downstream                          |
| S5    | unfoldings in `.fxi`, guards bound by implementation stamp                                                     | none                 | cross-unit inlining without recompilation for correctness                      |
| S6    | fragments: a unit's cellular words with import/export tables, checked on link (C9, C10)                        | none                 | compiled units on disk; machine code regenerated on load                       |
| later | bounded abstract effects; first-class modules if a client needs them                                           | yes                  | hiding what a unit reads; FX-91's module values                                |

S0 and S1 should come first. Stage S0's benefit can be measured before any
design is settled: time a session's startup and the suite before and
after. S2 is a bug fix in its own right.

### What each side needs (S2–S5)

- **Rust checker** (`check.rs`, `top.rs`): `Region::Global` keyed by
  (unit, name); generatives by (unit, name); `declare_ahead` per unit; an
  interface printer (types exist; effects sorted canonically) and reader
  (the `ENTRIES` path); `defs` recording which imports each definition
  used; the link check as `fits_old` over imports.
- **FX-26 checker** (`check.fx`): the same, rule for rule. `k-facts` gains
  a file. `check-more` stops forgetting earlier forms' facts, or facts move
  into the trees. Its interface print must equal Rust's byte for byte, a
  new agreement test beside `effect_summaries_agree`.
- **Rust compiler** (`cellular.rs`) and **FX-26 compiler** (`compile.fx`,
  `regcode.fx`): `c-genv-index` keyed by (unit, name); `c-inlines` entries
  gaining a unit, a stamp, and their facts; a guard's expected word taken
  from a link table rather than a heap pointer in the compiling session.
- **Lowering** (`lower.rs`): per-unit global prefixes, as
  `compile_program_as`'s `prefix` already does for one program.
- **Session/CLI**: `fixpt check|compile` writing `.fxi` beside an input;
  a REPL `,load` that links a unit by stamp; a REPL `,enter U` for
  redefining inside a unit.

### What the examples found

Writing the toys in today's FX-26 turned up these, each small:
- **No abstract type inside a product's type.** `stack-ops` takes `s` as
  a parameter, and every client is `poly` in it (Example 1). FX-91's
  `moduleof` has `(abs s type)`; FX-26 would need an existential, which is
  first-class-module territory.
- **Generative conversions are global.** `down-counter` works in any later
  form (Example 2). An export list is the fix, and the only thing
  `define-generative` still needs from units.
- **`define*` names private helpers.** `three`'s precise type lists
  `down-counter` and `up-counter` (Example 6), which is why §2.3 (b)
  matters as soon as units exist.
- **A client names the module's region**, `@tally`, unless it is
  polymorphic in the effect (Example 7).
- **Calling a global reads it**, so an abstract effect cannot cover a call
  of the procedure that has it; the caller adds `(read (globals tick))`
  (Example 7).
- **Printed types expand parametrized `define-type`s.** `use-stack` prints
  with `stack-ops` written out as its `productof` (`fixpt check` on
  Example 1). An interface printed so is correct but long, and loses the
  name; the `.fxi` should keep type abbreviations as entries and use them.

### Open questions for the user

1. **Scope first.** Is the target the front end's own edit–check loop
   (S0–S1 suffice), the test suite's time (S0), user programs split into
   files (S3 on), or the two front ends sharing units (`fx-rsmirror`,
   `fx-idiomatic`)? The last would argue for doing S3 before the split.
2. **Exports by default.** Should a unit with no `export` export everything
   (REPL-friendly, today's behaviour), or nothing but what it lists
   (Koka's `pub`, better hiding)?
3. **Precise globals across units.** Is (b), widening private names to
   `(globals-of U)`, acceptable? Or should interfaces qualify every name,
   (a), at the cost of interface churn? (c) is deferred unless you want
   hiding of effects now.
4. **Redefinition across units at the REPL.** May a form at the REPL
   redefine an imported global (the rule would re-check dependents in every
   unit), or only after `,enter` into the defining unit, as Racket
   restricts `set!` of another module's variables?
5. **Stamps.** Content hash (Sheldon's fourth option, GHC, Racket) or
   compiled-files-only (Sheldon's first, the FX-91 implementation's
   write date)? This note assumes a content hash.
6. **Unfoldings by default.** Should interfaces carry them always (GHC
   `-O`), or only with a flag? Guards make both correct; the difference is
   interface size and load time.
7. **Whole-program for shipping.** Should `fixpt build` and the bootstrap
   stay whole-program, as MLton and Chez's `compile-whole-program` do, with
   units only for development?
8. **FX-91 modules.** Is there any client in view for first-class module
   values or `(abs id effect)`, or do they stay out until one appears (as
   `docs/fx26.md` 815–819 says: "Modules … wait until the checker written
   in FX-26 spans more than one file")? This note would read that
   condition as met by S3's units, not by module values.

## Sources

On disk (read-only):
- `~/Dev/LangPlay/GiffordHistory/papers/fx91-report.pdf`. Gifford, Jouvelot,
  Sheldon, O'Toole, *Report on the FX Programming Language* (FX-91), the
  DVI of 1993-05-26 rendered by `dvipdf` (per `papers/README.md`). Pages 2,
  3, 6, 7, 10, 11, 15, 17, 18, 23, 27, 28.
- `~/Dev/LangPlay/GiffordHistory/papers/lfp90.pdf`. Sheldon and Gifford,
  *Static Dependent Types for First Class Modules*, LFP '90. PDF p. 5, §2.3.
- `~/Dev/LangPlay/GiffordHistory/papers/mthesis.pdf`. Sheldon, *Static
  Dependent Types for First-Class Modules*, S.M. thesis, MIT. Pp. 9, 31, 40,
  45.
- `~/Dev/LangPlay/GiffordHistory/papers/README.md`. The FX-87 manual
  (TR-407) is not available.
- `~/Dev/LangPlay/GiffordHistory/extracted/fx91/typecheck.scm` 633–695,
  `token.scm` 354–360, `README`. The FX-91 reference implementation's
  `load` and `.fxt` cache.
- `~/Dev/LangPlay/GiffordHistory/fx-lang/fx87/private/impl.rkt` 7317–7530,
  7599. The FX-87 interpreter (BETA-0), ported: `load`, `compile`,
  compiled files, `try-to-intern`.
- `~/Dev/LangPlay/GiffordHistory/extracted/fx91/tests.fx` 14–15, 116–117,
  142–146, 148–176. The FX-91 implementation's test programs, source of
  the FX-91 snippets in Examples 1, 2 and 5.

Examples (this revision):
- `docs/research/examples/separate-compilation/*.fx`, each checked with
  `fixpt check` and run with `fixpt eval`, `target/release/fixpt` of
  2026-09-29 11:01 (commit `e623b23` plus uncommitted work in the
  tree); Example 9's register code is `fixpt compile`'s.
- The FX-91 snippets, and the refusals quoted beside them, are from
  fixpt's FX-91 port, `fixpt --dialect fx91 eval`, same binary.
- The Rust snippet, compiled as a library with a client by `rustc 1.95.0
  (59807616e 2026-04-14)`.
- The SML, OCaml, Haskell and Racket snippets were written for this note
  and not compiled. Syntax as in the definitions and manuals already cited
  here (OCaml manual 5.2; GHC User's Guide; Racket Reference §1.1.9), not
  re-read for this revision.

Online (read 2026-09-29):
- Xavier Leroy, *Manifest types, modules, and separate compilation*, POPL
  1994, pp. 109–122: <https://xavierleroy.org/publi/manifest-types-popl.pdf>
  (p. 109 quoted).
- Matthias Blume, *CM: The SML/NJ Compilation and Library Manager (for
  SML/NJ version 110.40 and later), User Manual*, May 21, 2002:
  <https://www.smlnj.org/doc/CM/new.pdf> (p. 5 §1; p. 31 §11).
- OCaml manual 5.2, native-code compilation, option `-opaque`:
  <https://ocaml.org/manual/5.2/comp.html>. Flambda, §1:
  <https://ocaml.org/manual/5.2/flambda.html>.
- GHC User's Guide, separate compilation (interface files, recompilation
  checking): <https://ghc.gitlab.haskell.org/ghc/doc/users_guide/separate_compilation.html>.
  Optimisation flags (`-fomit-interface-pragmas`,
  `-fexpose-all-unfoldings`):
  <https://ghc.gitlab.haskell.org/ghc/doc/users_guide/using-optimisation.html>.
  Current version as served on 2026-09-29.
- MLton guide, `WholeProgramOptimization.adoc` and `Features.adoc`, at
  MLton commit `aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37`:
  <https://raw.githubusercontent.com/MLton/mlton/master/doc/guide/src/WholeProgramOptimization.adoc>,
  <https://raw.githubusercontent.com/MLton/mlton/master/doc/guide/src/Features.adoc>.
- Chez Scheme User's Guide 9.5: libraries §10.2, §10.5, §10.6,
  <https://cisco.github.io/ChezScheme/csug9.5/libraries.html>. Compiler
  controls §12.4, §12.6,
  <https://cisco.github.io/ChezScheme/csug9.5/system.html>.
- Racket Reference §1.1.9, modules and module-level variables:
  <https://docs.racket-lang.org/reference/eval-model.html>. `raco make`
  §1: <https://docs.racket-lang.org/raco/make.html>. Current versions as
  served on 2026-09-29.
- Koka language specification (`alias`, `pub`, `import`), at Koka commit
  `facb7932ce6871fdb063f762a304bd8238f35fba`:
  <https://raw.githubusercontent.com/koka-lang/koka/master/doc/spec/spec.kk.md>.
  The Koka book: <https://koka-lang.github.io/koka/doc/book.html>.
