# Loads, hidden globals, and facts by place: a review

The user's question (2026-10-15), after `TODO.md` §97's `load-input` bug:
the hidden globals of loaded files, and the reshaping of modules, sound
error-prone; should that part of fixpt be redesigned? This note says how
they work, what has gone wrong with them, why, and what could replace
them. Nothing here is decided.

## How loads work now

Every load of a path is one value, made once (`TODO.md` §68, decided
2026-10-08). A load is a *hidden global*, `%shared:K`, `K` the file's key
(`input:` before a `load-input`'s, then the path as resolved):

- **The Rust parser** (`parse.rs`, `parse_load`), at the first load of a
  key, makes a definition of its own, the *form*
  `(define %shared:K (load-module "P"))` (or `load-input`), and checks it
  with `top_defining` while the key is in `sharing_now`, the one state in
  which that load means "the file's module" rather than a load of it. The
  definition is *hoisted*: it runs before the form that loads the file.
  Every load is then the global (`load-module`) or the global's one item,
  `(with %shared:K input)` (`load-input`).
- **The front end written in FX-26** does the same in its own way: the
  Rust side reads each file once (`syn.rs`, `supply_loaded_in`) and gives
  the texts, at positions a billion apart per file (`LOAD_BASE_STEP`);
  the parser (`parse-loaded`) puts each new key's definition in
  `shared-pending`, which `parse-tops` places before the form.
- **The session** (`session.rs`), at the REPL and on the machines that
  check form by form, runs each hoisted definition as a form of its own:
  written back to text and given again to whichever front end and
  machine runs it. `shared_made` remembers which keys this session has
  made, so that the FX-26 front end is told not to make them again (base
  −1).
- **The checkers** let `%shared:` names through a loaded file's hidden
  scope, require the definition to be pure ("a loaded file is one value
  …"), and print no line for it. The compilers treat it as any global.
- **`module-parameters`**: the hidden global is a `plambda` over a
  `lambda` of no arguments, so each client's application makes a fresh
  module; each of the three at a place of its own.

## Reshaping

A module is a product of its values, by position. Where one is given
where a `moduleof` of fewer values, or the same in another order, is
expected, the checker records each wanted value's position in the given
module (`expect`: Rust `Checker::reshape`, FX-26 `k-reshape`), and the
compilers build the narrower product there. `extend`, `include` and
`hide` (§69) make reshapes too, by *paths* encoded as positions
(`RESHAPE_PATH`, `2^40 + (k << 20) + j`). The meaning is simple and
sound. What is fragile is how it is found again:

- **The Rust front end keys facts by expression** (`ExpId`):
  `NodeFacts.reshaped`, conversions, and the rest.
- **The FX-26 front end keys them by place**, an expression's start and
  end in the text (`k-reshapes`, `k-with-index`, the conversions
  `k-convert-at` notes, the effect summaries), and the FX-26 compiler,
  evaluator and register code look them up by place (`c-reshape-at`,
  `ev-reshape-in`). Rust's facts handed to the FX-26 compiler are turned
  into places too (`syn.rs`).

So two expressions must never share a place, and every expression the
parsers *make*, rather than read, needs a place invented for it.

## What has gone wrong

| when      | what                                                               | the cause                                                |
| --------- | ------------------------------------------------------------------ | -------------------------------------------------------- |
| `0c08e72` | a load given where a narrower module was wanted: the wrong reshape | the hidden definition and its use, one place             |
| DONE §69  | SIGSEGV: a parameterized module's closure reshaped                 | `plambda`, `lambda` and module, one place                |
| `7989f6f` | the FX-26 compiler slow on modules                                 | every reshape searched, by place, per expression         |
| `5b39a90` | `load-input` form by form: "unbound variable `input`"              | the hidden *form* means the module only in `sharing_now` |
| `5b39a90` | hid the above on the native machine                                | a checker's refusal taken as a decline                   |
| `5b39a90` | (first try) the scheduler cellular, not preempted                  | hidden definitions run per machine, differently          |

Two causes account for all but the fifth, which is a policy (see the
end):

1. **Facts by place.** Places are the FX-26 front end's identities for
   expressions, but they are not unique: made expressions have none of
   their own, and the fixes invented them (the load's keyword span for
   `input`, a zero-width `lambda`, positions a billion apart per file, a
   REPL form's positions past every earlier text, `2^40` for paths).
   Every new way of making an expression is a new chance to collide.
2. **A definition carried as source text whose meaning depends on the
   reader's state.** `(define %shared:K (load-input "P"))` is the file's
   module only to a parser in `sharing_now`; read anywhere else it is the
   file's value. It travels as text between front ends, and the session
   runs it differently on each machine (and the native machine compiles
   its initializer alone).

## Options

**A. An explicit form for a hidden definition.** The hoisted definition
becomes an internal form whose meaning is fixed, say
`(%loaded K "P" input?)`, meaning the file's module wherever it is read:
both parsers, both checkers, the lowering, the evaluator and the native
machine's definition path (which would compile it as what it is, or
decline it, by its form). `sharing_now`, `sharing-now` and the `%shared:`
prefix tests go. Small (both parsers, the session's hoisting, the native
path); removes cause 2; does nothing for cause 1.

**B. Loads that are not globals.** The session keeps a table of loaded
files, each made once (its key, its module's type, its value); a load is
an expression of its own, `Loaded(K)`, typed from the table and lowered
to a reference to the entry; nothing is synthesized or hoisted. Removes
cause 2 entirely, and the hoisting order with it. Large: a new
expression in both front ends, every compiler and machine, the REPL's
redefinition, images (a table to save), and `module-parameters`; and
what it gains over A is mostly that the hidden definition is not a
global, which is not what has broken.

**C. Expressions with identities in the front end written in FX-26.**
The FX-26 parser numbers each expression it makes (a field of the
expression, as Rust's `ExpId` is an arena index), and every fact (reshapes,
withs, conversions, effect summaries) is keyed by that number, not by
place; places stay only for messages. Removes cause 1: made expressions
need no invented places, and collisions cannot happen. Large but
mechanical: the expression datatype gains a field in the parser, the
checker's fact tables change key, the compiler, evaluator and register
code look facts up by it, and the Rust side's facts handed to the FX-26
compiler are keyed the same way. It also makes the reshape index's speed
fix unnecessary, and is what the two front ends agreeing would want
anyway: both keyed by expression.

## Recommendation

**A now, C next, B not.** A is small and removes the bug class that
appeared this week, whose cause is wholly in the hidden definition's
form. C is the deeper fix: three of the six were places, the slowness among
them, and
places will keep colliding as long as the FX-26 front end keys facts by
them; but it touches every FX-26 phase, so it deserves its own plan,
steps and measurements (the FX-26 checker's time on `peval` is the one to
watch). B changes the most and fixes nothing A and C leave.

Independently: the native machine should not treat a checker's refusal
as a decline (`TODO.md` §97); a refusal there is a disagreement between
the checkers, which the test suite should see. (Done, 2026-10-15: an
error saying so.)

## Decided: C first, as identities that are spans (2026-10-15)

The user's answer: C now, and the identity a span where a span is one,
with a count for the rest, so that what works keeps its representation
and made expressions have identities of their own. Not the place's two
integers with a count packed into one of them: the user ruled that out,
and the trees' types carry it instead.

- **An expression's identity is `(start end k)`**: where it starts and
  ends, and which of the expressions there it is. Every `exp` and `kx`
  node carries the three. `k` is 0 for the first at a span in a walk of
  the program's trees that takes each expression before what is in it,
  the forms in order (each after the hidden globals of the files it loads
  first); 1, 2, … for the others there, which the parsers made
  (desugarings, a loaded file's `input`, a generative type's conversions).
- **Numbered after the parse, not while parsing** (`parser-ids.fx`,
  `number-tops`): the parsers build nodes in different orders, but their
  trees are the same (`tests/parser.rs` compares them, `k` included), so
  a walk of the trees numbers both alike. The Rust front end keeps
  `ExpId`; `ids.rs` (`Kth`) says which `k` each is, so that the Rust
  checker's facts reach the FX-26 compiler keyed as it looks them up
  (`syn::rust_facts`).
- **Facts are keyed by identity, a product `k-at`**, not by place: the
  checker's (`k-fact`, `k-with-noted`, `k-reshaped`, the operator and
  checked-call marks), the compiler's tables (`c-by-at`, the plan's and
  the lifts' keys, where `c-span-key` was `a·2²² + b`), the evaluator's,
  and the words a body made (`c-made`). Places stay for messages.

What it costs, on `peval` (`fixpt bench`, back to back, alternated
three times, against `e1ae91cf`): `fx parse` 0.15 → 0.52 ms (the
numbering, a table of the spans walked; it rebuilds only what changes),
`fx check` 19.3 → 20.2, `fx words` 11.36 → 12.15; the other phases
unchanged. Counted exactly (cells, `probe_phases_as_register_code` on
`peval`), the work is not what grew: checking 103.7 → 104.2 M cells,
compiling 42.7 → 41.0 M (each lookup asks where an expression ends and
which it is only if something is noted where it starts), but the trees
are a field larger, and the words allocated 2–5 % more. A first version
looked each fact up by a key made for it, and asked all three of every
expression: `fx words` 14.0 ms, 1.51 G cells compiling the front end
where it was 1.38 G; now 1.37 G.

Not yet done, and what C makes possible:

- ~~The places invented so that made expressions would not collide~~
  (done, 2026-10-15): a made expression is at its origin's span, the form
  or the binding, branch or arm it was made for: `extend`'s `with`, a
  parameterized file's `lambda` (both of no width before), a
  `load-input`'s `input` (its keyword before), a quote's `%quote`, `nil`
  and vector (its opening parenthesis, closing one, `#(`), and `spawn`'s,
  `par`'s, `race`'s and `pselect`'s pieces (none wide, or from a branch
  to the form's end). And the Rust compiler keys what it decides by
  expression too, not by span: its plans, liftings, specialized copies
  and effect summaries. Positions that stay: a loaded file's base and a
  REPL form's (past every earlier text), which say which text was read,
  as the user's count for repeat reads would.
- ~~Fact kinds encoded in the fact's integer~~ (done, 2026-10-15): a fact
  is a `k-noted`, a datatype (`n-datum`, `n-summary`, `n-conversion`,
  `n-apply-shares`, `n-frozen-define`, `n-plain-fx`), not -500, -501,
  -502, -1000 - code, -1 - summary; and a copy kept to be inlined holds
  what was found of its `extract`s and `tagcase`s in their nodes, as
  `e-bloblet` holds its field, not in where they start
  (`c-resolved-at`). And what an operation takes is a datatype too,
  `k-datum` (Rust's `Datum`), not a field past `2^40` or `n << 32 |
  size`; the run time's array operand made and taken apart in one place
  each (`layout::array_operand`, `k-array-operand`).

**On cause 2, Sheldon said it first.** In Sheldon's system `(input
"file")` is an ordinary pure expression, and textual identity makes two
of them one module (`sheldon-combining-modules.md` §2): a load's
identity is what the expression says, the file, wherever it is read; and
a `with` body cannot be parsed before its module's type is known (§3,
pitfall 6), which is why the parsers need the loaded files. The hidden
global, defined by a parser in a state of its own, departed from that.
So A, if it is done, should be a load that is its own identity (its key),
a `Loaded(K)` resolved where it is read, rather than a hidden definition
of a better form: nearer B than A was put, but without the session's
table, the key being the expression's own.

## Done: a load is its key (2026-10-15)

As Sheldon's `input` is the file it names, a load is now its key, the
path resolved (`input:` before it for a `load-input`), wherever it is
read; its value the hidden global `%shared:key`, made once. What changed
is the hidden definition: it was `(define %shared:key (load-input
"path"))`, whose load meant the file's module only to a parser in a state
of its own (`sharing_now`, `sharing-now`, `parse-define`'s case for
`%shared:` names), and whose path was relative to a directory the reader
had to know. It is now `(define %shared:key (%loaded "key" "path"))`:
`%loaded` an expression whose meaning is fixed, the module of the file
the key names (the path kept only for what is said of the file), so
either front end reads it alike wherever it travels, the session's
form-by-form machines included. Gone with the state: the native machine's
decline of `load-input`'s hidden globals, whose initializer alone is now
the module too.

What stays: the hidden global, as the store that makes a load one value,
made once (option B would make that a table of the session's); and the
front end written in FX-26 finds a file read for it by where its load
starts, as Rust supplies them.

## Decided: identity by position, spans for provenance (2026-11-06)

The user's reading: a source location serves two roles, provenance (where
to edit) and a proxy for what defines a fact, the expression and its
context. Macros break the proxy: a template's nodes share the use's span,
and an argument placed twice is one span at two positions. So the two
roles are split.

- **An expression's identity is its position**, `(form n last)`: the form
  a number given to each top-level form as it is checked (a program's in
  order, a loaded file's, its hidden globals, each REPL entry), never
  reused; `n` the expression's number in the walk `number-tops` and `Kth`
  already make, each before what is in it, from 0 in each form; `last`
  the greatest number inside it. `x` is inside `e` when `n(e) ≤ n(x) ≤
  last(e)`. Numbered on the parsed trees, after the parsers' rewrites, so
  a made expression is numbered where it is, with no count at its
  origin's span.
- **Not a summary of expression and context.** Facts keyed by a summary
  are sound only if it holds all the checkers consult (expected type,
  narrowings, the `allof` member, masks, what shadows `#%fx`'s names),
  computed alike by both; a position is the finest such key and needs no
  proof. A summary may come later as a memo over it, where measurement
  shows repeated checking in one context.
- **Spans are provenance**, for messages and edits. An argument's nodes
  keep its span; a template's nodes their own place in the
  `define-syntax`; each expanded node an expansion record (the macro, the
  use's span, the expansion it is in), carried by the span. An error
  found in both copies of an argument is said once.
- **Replaces**: `k-at`'s `(start end k)` in the FX-26 front end; `Kth`'s
  table (`ExpId` to the position, so the Rust checker's facts reach the
  FX-26 compiler alike); in the Rust checker, the places that read spans
  as identity or containment (`check_allof_lambda`'s lambdas and dead
  arms, `split_tries`' kept facts, `lambda_cert`'s free names, blame by
  `err.span == span_of(x)`, `literal_value`).
- **Order**: identity first, in both checkers, measured on `peval`; then
  provenance and the printed expansion's source map; then `(many σ)`
  (`typed-macros.md`).
- **Later, not this story**: caching macro expansion steps.

## Done: identity by position, in both front ends (2026-11-06)

- **`k` is the walk's number** (`parser-ids.fx`'s `number-tops`, `ids.rs`'s
  `Kth`): every expression's, from 0, in one call of the front end, the
  scope the compiler's tables have (`c-set-facts!` makes them anew). So
  the identity `(start end k)` keeps its shape and every comparison of it
  stands; `k` alone tells two apart, and the start and end beside it are
  provenance, kept in it for the tables hashed by where an expression
  starts. No form's number is needed: nothing keyed outlives a call.
- **What is inside an expression is found by structure**: in the Rust
  checker, `ids::subtrees` and `ids::parents` (an `allof` lambda's facts
  and lambdas, the arms and branches a member skipped, a split call's kept
  facts, a certificate's references and enclosing lambdas); in the
  checker written in FX-26, skipped arms and branches as intervals of
  walk numbers, `(k-kth x)` to `(k-last-kth x)` (`k-skipped?`), and a
  dead arm counted by its body's number, not its span. `Checker::extent`
  and `k-extent`, which widened an `if` made of a `cond` to its clauses,
  are gone.
- **Cost, on `peval`** (`fixpt bench --tables compile --front-end`, release
  builds, alternated three times, against `5bffbbbb`): `fx parse` 1.20 →
  0.55 ms, one count where a table of counts by span was; `fx check` and
  `fx words` unchanged (52, 26.5 ms). Compiling the front end: `fx parse`
  350 → 297 ms, and `fx words` 2455 → 2033 ms, which is not explained
  yet.
- **Provenance** (2026-11-06): a `Span` has an `expansion`, the use of a
  macro whose template made the text (0: none), recorded in a table of
  the process's (`fixpt_read::record_expansion`, `expansion_trace`), each
  use's own span saying which made it in turn. A template's parts are at
  their place in the `define-syntax`; an argument's keep theirs. `fixpt`
  says an error's place, then each use that made it, innermost first, on
  the lines after (`located`; `macros/nested-error.fx`).
- **Not done, and why**: the printed expansion's source map. The checker
  written in FX-26 checks the printed expansion, so its places are in that
  text; but its error is said only where the two checkers disagree (where
  both refuse, the Rust checker's is said, at its provenance). It matters
  once the expander is the front end written in FX-26's, which reads
  places from the text it expands; `write_syntax_mapped` is there for it.
- **Blame by span that stays**: `synth_app_split`, where an error inside an
  argument that is not a variable ends the split. Errors raised there are
  of the call's own parts, so an error whose span is inside an argument's
  is in that argument's text, or in a copy of it another argument holds:
  in its text either way. A copy is made only where a macro places an
  argument twice, which waits for `(many σ)`; that both checkers then
  agree is for it to show.
- **A REPL session is one text** (2026-11-06, the user's choice over a
  file number per entry): every entry is read into the session's text,
  past those before (`Fx26Session::read_entry`; `Checker::read_in_from`
  reads from where the entry starts), so a span of anything an entry read
  says which entry it is in (`Fx26Session::place`): a template's, in the
  entry that defined its macro; a pending entry's, in its own. `FileId(0)`
  keeps its meaning, the program, which at the REPL is the session's text,
  as the evaluator's positions are past every text before (`eval_base`).
  What is typed and not yet entered is read past it too, and kept nowhere
  (`read_trial`).

## Decided: three keys, validated (2026-11-06)

The user's direction, after a content digest was set aside (equal
occurrences are what had to be told apart): a key by digest of the
occurrence's context and the session's state, the reference; a cheaper
one by path and digests, checked against it; and the cheapest, a path
alone, for ordinary runs, the others only where debugging. All modes in
both front ends.

| mode | key | made of |
| --- | --- | --- |
| `full` | `(S, Z)` | `S` the session's state where the form is checked, a digest; `Z` the occurrence's context in its form, a zipper's digest |
| `digest` | `(S, F, k)` | `F` the form's digest, `k` the occurrence's number in a walk of the form |
| `path` (default) | `k` | its number in a walk of every form the session reads, continuing from one reading to the next, as places do |

- **`FIXPT_FACT_KEYS=path|digest|full|validate`.** `validate` makes all
  three and checks: `digest` against `full`, that they tell the same
  occurrences apart; `path` against `full`, that equal `path` keys are
  equal `full` keys (the converse failing is sharing lost, counted, not
  wrong); and `full` against the facts, that occurrences sharing a `full`
  key have the same facts, up to the fresh names a check makes (renamed in
  order of appearance; what that cannot settle said, not guessed). The
  last tests the reference itself: what `S` leaves out that checking
  reads shows as two contexts with one key and two answers.
- **`S`** is folded as the session changes: each definition, type,
  effect, generative type, convention, macro and file loaded, types by
  `ty_digest`. **`Z`**: each subtree's digest bottom up, then each node's
  context from its parent's, the parent's form, its place among its
  siblings and their digests. Provenance (places, expansion records) is
  in no digest.
- **Assumed, for the user to overrule** (their questions 2 and 3 not yet
  answered): `full` is the syntactic context and the session's state, not
  the checker's state within a form (the expected type, the `allof`
  member), which checking, deterministic, makes of them; facts compare
  up to fresh names as above.
- **Stages**: `path` first (the walk's count continuing across readings
  in both front ends and the bridge; places no longer in a key); then `S`
  and `F`; then `Z`; then `validate`, in the Rust checker and in the one
  written in FX-26, and a test of every program under it.
- **Stage 1 done, `path`** (2026-11-06): every tree node (`exp`, `kx`) has
  a fourth integer, its reading, beside its number `k` (the user's
  choice over packing the two into one integer: no encoding to get
  wrong). A reading is a digest (below; first a count, which is
  replaced). `k-at` is
  `(start end k reading)`; identity compares `k` and the reading
  (`k-at-is?`, `k-at=?`, `ev-at-is?`, `r-same-exp?`), every function that
  takes `a b k` takes the reading after `k`, and the compiler's tables
  are by `k`, not by where an expression starts. The checker written in
  Rust numbers within the reading, its facts of reading 0, since it checks
  before the FX-26 parser reads the text; the compiler gives them the
  reading of the trees it compiles (`c-set-facts!`'s reading,
  `c-reading-of`, `c-absolute-at`). A copy kept to be inlined, from an
  earlier reading, keeps that reading: its lookups miss, as they must.
- **A reading is a digest, not a count** (2026-11-06, the user's call,
  after the count proved the trouble they had foreseen: a global in the
  FX-26 image, bumped by every parse, so a reading's number told how many
  parses that image had made, and the Rust side, which counted nothing,
  would have had to own a count both agreed on). A reading is
  `reading-of(s, trees)` (`readings.fx`; `ids::reading_of`, the same
  function over the Rust reader's trees, `parser.rs`'s
  `the_readings_agree`): `s` the state of the session the text is read
  in, folded with the trees the text reads as into 40 bits, never 0.
  `parse-program` and `number-tops` take it; nothing is counted. Whoever
  reads the same in the same state makes the same reading, and asks no
  one (`a_reading_is_its_trees_not_a_count`).
  Of the trees, not the text (the user's point, the same day): the full
  key validates the cheap one, where the cheap key says "the same" the
  full must too, so a full key finer than meaning reports bugs that are
  none. So no space, comment, spelling the reader makes one tree of
  (`#t`, `#true`), or position tells readings apart
  (`a_reading_is_not_of_how_its_text_is_written`); what the parser tells
  apart the digest does, `(a . (b c))` from `(a b c)`. Each tree folds its
  kind's mark, then its pieces: a name's, string's or number's characters
  (an integer's decimal digits, a float's bits, a ratio's numerator and
  denominator in lowest terms, a bytevector's bytes) ended by a mark, a
  list's elements then its end. Nothing the reader reads is left out:
  where FX-26 could not reach a datum's pieces (a bytevector's bytes, a
  ratio's parts), the standard gained what reaches them
  (`datum-bytevector-length`, `datum-bytevector-ref`, `datum-rational?`,
  `datum-numerator`, `datum-denominator`). The state
  `s` is kept by what owns the state it stands for (stage 2a, below, for
  where, and which texts advance it). A syscall's definitions, which
  the checker makes, are the reading of the text they are made of, no
  trees (`text-reading-of`), in state -1.
- **Stage 2, decided** (2026-11-07, the user's choice of "both,
  validated"): two `S`. The reference, `S` by trees: the session's state
  is the reading of the last text its checker kept, so it is of the trees
  of every text kept, in order; a text refused, or tried, leaves it as it
  was. The cheaper, `S` by types: each definition's name and type, each
  type's definition, macro, load and convention, by a type digest written
  in both languages; checked in `validate` against the facts, as `path`
  is: where two occurrences share an `S`-by-types key and not an
  `S`-by-trees one, their facts must agree, or `S` by types has left out
  what checking reads (bodies do matter: inlining, frozen definitions,
  certificates). Then `Z`, then `validate`.
- **Stage 2a done, `S` by trees** (2026-11-07), and then, the user's
  choices the same day, per form, `Z` of the path, each mode's keys in
  both front ends:
  - **A form's reading** (`readings.fx`'s `form-reading`, `ids.rs`'s
    `form_reading`, tested alike): the session's state before it, folded
    with the switches that change what the checker finds (the program's
    convention, `globals-effects`, `defer-reruns`, `syscalls`, inside a
    module file built in: `ids::Settings`, `checked-settings`, tested to
    write them alike), its trees, and each file it loads first, by key and
    trees, in the order of the keys (the trees of a `load-module` form are
    not the file's). The state after a form is its reading, so a session's
    state is the same however its forms were split into texts
    (`a_state_is_its_forms_however_they_are_split`). Where a checker
    begins, the standard environment's state, its trees' reading
    (`standard-state`, `standard_state`); a staged step's text is read
    with the reps of the type it is checked against and of the types its
    names are given folded in (`with-reps`, `with_reps`).
  - **Each expression's key** (`parser-ids.fx`, by the mode `keys` names;
    `FIXPT_FACT_KEYS`, `ids::mode`): `path`, `(n, 0)`, `n` its place in
    the parser's walk of every text it has read, which goes on from text
    to text and is never given twice (a text refused still advances it):
    the parser's own count (`walked-total`), as long as its front end
    lasts, the key space its tables are of; `digest`, `(n, R)`,
    its place in its form's walk and the form's reading; `full` and
    `validate`, `(Z, R)`, `Z` the path's digest down from the form (each
    place among its parent's, folded onto the parent's: a zipper's
    information, since the form fixes the siblings). Identity compares
    the two fields whatever the mode.
  - **Where `S` lives**, each where the checker's state is, each left by
    a text its checker kept (a refused text, or a try, leaves the state as
    it was): `Fx26Session::own_state`, each entry that reads taking an
    `ids::State` and leaving the state after in it (`syn.rs`); a staging
    session on the Rust checker (`sessions.rs`'s `kept`, `State::keys`, as
    `session-compile` takes them); a staging session on the checker
    written in FX-26 (the conductor's `step-state`). `parse-program` takes
    the keys and gives the state after, the count it began at, and the
    keys it gave, in order. The count was first each caller's too; but a
    caller that began again at 0 (a program compiled alone, a test's) gave
    another program's numbers again in one front end, whose kept copies
    to inline outlive a call: so it is the parser's.
  - **The Rust checker's facts** are numbered by their place in the walk
    (reading -1, `rust_facts.rs`), since it checks before the text is
    parsed; the compiler gives each the key the parse gave there
    (`c-absolute-at`, from the parse's numbering: in `path`, that place
    past the count before; else the key given there). `and_after`, which
    joins the facts of several texts, puts each walk after the one before.
  - **The evaluator's own forms** (`stage`'s code, a session's forms, run
    among the program's facts: `ev-withs`, `ev-facts`) are numbered past
    any number of a program's, as their places are past any of a
    program's (`ev-keys`, `ev-stage-base`): no session walks 10¹²
    expressions, each made in the heap. I had taken them for safe at 0,
    since nothing they find is kept; but they are looked up in the
    program's facts, and at 0, in `path`, one took a program's `with` for
    its own (`stage.rs`'s `a_process_stages_while_another_runs`).
  - **`validate`** (2026-11-07), each mode's keys made beside the full
    one, which every expression is keyed by: as the walk gives them,
    each cheap key, `path`'s and `digest`'s, recorded with the full key
    of its expression, as long as the parser lasts, and a cheap key
    given again with another full key the parse's error
    (`parser-ids.fx`'s `validated!`); as the compiler takes facts, of
    either checker (`c-set-facts!`), each full key's facts, `with`s and
    reshapes, by a digest of them in no order, recorded as long as the
    compiler lasts (one table per front end, the user's choice over one
    for the process), and a key met again with other facts the
    compiler's error (`c-validate-facts!`). A convention's variable is a
    variable in the digest, its number aside, as a fresh one is; a
    staged fact's rep, a cell only the runtime reads, by a digest the
    checker makes of its bytes (`n-staged`'s fourth field). Tested:
    each detector (`tests/validate.rs`), and every test program compiled
    by one front end under `validate`, each full key met again with the
    facts it had. `S` by types is tabled (the user, 2026-11-07;
    `TODO.md` §215).
  - **Its first finding** (2026-11-07): a definition checked again after
    a name it uses was redefined (`k-rerun`) was checked on its trees as
    first read, keys and all, in the state after the redefinition: its
    facts changed (it broke) under the keys its first check's facts had,
    which a copy kept to inline has too. Now a definition checked again is
    read again first (`read-again`, the parser's own walk, so its count):
    its reading of the form's old reading and the state the text being
    checked left (`read-again-reading`), its keys new. Checking may so
    write the syntax's region, `@s` (`k-tag`): the parser's count goes on.
    `a_definition_checked_again_is_read_again`.
