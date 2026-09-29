# Suspected unsoundnesses and proof assumptions

Research note, 2026-09-27. Companion to `docs/research/soundness.md` and
`docs/research/soundness-regions.md`. Each item is either a place where the
checkers' rules look unsound against the semantics those notes give, or an
assumption the proof needed that the implementation may not meet. Every
item names files and lines, and, where one was run, a small program and
what the tools did with it. Programs were run with the release binary
under the timeout wrapper. Line numbers are as of this note; `check.rs`,
`infer.rs`, `sizes.rs`, `terminate.rs` and `check.fx` were being edited in
another session, so they may have drifted by a few lines — search for the
named function.

A caveat on severity: `spin` is a claim about termination, not about type
safety. An unsound `spin` (F1, F3, F5) means a procedure typed `pure` can
loop; it cannot corrupt the store. F2 is the only item that looks like it
can read freed memory, and even there the type system's own escape rule
seems to save the concrete runtime (see F2). Read these as "the proof of
T5 fails here, and here is why", with F2 flagged for a closer look.

## Status

| item | status                                                                                                                                                                                                                                                                                      |
| ---- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| F1   | fixed: `known` is by binding (its place in `env`; in `check.fx`, a flag beside each binding), forgotten as its scope ends                                                                                                                                                                   |
| F2   | fixed: reading data frozen into a place is an effect on it, masked where the place is not seen; only heap-frozen reads are pure                                                                                                                                                             |
| F3   | fixed: a `cwcc` call says `spin` unless its receiver's continuation can only be called while `cwcc` runs; a kept composable continuation is refused by the knot rule                                                                                                                        |
| F4   | fixed: a size binder may be `finite` only as the size of at most one parameter's own `(nlist T n)` or `(nat n)`, and nowhere else supplied                                                                                                                                                  |
| F5   | fixed: past the depth bound, the self-application test says the procedure may loop                                                                                                                                                                                                          |
| F6   | fixed: `no-escape` only where the value is first-order data                                                                                                                                                                                                                                 |
| F7   | fixed: a continuation keeps how many regions were live when taken; reinstated whole, it ends those entered since, in both cellular[^cellular] machines                                                                                                                                      |
| A1   | holds for the constructs present (the syntactic rule is the stronger)                                                                                                                                                                                                                       |
| A2   | fixed: a generative type whose representation is one of what it is given is no constructor for the recursive-type rule                                                                                                                                                                      |
| A3   | holds by construction: every `datum` is made by FX-26's own constructors (fresh pairs of acyclic data; lists checked proper, cycle-safely) or its reader; the host passes no datum in. The contract for Scheme code calling an `fx:` global directly is that a `datum` it passes is acyclic |
| F8   | fixed: a `nat` binding's size may be forgotten only where the escaping type gives it back (no negative or invariant occurrence); otherwise an error. Both checkers. Test `sizes/nat-forget-taken.fx`                                                                                        |
| F9   | fixed: a `cwcc` call also says `spin` when its receiver's latent effect has a `comefrom`, since a continuation captured inside it could carry a call of `k` past `cwcc`'s return. Both checkers. Test `terminate/cwcc-captures.fx`                                                          |
| F10  | fixed (2026-09-29): a size binder solved from `n + k` against a size `s` is `s - k`, and must be shown no less than 0 by the facts in scope; `head` of an empty list solved `n = -1`. Both checkers. Tests `sizes/solved-*.fx`                                                              |
| F11  | fixed (2026-09-29): `apply` gave a `vlambda` the caller's list, typed `acyclic` though writable; a `set-cdr!` made it cyclic and a `pure` walk looped. `apply` now copies (a cycle is an error) unless the list is at `acyclic`. Tests `run/apply-fresh.fx`, `native/apply-cyclic.fx`       |

**Re-verification of F1–F7, A2, A3 against d83face** (fresh offline build,
2026-09-27). F1: the name-shadowing probe (`known.fx`) is now rejected
(`omega` is `(subr spin (T) int)`). F2: a closure reading place-frozen data
now carries `(read (finite p))` and its escape from `letrena` is refused
(`frozen-eff.fx`); the same read masks to `pure` when used internally
(`frozen-internal.fx`) and heap-frozen reads stay `pure` (`frozen-heap.fx`).
F3: a stored full continuation is rejected `spin` (`cwcc-store.fx`), and the
honest stored composable is refused by `no_knot` (`comp-min2.fx`); but see
F9. F4: `(proj f finite)` with `f` sizing two parameters, or one parameter's
inner list, is refused (`skolem-neg.fx`, `f4-gen.fx`, and the crate's
`finite-two-args.fx`/`finite-inside.fx`/`finite-proj.fx`), while the
map-shaped one-parameter case is accepted (`f4-ok.fx`,
`finite-one-arg.fx`); but see F8. F5: the depth-`>64`
self-application (`deep.fx`) is rejected `spin`. All as intended.

Tests: `tests/programs/terminate/known-shadowed.fx`,
`known-let-shadowed.fx`, `deep-self-application.fx`, `cwcc-kept.fx`,
`cwcc-escape.fx` and `composable-kept.fx`; `tests/programs/sizes/finite-*.fx`;
`tests/programs/regions/frozen-read-effect.fx`;
`tests/programs/generative/unguarded-cycle.fx`; `tests/run.rs`
(`no-escape`); `tests/register_code.rs`, `a_throw_ends_the_regions_it_leaves`
(`run/region-throws.fx`).

## F1 — "known" procedures are exempt from the spin test by name and type

**Where.** `infer.rs:469–488` (`may_spin`), with `known` populated at
`check.rs:427` (letrec), `check.rs:461` and `infer.rs:203` (a `let` of a
lambda). `is_standard` at `check.rs:323–325`. The FX-26 checker: `check.fx:498–513`
(`k-known-callee?`, `k-may-spin?`), `k-known` at `check.fx:311,358`.

**The rule.** `may_spin` returns `false` for a call whose operator is a
"known" binding — one in `self.known` or standard — so the
self-application test (`cyclic`) is skipped for it. `known` holds a
`(Sym, TyId)` pair.

**Why it looks unsound.** The exemption is meant for code the checker has
seen and is checking. But `known` is keyed by name and type, and a shadowing
binding of the same name and type is treated as the seen one. A first-class
procedure of a self-applicable type, bound to a name that a known lambda
also used, would be called without the `spin` the type otherwise forces.

**Probe.** `known.fx`:

```
(define-type T (subr pure (T) int))
(define w T (lambda (x) 0))
(define omega T (lambda ((w T)) (w w)))     ; the parameter is named w
omega
```

Accepted, `omega : (subr pure (T) int)`. Inside `omega`, the call `(w w)`
has operator `w`, the *parameter*; but `known` contains `(w, T)` from the
top-level `w`, so `may_spin` says false and no `spin` is added. `known3.fx`
runs `(omega omega)` and it exceeds the step limit while typed `pure`.
Compare `known2.fx`, which names the parameter `x`: there `(x x)` is not
in `known`, `cyclic` fires, and the checker reports
`(subr spin (T) int)` and rejects the `pure` signature.

**Fix.** Key the exemption by binding, not by `(name, type)`: the checker
already distinguishes bindings by their position in `env` for `acyclic?`
and `certify-length` (`check.rs:684–685`, `infer.rs:322`). `may_spin` should
ask whether the operator resolves to a binding it is currently checking or
a standard one, not whether some binding of that name and type is known.
In the proof (T5) the exemption must refer to the actual binding
(`soundness.md` §5, point 4).

## F2 — reads of frozen data are dropped from the effect

**Where.** `check.rs:312–321` (`frozen`), called from `synth`
(`check.rs:305–310`); the mask keeps frozen atoms only to re-drop them at
`synth` (`check.rs:702–703`, `mask` returns them; `frozen` filters). FX-26
checker: `k-frozen`, `check.fx:3425–3429`; `k-drop-frozen`,
`check.fx:3417–3422`.

**The rule.** `frozen` removes `read`, `alloc` and `await` atoms on a
`(const p)`/`(finite p)` region: "reading it and making it are pure". So a
closure that reads frozen data allocated in a place has a latent effect
with no atom on the place, and — since `regions_in` does report the place
of a frozen region (`check.rs:822–827`) — the escape check
(`close_region`, `check.rs:564–578`) is what must stop it leaving.

**Why it looks unsound in the abstract.** In K26 the atom `read (const p)`
is the only part of the effect that ties such a closure to `p`'s lifetime;
Lemma 4.8 of `soundness.md` uses it. Dropping it means the effect no
longer records that the closure touches `p`.

**Probe, and why the runtime survives.** `frozen-escape.fx` builds a pair
in a place, freezes it, and returns a closure `(lambda () (car x))` reading
the frozen pair; a second function reuses an arena in between; then the
closure is called:

```
(letrena p (let ((x (letfreeze (r p) (the (pairof int int r) (rcons p 1 2)))))
             (lambda () (car x))))
```

The checker *rejects* the escape: the returned closure's type still
mentions `(const p)` (frozen data mentions its place), and `regions_in`
reports `p`, so `close_region` refuses the value of `letrena p`. Wrapping
the closure so its type hides `p` was not possible without also hiding the
data. So the mention-based escape rule (`close_region`) catches what the
dropped effect no longer records, and the concrete programs are safe. When
`letrena` is replaced by `letreap`, or the pair by a frozen bloblet
(`blob-escape.fx`), the checker still refuses the escaping closure.

**Status.** Not a demonstrated unsoundness: every attempt to build one was
caught by the escape rule. It is a fragility: safety here rests entirely
on `regions_in` reporting the place of every frozen region in the value's
type, in every construct that lets a value out (currently only
`close_region`). If a future construct drops or replaces a mention
without re-adding the place (as `letfreeze` does for the region it
freezes), the missing effect atom would no longer be backed by anything.
The proof (K26) keeps the atom (rule FrozenRead) so the effect alone
suffices; the checker should keep it too, or the invariant "every
value-escaping construct consults `regions_in`" must be stated and
maintained.

## F3 — a continuation captured, stored and re-entered loops with no spin

**Where.** `standard.rs:50–58` (`cwcc`); the store operations
`standard.rs:27–31`, I-cells `docs/fx26.md` "I-cells". The `spin` rules do
not treat re-entering a stored continuation as possible non-termination:
`may_spin` (`infer.rs:469–488`) looks only at the operator's binding and
type-cyclicity; `no_knot` (`check.rs:1190–1274`) looks for a procedure
whose latent effect reads its own region.

**The rule that is missing.** A continuation of type
`(subr (goto @k) (int) void)` (what `cwcc` hands its argument) does not
read any region when *called*: calling it jumps. So storing it in a cell
and calling it later is not a store-knot (no `read` of the cell's region
in the callee's latent effect), and it is not self-application. Nothing
adds `spin`.

**Probe.** `cwcc-loop.fx`:

```
(define loop (subr pure () int)
  (lambda ()
    (let ((c (the (icell (subr (goto @k) (int) void) @c) (make-icell))))
      (begin
        ((proj (proj (proj cwcc @k) int) (write @c))
          (lambda ((k (subr (goto @k) (int) void))) (begin (icell-put! c k) 0)))
        ((icell-get c) 0)))))
(loop)
```

The continuation `k` re-enters the point after `cwcc`, which calls
`(icell-get c)` and jumps again: an unbounded loop. The checker accepts
`loop : (subr pure () int)` (the effects on `@k` and `@c` are masked, the
cell being private), and running it exceeds the step limit on both the
lowered and cellular back ends.

**Assessment.** This is a real hole in the `spin` analysis: a `pure`
procedure that does not terminate. It is not a memory-safety problem; the
loop is well behaved but for ending. The general fact is that `comefrom`
(and a `goto` to a captured continuation) can encode recursion. The proof
(T5, `soundness.md` §5 point 3) states that a captured continuation that
can be stored and called must be treated as `spin` unless something rules
out its second use. FX-26's answer elsewhere is the answer-type-fixed tag
and delimited control; full `cwcc` with a stored continuation escapes it.
Options: give a stored/duplicable continuation `spin` when it is named
anywhere but as a direct callee (as recursive-group members are,
`check.rs:331–336`), or require the region of a re-enterable continuation
to behave like storage in the knot rule.

## F4 — size binders are instantiated with `finite`

**Where.** `infer.rs:809–811` (an unsolved size binder defaults to
`Size::Finite`); `check.rs:366–368` (a `proj` argument `finite` given for
a size binder becomes `Size::Finite`). FX-26 checker: `check.fx:3000`,
`check.fx:2730,2787` (`dz (sz-finite)`).

**Why it is unsound for exact sizes.** `finite` is the top size, "some
length". Substituting it for `n` in `∀n. (nlist t n) (nlist t n) → …`
lets the two arguments have *different* lengths while both read as
`(nlist t finite)`, and lets a `(nat n)` result be claimed for a value
whose size is not `n`.

**Probe.** `nat-neg.fx`:

```
(define g (poly ((n size)) (subr pure ((nlist int n) (nat n)) nat))
  (plambda ((n size)) (lambda (xs k) (if (null? xs) 0 (- k 1)))))
(define one (nlist int finite) (cons 1 nil))     ; length 1, but typed `finite`
((proj g finite) one 0)                          ; g gets a `(nat finite)` = the value 0
```

`g` computes `(- k 1)` in the else branch (the list is non-empty), where
`k : (nat n)` and `n ≥ 1` should hold. Instantiated at `finite`, `k` is
`(nat finite)` = plain `nat`, and `0` is accepted for it although the list
has length 1. The call returns `-1`, printed `-1 : nat`. So a `nat`, which
`docs/research/sizes.md` says is "never negative", holds `-1`.
`nat-loop.fx` feeds that `-1` to a `pure` countdown `(if (= k 0) 0 (down (- k 1)))`
and it runs past the step limit — a second way to reach F3's symptom, this
time with no continuation, purely from a false size fact.

**Consequence for the proof.** Invariant (I6) of `soundness.md` is false
in the checker: a `(nat k)` value need not equal `k`, and size-change's
use of `nat` as a well-founded measure (a countdown on a `nat`) loses its
lower bound. So C3 is false, and T5's clause 2 (size-change soundness)
fails. `soundness.md` §4.9 gives the sound reading: a size binder ranges
over naturals only, and `finite` is an existential to be *opened*, not
substituted; a `∀n.` used at `finite` must open the existential of a
single occurrence, not replace `n` everywhere.

## F5 — the self-application test gives up at depth 64

**Where.** `infer.rs:511` (`if path.len() > 64 { return false; }` in
`cyclic`). FX-26 checker: `check.fx:3460` (`(> (k-length path) 64) #f`).

**The rule.** `cyclic` walks the operator's type looking for a cycle
through a parameter; past 64 nodes it returns `false` ("not cyclic"),
which makes `may_spin` say the call cannot self-apply, so no `spin`.

**Why it looks unsound.** A self-applicable type whose cycle first closes
deeper than 64 constructors is reported non-cyclic, and a looping
self-application through it is typed without `spin`.

**Probe.** `deep.fx` builds `T = (subr pure (P) int)` where `P` nests 70
`productof` wrappers around `T`, and writes `omega` that unwraps its
argument 70 times and self-applies:

```
(define-type T (subr pure ((productof (a (productof (a … T …)))) int))
(define omega (subr pure () int)
  (lambda () (let ((w (the T (lambda (p) (let ((f (extract … (extract p a) … a))) (f (product (a …(a f)…))))))))
               (w (product (a …(a w)…))))))
(omega)
```

Accepted (`exit 0`), and `omega` exceeds the step limit. The same shape at
depth 3 (`shallow.fx`) is rejected: `omega` is reported
`(subr spin ((productof (a (productof (a (productof (a T)))))) int)` and
the `pure` signature refused. So the only difference is the nesting depth
crossing the cutoff.

**Fix.** The cutoff exists to bound the walk. Because types are cyclic
graphs, the walk terminates on its own once it memoises visited
`(node, by_param)` pairs — `cyclic` already keeps `path` and checks
membership (`infer.rs:506–510`); a visited-set keyed by `(TyId, bool)`
would make the 64 bound unnecessary and the answer exact. If a bound must
stay, exceeding it should be conservative — return `true` (assume it may
loop), not `false`.

## F6 — the `no-escape` fact for a value a closure still holds

**Where.** `check.rs:711–714` (mask sets `no_escape` when allocation was
removed); `lower.rs:400–401` emits `(no-escape)`; the comment
`check.rs:135–136` and `lower.rs:22–24` read "nothing they allocate
outlives them". Parsed at `fixpt-scheme/src/expand.rs:987`
(`Claim::NoEscape`); `facts.rs:86`.

**Why it is a latent hazard.** The claim is emitted whenever masking
removed every `alloc` atom, which happens for any expression that
allocates only in regions invisible outside it — including one that
returns a closure capturing the allocation.

**Probe.** In the REPL with `,code` on:

```
(let ((x (cons 1 2))) (lambda () (begin x 1)))
```

lowers to a body wrapped in `'(%fx-note (no-escape) (basis checked)
(because "pure"))`, yet the returned closure holds the pair `x`. So
`no-escape` here cannot mean "the allocation is dead after this
expression".

**Assessment.** No consumer acts on the claim today (grep for
`Claim::NoEscape` finds only the parse site). So it is latent. But its
stated meaning would justify stack allocation, which would leave the
collector a dangling pointer. Before anything consumes it, narrow the
claim to what is proved — "no *use* of the allocation escapes", which
licenses nothing about placement — or strengthen the analysis to check
that no returned value's type mentions the allocation's region
(`soundness-regions.md` §3.3).

## F7 — the cellular engine's throw does not end the places it leaves

**Where.** `fixpt-engine/src/cellular.rs:557–592` (`reinstate`): no
`region_exit`. Compare the abort path, which does end them
(`fixpt-engine/src/cellular.rs:939–947`), and the lowering, which wraps
each place in `dynamic-wind` (`lower.rs:286–295`).

**Why it is a space issue, not a safety one.** A full continuation thrown
out of a place body abandons the place's frame without ending the place.
The place stays live until an older place ends. Nothing uses it (the
computation that would have is gone), so C1 is not violated; but the
arena's chunks are held. A loop that enters an arena and escapes it with a
whole-continuation throw each time keeps every arena live: `Θ(iterations)`
where `S_place` is `O(1)` (`soundness-regions.md` §4.4, the counterexample
to S1).

**Status.** From reading the engine, not from a run. The fix mirrors the
abort path: record the live-region count in the continuation (the abort
path already stores it in the prompt word, `cellular.rs:900–902,939–947`)
and call `region_exit` to that count when a whole continuation is
reinstated.

## F8 — `finite` leaks into a negative position through `forget_nats`

**New, 2026-09-27, after the F4 fix (commits 0f0a61e, d83face).** Found
against a fresh build of d83face; confirmed in the Rust checker and, by
inspection, present in the FX-26 checker on the same path.

**Where.** `sizes.rs` `forget_nats` (the skolem-forgetting substitution,
`{skolem ↦ D::Size(Size::Finite)}`, `sizes.rs:358–364` at d83face), called
from the `let` and `lambda` rules (`check.rs` and `infer.rs`, at each
`self.forget_nats(named, t)`). The F4 guard `check_finite_sizes` is called
only from the `proj`/instantiation path (`check.rs`, `infer.rs`
`instantiate`/`instantiate_against`), **not** from `forget_nats`. The
FX-26 checker: `k-forget-nats` (`check.fx:2801–2809`) does the same
`k-subst t m` with no call to `k-finite-size-ok?` (`check.fx:3154`).

**The rule that is missing.** N5d gives a plain-`nat` binding a fresh
*skolem* size `ŝ` (`name_nat`, `sizes.rs:347–354`), so a `let`- or
`lambda`-bound `n : nat` is typed `(nat ŝ)` inside the scope, and facts can
be learned about `ŝ`. When the scope ends, `forget_nats` replaces `ŝ` with
`finite` everywhere in the escaping type. That substitution is exactly the
one F4 governs — but here it is applied with no check on where `ŝ` occurs.
When `ŝ` lands in a **negative** (parameter) position of the escaping
type, the F4 unsoundness returns: a singleton `(nat ŝ)` that stood for a
fixed value becomes `(nat finite) = nat`, "any natural", while the closure
body still treats it as the fixed value.

**Probe.** `f8-min.fx`:

```
(define f (poly ((s size)) (subr pure ((nat s)) (subr pure ((nat s)) (nat 0))))
  (plambda ((s size)) (lambda (a) (lambda (b) (- b a)))))
(define k (let ((y (the nat 5))) (f y)))
(the (nat 0) (k 2))
```

`f` is sound: `a, b : (nat s)` are singletons, both equal to `s`, so
`(- b a) : (nat (s − s)) = (nat 0)` is genuinely 0, and a direct
`(proj f finite)` is refused by F4 (`s` sizes two parameters). But `y` in
the `let` is typed `(nat ŝ)` with `ŝ = 5`; `(f y)` unifies `s` with the
skolem `ŝ`, not `finite`, so F4 passes, giving
`k : (subr pure ((nat ŝ)) (nat 0))`. Ending the `let`, `forget_nats`
sends `ŝ ↦ finite` in this escaping type — `ŝ` is in the *parameter* of
the returned subroutine — so `k : (subr pure (nat) (nat 0))`. Now `(k 2)`
computes `2 − 5 = −3` and the REPL prints `-3 : (nat 0)`: a `(nat 0)` that
is neither 0 nor a natural.

**Consequence.** Invariant (I6) of `soundness.md` is false again, this time
on the `let`/`lambda` path rather than `proj`. And it drives a `pure`-typed
loop, via size-change's trust that a `nat` is bounded below by 0.
`f8-full.fx`:

```
(define f (poly ((s size)) (subr pure ((nat s)) (subr pure ((nat s)) (nat 0))))
  (plambda ((s size)) (lambda (a) (lambda (b) (- b a)))))
(define k (let ((y (the nat 5))) (f y)))
(define down (subr pure (nat) int) (lambda (n) (if (= n 0) 0 (down (- n 1)))))
(define bad (subr pure () int) (lambda () (down (k 2))))
(bad)
```

`down` is accepted `pure` by size-change (a countdown on a `nat`, bounded
below). `bad : (subr pure () int)`; running `(bad)` feeds `down` the
value `−3` and exceeds the step limit — a spin-free procedure that never
ends.

**Fix.** `forget_nats` must not send a skolem to `finite` where the
skolem occurs in a non-positive position of the escaping type: the same
test `finite_size_ok`/`size_walk` already written for F4, applied to each
skolem before it is forgotten. Where it would be unsound, the binding
should not have been given a skolem to begin with, or the type must be
rejected (the value's exact size cannot be forgotten if a caller of the
result would rely on it). In the proof (`soundness.md` §4.9, revised) the
skolem is an existential opened at the *end* of the scope, and opening is
sound only under the same single-positive-occurrence condition.

## F9 — a `cwcc` continuation, cleared by `escape_only`, loops through a stored composable

**New, 2026-09-27. Suspected: a `pure`-typed program that does not
terminate is exhibited; the precise rule to blame is the *interaction* of
three, and the reproduction is not fully minimized.** Confirmed against a
fresh build of d83face.

**Where.** `escape_only`/`only_called` (`infer.rs:505–543` at d83face),
the prompt rule (`synth_prompt`, `check.rs`), and `no_knot`
(`check.rs`). Each is individually sound (F3's tests pass; see below); the
loop slips through their seam.

**Probe.** `comp-cwcc.fx`:

```
(define-effect D (maxeff (write @d) (goto @k) (comefrom @k)))
(define loop (subr pure () int)
  (lambda ()
    (let ((c (the (icell (composable int int D @p) @d) (make-icell)))
          (t ((proj (proj make-continuation-prompt-tag @p) int int D))))
      (begin
        (prompt t
          ((proj (proj (proj cwcc @k) int) (maxeff (write @d) (comefrom @p) (goto @k)))
            (lambda ((k (subr (goto @k) (int) void)))
              (begin
                ((proj (proj call-with-composable-continuation @p) int int D int (write @d))
                  (lambda ((j (composable int int D @p))) (begin (icell-put! c j) 0))
                  t)
                (k 0))))
          (lambda ((v int)) v))
        ((icell-get c) 0)))))
(loop)
```

`loop : (subr pure () int)` is accepted, and `(loop)` exceeds the step
limit.

**Why the three rules each pass.**
- `escape_only` clears the `cwcc`'s `spin`: the continuation `k` is named
  only as `(k 0)`, the operator of a call, so it is judged "only called
  while `cwcc` runs".
- The prompt rule does not force `await @d` into the tag's effect `D`,
  because the `(icell-get c)` that composes the stored continuation is
  *outside* the prompt (in `loop`'s body), not in the delimited
  computation.
- `no_knot` does not fire on the stored composable `j`: `j`'s effect `D`
  writes `@d` but does not `read` or `await` it (the read is outside `j`'s
  delimited segment), and `no_knot` looks only for `read`/`await` of the
  storing region.

The loop is real: invoking `k` resumes a context that composes `j`, whose
return leads back to `((icell-get c) 0)`, composing `j` again. The
recursion runs through the *return* of a composable continuation into an
outer context that re-composes it — a cycle no one of the three rules
sees.

**What is and is not minimized.** Two controls locate the seam:
- `cwcc-store.fx` (store `k` itself in a cell and re-enter): **rejected**,
  `spin` — `escape_only` sees `k` passed to `icell-put!`, not only called.
- `comp-outside.fx` / `comp-min2.fx` (the composable alone, no `cwcc`,
  composed outside its prompt): the honest version with `await @d` in the
  effect is **rejected** by `no_knot`; the version that hides the `await`
  is **rejected** by the prompt rule; and the accepted variant
  **terminates** (composing a delimited continuation once and returning).

So neither mechanism loops alone; the `cwcc` re-entry is needed, and its
`spin` was cleared by `escape_only`. This points at `escape_only` as too
weak: a `k` that is "only called" can still re-enter a context that, via a
stored composable, re-invokes the same computation. But because the
reproduction needs the composable and the effect annotations are intricate,
this is filed as *suspected*, pending a cleaner minimization and a decision
whether the fix belongs in `escape_only` (treat a `cwcc` whose extent
captures a composable that outlives the prompt as `spin`), in the prompt
rule (an `await` on a region a composable of the tag is stored in), or in
`no_knot` (count a composable reachable from storage the surrounding
computation reads).

**Not a memory-safety problem**, like F1/F3/F5: the loop is well behaved
but for ending.

## Assumptions the proof makes

**A1 — masking side conditions read over derivation types, not syntax.**
`soundness.md` Lemma 4.2 (value substitution) needs the escape and
`reaches_only` conditions to be about the *types* appearing in the
derivation, not the free variables of the term. The checker computes them
syntactically (`free_vars`, `check.rs:719–724`; `reaches_only`,
`check.rs:1946–1959`; `close_region` uses `regions_in` on the *type*,
which is on the right side). The two agree as long as a variable free in
the term has a type that mentions exactly the regions the value at run
time can reach. This is the standard gap between a syntactic and a
semantic masking rule; for the elaboration (T0) to be sound the syntactic
rule must be at least as strong as K26's, which it is for the constructs
present (a captured-but-unused variable keeps its region visible, the
conservative direction). Worth a dedicated check if masking is ever made
finer.

**A2 — a cycle through a generative name is contractive.** The checker
counts `N[d…]` as a constructor for the "a cycle must pass through a
constructor" rule (`docs/fx26.md`, "Recursive types"). Semantically `N` is
its representation, so `μx.N[x]` with `N[a]=a` is a non-contractive cycle.
`soundness.md` §4.7 assumes no value of such a type can be built; that
seems right (there is no base case) but is not proved, and the subtyping
and size-change walks that unfold `N` bound their recursion by depth (64),
which is the F5 pattern in another place (`lemma.rs:118–126`
`unfold_all`, `check.rs:1059` `unfold`).

**A3 — `datum` values from the host are acyclic.** Size-change and
`acyclic?` treat `datum` as data. A cyclic datum built by the Scheme host
and handed in (`docs/fx26.md` notes "a `read` that makes cycles from datum
labels is still to come") would break the termination of a walk that the
checker certified. The proof (T5) assumes host data acyclic; the language
does not yet enforce it.

[^cellular]: "Cellular" would be called "threaded" in the Forth community: code as
a sequence of cells (references to routines, and their operands), run by an inner
interpreter. This repository says "cellular" throughout (the user's decision,
2026-09-27).
