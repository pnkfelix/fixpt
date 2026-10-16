# Raw scalars: unboxed `f64`s as a kind of their own

Design note, 2026-10-16, for the user to decide (`TODO.md` §91). The
user's question (2026-10-13): unboxed floats as a kind of their own that
no type variable ranges over, as `flat` is, so that every call agrees
from the types; compare GHC's `Double#` and OCaml's layouts.

## The recommendation, in brief

- **Yes, as a kind, `raw`, of types written `(raw F)`** for `F` a flat
  scalar of a word or less: `(raw f64)` first, `(raw i64)` and
  `(raw u64)` with it (the "raw `i64` and `u64` slots" item of §91
  comes free), `f32`, `i32`, `u32` allowed but no faster than today's
  immediates. A raw is not a type (`` `(raw f64)` is a raw, not a type ``,
  as `` `f` is a flat, not a type ``), so no `(t type)` is ever
  instantiated at one, and polymorphic code never meets one.
- **Written only where it is wanted**: as a procedure's parameter or
  result, a binder's type, or `the`. A program that writes none is
  checked and compiled as today; today's inference of raw slots,
  arguments and results stays, for code that writes none.
- **What it buys is a static convention for unknown calls.** A procedure
  whose type has `(raw f64)` parameters takes them raw in `d`
  registers from every caller, known or not, and returns a `(raw f64)`
  raw in `d0` to every caller: both ends know it from the type. No mask,
  no adapter at run time, no mark at the return address.
- **Between `(raw f64)` and `f64`, the checker inserts the conversion**,
  where bidirectional checking sees both ends, as it inserts conventions'
  conversions (`docs/research/native-conventions.md`): an unbox, a box,
  or, for a procedure, an adapter made where the conversion is written,
  never decided at run time. The `f64` operations keep their types: a
  conversion into an `f64` operation and out of it is free natively, where
  `reps` already keeps their operands raw.
- **Before building, measure** (below): of the ported benchmarks only
  `nbody` still boxed `f64`s in its loop, and an analysis-only fix took
  most of them. The kind pays for higher-order numeric code (a procedure
  passed a procedure over `f64`s) and for predictability; neither is in
  the ports yet.

## Where we are

Natively (`DONE.md` §91), an `f64` is a boxed flonum as a value, and raw
where the compiler can see both ends:

| where                 | raw when                                                                                         | how a caller knows                                                       |
| --------------------- | ------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------ |
| a frame slot          | every web of the slot is an `f64`'s (`reps::raw_slots`)                                          | n/a: one procedure's                                                     |
| a result              | the caller uses it only in `f64` operations (`reps::raw_refs`)                                   | at run time: a mark at the return address (`movk xzr, #0xf64f, lsl #48`) |
| an argument           | the callee uses it only in `f64` operations (`reps::raw_params`), and the call is to a known callee | at compile time: `invokeself`, or a global not written since, or a lifted lambda |
| a flat array's element | always (`flatarrayof`, `blobref`)                                                                | the type                                                                 |

So raw passing depends on analysis at both ends and, for results, on a
protocol at run time; a call through a procedure value passes boxes,
as does a call of a global made native a form before (`TODO.md` §91);
and a parameter that only goes on to another call is taken as a value.
The first version (6ec7f7e) passed a mask in `x9` to any callee
and was dropped as complexity that would not pay (the user's,
2026-10-13: no masks).

## Why a kind, and not a convention or a type

**Not a type.** If `(raw f64)` were a type, `(t type)` could be
instantiated at it, and `(poly ((t type)) (subr pure (t) t))`'s one body,
compiled for values, would be called with a raw `d` register. Either
every polymorphic procedure is compiled per representation
(specialization, against dictionary passing, the user's rule), or each
instantiation coerces (Leroy, POPL 1992), which must reach into data:
a `(listof (subr pure (t) t))` instantiated at `f64` would be copied with
each element adapted. OCaml (flat `float array`) shows the third way, a
test at run time in polymorphic code, which is what we do not do. A kind
that no type variable ranges over closes all three: the instantiation
cannot be written.

**Not a convention.** Conventions are already in procedure types, `(subr
(conv C) …)`, and their conversions are already static adapters, so
"`native` passes `f64` raw" is tempting. But a convention is a property of
the procedure, and an `f64` parameter's representation would then follow
from its type after instantiation: `(proj id f64)`, a `(subr (conv
native) pure (f64) f64)`, is the uniform `id`, whose code takes a value.
The convention would promise what the code does not do; it is the type
case again.

**As GHC and OCaml do.** GHC's `Double#` has kind `TYPE 'DoubleRep`, not
`Type`, so a variable of kind `Type` cannot stand for it; variables over
representations exist (levity polymorphism) but may not be bound or
passed, since their code would not know its registers (Eisenberg & Peyton
Jones, PLDI 2017). OCaml's unboxed types (Jane Street's layouts, 2023–)
give `float#` the layout `float64`; a type variable has layout `value`
unless annotated, and a function over `('a : float64)` is compiled for
that layout, once. Both keep the boxed type (`Double`, `float`) as the
one generic code sees, with explicit or inferred conversions between.
That is the proposal: our `flat` kind already has the shape (a kind of
non-values, the scalars named as the types are), and `raw` is its
counterpart in registers and frames.

## The rules

1. **The kind.** `(raw F)`, `F` one of `f64`, `f32`, `i64`, `u64`,
   `i32`, `u32`, has kind `raw`. Not a type: refused wherever a type is
   wanted, with that message. No binder of kind `raw` at first (see the
   open questions).
2. **Where one may be written.** A `subr`'s parameter and result types;
   a `lambda`'s, `let`'s and `define`'s binder type; `the`. Not as a
   type argument, a field of `pairof`, `listof`, `ref`, `arrayof`,
   `productof` or `sumof`, a member of a `union`, a module's value, or a
   global (a global's cell holds a value): those are type positions, so
   rule 1 already refuses them. A flat array or a blobref is where a raw
   is kept in data.
3. **Values of it.** A raw has no region and no effect to make; it is
   pure, as an `int` is. `eq?` on raws is not provided (an `f64=`).
4. **Conversions, inserted.** Where an expression of `(raw F)` is checked
   against `F`'s type, or the reverse, the checker elaborates
   `(%box-raw e)` or `(%unbox-raw e)`; where a procedure whose parameters
   or result differ only so is checked against the other, an adapter
   (rule 6). `(raw-of e)` and `(boxed e)` write them where the checker
   could not tell, or to make one visible; `,code` shows them, as
   conventions' conversions are shown.
5. **Operations.** The `f64` operations keep their types; `(f64+ x y)`
   of two raws is two unboxes, the operation and, where a raw is wanted,
   a box, all of which `reps` already removes natively. No second set of
   primitives.
6. **Procedures.** `(subr e ((raw f64)) (raw f64))` is a type of its
   own, related to `(subr e (f64) f64)` by no subtyping, only by a
   conversion, an adapter made where the conversion is (a closure in the
   other representation, as a convention's adapter is). Natively, every
   call of a procedure of that type passes the raw arguments in `d`
   registers (the integer raws in `x` registers, as values are) and takes
   the raw result in `d0`, whatever the callee: the type is the
   convention.
7. **Captures.** A closure that captures a raw keeps it in its bloblet's
   suffix, as a frame keeps raw slots (`bloblet-shaped layouts`): fields
   for values, raw bits after.
8. **Every machine.** The meaning is a boxed float's: the lowering, the
   evaluator written in FX-26 and the cellular machines may keep raws
   boxed throughout, since nothing generic sees them and both ends of
   every call agree from the type. Only native code (and register code
   for it) must keep them raw, and the adapters between cellular and
   native code box and unbox them.

## What changes, by part

| part                                 | change                                                                                                                                         |
| ------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------- |
| both checkers                        | the kind; `(raw F)` read and refused in type positions; conversions elaborated in `check` where the expected and found differ by rawness       |
| both compilers to register code      | a raw parameter, result or capture by its declared type, not `reps`; the conversions as unbox and box, which `reps` may then cancel           |
| native code (`direct.rs`, `native.fx`) | `d` registers for raw parameters and results at every call; a stub's and an overflow's boxing of raw argument registers, as today's known calls |
| closures                             | raw captures in the suffix                                                                                                                     |
| cellular machines, lowering, evaluator | `(raw F)` as `F`; the conversions the identity                                                                                                 |
| adapters (`%fx26-convert`)           | box or unbox a raw parameter or result crossing between cellular and native code                                                               |
| `docs/fx26.md`, tests                | a section; programs for each position refused, each conversion, unknown calls passing raws, captures, every machine                           |

Today's `reps` inference stays: code that writes no `raw` gets what it
gets now. The return-address mark (`take_raw_f64`, `raw_return`) is then
needed only for procedures typed `f64`; whether to keep it is open
question 3.

## Measure first

What the ports would gain is small and checkable before any of this:

- `nbody`: measured (2026-10-16), the boxes were not `put`'s `v` (`put`
  is inlined) but a frame slot shared by an `f64` and an `int`; fixed in
  the native compiler (`reps::split_slots`, `DONE.md` §91), 1.29 → 0.67
  s. What is left there (`advance` passing `dt` to `pairs`, compiled a
  form before, through its cell) is an argument to a callee not known
  where the call is compiled: what `raw` would settle by the type, and
  what the native code could also settle by saying how its procedure
  takes its arguments (`TODO.md` §91).
- The integrator, measured (2026-10-16,
  `docs/research/examples/raw-scalars/`): Simpson's rule over 4/(1+x²),
  60 M calls of the integrand, natively, the run alone, best of 3:

  | integrand                              | time    | M words | ns a call |
  | -------------------------------------- | ------: | ------: | --------: |
  | a procedure value (`closure.fx`)       | 0.545 s |   119.6 |       9.1 |
  | a global called by name (`known.fx`)   | 0.292 s |     0.0 |       4.9 |
  | its body in the loop (`inlined.fx`)    | 0.266 s |     0.0 |       4.4 |

  Through a value one box a call, the argument's (the result comes back
  raw, by the return address's mark): about half the time. So `raw`
  would make such a call about 1.9× faster, 4 ns. (`value.fx`, the
  integrand a global's closure passed as a value, took 1.110 s: not the
  boxing but a nursery left uncollected, `TODO.md` §102.)
- What would need `raw`: an `f64` argument or result through a procedure
  value. None of the 46 ports does that in a hot loop; the integrator
  above does, and shows the gap.

So the order would be: the `reps` fix for `nbody` (done); the
integrator written and measured (done: about 1.9× on such a call); then
`raw` if the gap is worth its rules.

## Open questions for the user

1. **Worth it now?** Given the measurements above: build `raw` once a
   program needs raws through unknown calls, or now, for predictability
   (raw where the type says, not where an analysis found it)?
2. **Spelling.** `(raw f64)`, one form over the flat scalars and the
   kind named `raw`; or a name per type, `f64#` as GHC and OCaml write
   it?
3. **The return-address mark.** Keep it for code that writes no `raw`
   (today's gains stay without annotations), or retire it, a protocol at
   run time, once `raw` exists, and let programs that want raw results
   say so?
4. **Variables of kind `raw`.** Not at first. OCaml allows them, compiled
   once per layout; for us, `(r raw)` would need code per register class
   (`d` or `x`), so a copy per class, which is specialization. Leave out
   unless asked for?
5. **Inferred raws.** Should `->*` (whose types are found from the
   lambda) find `(raw f64)` for a parameter only `f64` operations use?
   That would change a procedure's type by what its body does, which the
   type is meant to fix for its callers; so not, unless asked.

## Sources

- Eisenberg and Peyton Jones, "Levity Polymorphism", PLDI 2017.
- Peyton Jones and Launchbury, "Unboxed Values as First Class Citizens
  in a Non-Strict Functional Language", FPCA 1991.
- Leroy, "Unboxed Objects and Polymorphic Typing", POPL 1992.
- OCaml's unboxed types: Jane Street's layouts (`float#`, layout
  `float64`), described in their talks and the OCaml RFC on unboxed
  types (2023); OCaml's `floatarray` and `--disable-flat-float-array`.
- `docs/research/floats.md` (§2c, the polymorphism table);
  `docs/research/native-conventions.md` (conventions in types, their
  conversions); `DONE.md` §91 (raw slots, results, arguments).
