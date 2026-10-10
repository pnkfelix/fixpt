# Claude's choices

Decisions made while working without asking (the user's, 2026-10-10:
"whenever you have to make a decision, use your best judgement, and log
your choice"). Newest last; each says what was chosen, over what, and why.

## TODO.md §69: `with` shadows applied description functions (2026-10-10)

1. **What is read.** In a `with` body, `(f d …)` is read as `((select m f)
   d …)` for the innermost `with`'s `m`, falling back to the next `with`'s,
   then to what `(f d …)` means outside. Same shape as bare names
   (`with_selected`), so the two read alike.
2. **What falls back.** When `m` does not give `f`, the *application* node
   is linked to the outer reading, not the `select` node. Rejected: making
   the fallback a constant `dlambda` ignoring its arguments, because the
   `select` map is keyed by `(m, f)`, and two applications of one `f`
   (`(pairof (f int) (f bool))`) would then share one fallback.
3. **What is not shadowed.** Heads that are type forms (`listof`, `subr`,
   `pairof`, … : `TYPE_FORMS`, FX's `k-type-forms`) are never shadowed, as
   base types are not for names alone.
4. **Arguments read by shape.** Each `with` level reads the arguments
   again with `parse_d` (by their shape, kinds checked once `f` is known,
   `check_apps`), as `((select m f) d …)` written out already is.
5. **The outer reading's errors.** If `f` is bound outside, the outer
   reading is made eagerly and its errors are reported even where `m`'s
   `f` would have fit; the same as for bare names today. Simpler, and the
   case (an outer `f` of a different kind shadowed by `m`'s) is rare.
6. **Error wording** where neither `m` nor the outside gives `f`: "`f` is
   not a description function, nor one a module opened by `with` gives",
   parallel to the names' "`n` is not a type, nor one …".
7. **Effect functions applied, `(e d …)` in an effect, are not shadowed.**
   A module's effect function cannot be selected at all yet (`effect_app`
   reads a name or a `dlambda` head, no `select`), so there is nothing for
   `with` to put first; left for when that exists.

## TODO.md §69: `include` and `extend` of modules with abstract types not named (2026-10-10)

1. **Types, not text.** The TODO suggested splicing a literal module's
   items (`(module …)`, `(load-module "f")`) into the including one, as
   OCaml's `include struct … end`. Chosen instead: at the type level, a
   module that is not a name (literal, loaded, made by a call) has its
   abstract types taken in as the new module's own abstract types (an
   existential unpacked and packed again), its values by path as before.
   This covers every such expression, not just literal text, needs no
   change at run time, and keeps one way of combining (the reshape).
   Splicing would also have had to re-check the items in the new scope.
2. **Fresh variables.** Each taken-in abstract type gets a fresh variable
   (`abs_taken`, `k-abs-own`), with one substitution over all the sides
   and the module's own items. A procedure's result type is parsed once,
   so two calls share its variables; without this, two modules including
   `(make 1)` and `(make 2)` could share a type. (Binding to a name
   renames them anyway, so this is belt and braces, but it costs little.)
3. **`extend` replacing an abstract type.** `e1`'s names, abstract or not,
   replace `e0`'s. If something kept (a value of `e0` not replaced, or a
   description) still mentions the replaced abstract type, refused:
   "`x`'s type mentions the first module's `t`, which the second's `t`
   replaces". Rejected: keeping it under a hidden name (an existential
   that can't be named outside), which FX-91 does not describe.
4. **Order of the abstract types.** `include`: the included modules' own,
   in order, then the module's own. `extend`: `e0`'s kept, then `e1`'s.
5. **Name clashes in `include`.** An abstract type taken in is "defined
   twice" if the module or an earlier include already has that name as an
   abstract type or a description. The Rust checker missed the case of
   the module's own description against an included abstract type; fixed
   in both.
6. **`(hide (include …))` hides the abstract types too.** They are names
   the include brings in, so they are marked hidden, as its values and
   descriptions are. An exported type mentioning one is then refused, as
   for any hidden abstract type (TODO.md §69's remaining item).
7. **The old refusal tests** (`include-abstract.fx`, `extend-abstract.fx`)
   now run; I rewrote them as programs giving answers rather than keep
   tests for an error that no longer exists.
