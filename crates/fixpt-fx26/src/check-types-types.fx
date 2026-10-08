;;; The types of `check-types.fx`, its `check-types-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type syn (select parser-types syn))
;; The checker's state, and everything checking may do.
(define-effect kstate (maxeff (read @globals) (read @t) (write @t) (alloc @t)))
(define-effect checks (maxeff (read @s) kstate (goto @z)))
;; Reading the checker's state; and that, allocating in it, and perhaps not
;; ending, as reading and showing descriptions do.
(define-effect kreads (maxeff (read @globals) (read @t)))
(define-effect kbuilds (maxeff kreads (alloc @t) spin))
;;; ------------------------------------------------------------ descriptions

;; A region: a constant `@name`, a fresh one (made by inference or a
;; bloblet, which no program can name), or a binder.
;; `(r-frozen p #f)` is `(const p)`, and `(r-frozen p #t)` `(acyclic p)`
;; (frozen data never written, only built, and so finite); in both, the
;; region of data frozen into place `p` (a
;; place variable, or -1 for the heap: `const`), which nothing may write;
;; `r-heap` is `heap`, the place that never ends
;; (`docs/research/places-and-regions.md`). `(r-global g)` is `(globals g)`,
;; the binding of global `g`, and `r-globals` is `@globals`, every global's:
;; only in effects, only read and written, never masked.
(define-datatype k-region
  (r-const symbol) (r-fresh int string) (r-var int) (r-frozen int bool) (r-heap)
  (r-global symbol) (r-globals))
(define-datatype k-atom
  (a-read k-region) (a-write k-region) (a-alloc k-region)
  (a-goto k-region) (a-comefrom k-region) (a-await k-region) (a-spin) (a-var int)
  ;; `(e d …)`: a description function to an effect, a variable, applied
  ;; to descriptions, none a type (`check-kinds.fx`): an unknown effect, as
  ;; a variable is.
  (a-app int (listof k-desc acyclic)))
(define-type k-eff (listof k-atom acyclic))
;; A `vsubr`'s effect, element and result, in a list: one or none.
(define-type k-vsub (listof (productof (1 k-eff) (2 int) (3 int)) acyclic))
(define-type k-ids (listof int acyclic))
;; Propositions about a procedure's arguments (`ty-proving`), each by its
;; parameter's number from 0: of a shape (`check-unions.fx`'s), or, the
;; flag, not; certifications, acyclic, a natural, of a length; a relation
;; of sizes, 0 `<`, 1 `<=`, 2 `=`, 3 not `=`, of terms: argument `i` as a
;; natural, the length of its `nlist`, or a natural (`sizes.rs`).
(define-datatype k-term (tm-param int) (tm-length int) (tm-lit int))
(define-datatype k-prop
  (pr-shape int int bool) (pr-acyclic int) (pr-nat int) (pr-length int int)
  (pr-rel int k-term k-term))
(define-type k-props (listof k-prop acyclic))
;; A binder: a description variable and its kind, 0 region, 1 effect, 2 type.
(define-type k-binders (listof (productof (1 int) (2 int)) acyclic))
(define-type k-parts (listof (productof (1 symbol) (2 int)) acyclic))
(define-type k-names (listof symbol acyclic))
(define-type k-strings (listof string acyclic))
;; A description in argument position, what `proj` supplies.
;; A list's length, as far as it is known: `finite`, some number; or a
;; constant and terms (variable . coefficient), in variable order.
;; A procedure's convention (`docs/research/native-conventions.md`):
;; `cellular`, `native`, `fx`, or a binder.
(define-datatype k-conv (cv-cellular) (cv-native) (cv-fx) (cv-var int))
;; A size's terms: each a variable and its coefficient.
(define-type k-terms (listof (pairof int int acyclic) acyclic))
(define-datatype k-size (sz-finite) (sz-lin int k-terms))
(define-datatype k-desc (dr k-region) (de k-eff) (dt int) (dz k-size) (dc k-conv)
  ;; A description function: a `dlambda`, a variable of an arrow kind, or a
  ;; `select` of a module's (`check-kinds.fx`).
  (df int))
(define-type k-descs (listof k-desc acyclic))
(define-datatype k-ty
  (ty-base symbol)
  (ty-void)
  (ty-var int)
  ;; effect, parameters, result, convention
  (ty-subr k-eff k-ids int k-conv)
  (ty-poly k-binders int)
  (ty-ref int k-region)
  ;; head, tail, region, and whether it may be `nil` (`(union nil (pairof
  ;; …))`, as a list's pairs are; `docs/research/logical-types.md`, L0)
  (ty-pair int int k-region bool)
  ;; answer, payload, bound, region
  (ty-tag int int k-eff k-region)
  ;; argument, answer, effect, region
  (ty-comp int int k-eff k-region)
  (ty-markkey int k-region)
  (ty-product k-parts)
  (ty-sum k-parts)
  (ty-array int k-region)
  (ty-icell int k-region)
  ;; The place a region is allocated in, as a value: what `letrena` and
  ;; `letreap` bind.
  (ty-place k-region)
  (ty-bloblet k-ids bool k-region)
  ;; A forwarding slot: none or one.
  (ty-link k-ids)
  ;; A generative type applied to its descriptions: the `n`th
  ;; `define-generative`. Equal only to itself, by its variance; looked
  ;; through by every analysis of what a value holds.
  (ty-named int (listof k-desc acyclic))
  ;; `(nlist T size)`: a list frozen at the region (always finite) with `size`
  ;; elements, or some number (`docs/research/sizes.md`).
  (ty-nlist int k-size k-region)
  ;; `(nat size)`: a natural, exactly `size`; `nat` is `(nat finite)`.
  ;; Every one is an `int` (`docs/research/sizes.md`, N5d).
  (ty-nat k-size)
  ;; `(moduleof (abs t type) … (desc d T) … (val x T) …)`: a module's type
  ;; (`docs/research/first-class-modules.md`): its abstract types, each a
  ;; name and a type variable, binders in its descriptions and values.
  (ty-module k-parts k-parts k-parts)
  ;; `(select m t)` as written, resolved where it is checked
  ;; (`k-resolve-selects`).
  (ty-select symbol symbol)
  ;; `(select $k t)`: in a procedure's type, the type `t` of its `k`th
  ;; parameter (from 0), a module: a dependent procedure, a functor
  ;; (`first-class-modules.md`, M5). A call puts the argument's for it.
  (ty-param int symbol)
  ;; `(dlambda ((x k) …) d)`: a description function; and `(f d …)`, one
  ;; applied that cannot be reduced, `f` a variable or a `select`
  ;; (`check-kinds.fx`).
  (ty-lam k-binders k-desc)
  (ty-app int (listof k-desc acyclic))
  ;; `nil`, the empty list only; and `(union T …)`, its members of shapes
  ;; that differ at run time (`k-shape`; `logical-types.md`, L1).
  (ty-nil)
  (ty-union k-ids)
  ;; `(bool (then P …) (else Q …))`: a `bool` that proves the `P`s of its
  ;; procedure's arguments where true, the `Q`s where false; a procedure's
  ;; result only. A call's own type is `bool` (`k-call-te`).
  (ty-proving k-props k-props)
  ;; `false`: `#f` alone, below `bool`, of `bool`'s shape.
  (ty-false))
(define-type k-map (listof (pairof int k-desc @t) acyclic))
;; What a description name means where it is used.
(define-datatype k-ds
  ;; A name `define-generative` bound: the `n`th generative type.
  (ds-gen int)
  ;; A size given for a type family's size parameter.
  (ds-size k-size)
  (ds-var int int)
  (ds-rec int)
  (ds-abbrev (listof (productof (1 symbol) (2 int)) acyclic) syn)
  (ds-region k-region)
  (ds-eff k-eff)
  ;; A convention given for an abbreviation's convention parameter.
  (ds-conv k-conv)
  ;; A name for a description function: `define-type` of a `dlambda`, or a
  ;; type family's parameter of an arrow kind given one.
  (ds-fun int))
;;; ------------------------------------------------------------ expressions
;;; The parser's trees with their descriptions read. Each ends with where it
;;; starts and ends.

(define-datatype kx
  (x-var symbol int int)
  ;; A literal: its type, and its value if an integer (a boolean's is 1
  ;; or 0), which the termination check reads.
  (x-const int int int int)
  (x-lambda (listof (productof (1 symbol) (2 k-ids)) acyclic) kx int int)
  (x-app kx (listof kx acyclic) int int)
  (x-plambda k-binders kx int int)
  ;; `letregion`, `letrena`, `letreap` or `letfreeze`: what it makes besides
  ;; the region (0 nothing, 1 an arena, 2 a reap, 3 nothing, frozen as it
  ;; ends), the region variable, what a `letfreeze` freezes into (`(const
  ;; p)`), and the body.
  (x-letregion int int k-region kx int int)
  ;; `rlambda`: the region, and the `lambda`.
  (x-rlambda kx kx int int)
  (x-proj kx (listof k-desc acyclic) int int)
  (x-if kx kx kx int int)
  (x-letrec (listof (productof (1 symbol) (2 int) (3 kx)) acyclic) kx int int)
  (x-let (listof (productof (1 symbol) (2 kx)) acyclic) kx int int)
  (x-begin (listof kx acyclic) int int)
  (x-prompt kx kx kx int int)
  (x-the int kx int int)
  ;; `(convention C e)`: the procedure converted to `C`.
  (x-convention k-conv kx int int)
  (x-bloblet symbol int (listof kx acyclic) int int)
  (x-product (listof (productof (1 symbol) (2 kx)) acyclic) int int)
  (x-extract kx symbol int int)
  (x-sum symbol kx int int)
  (x-tagcase kx (listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) acyclic)
             (listof (productof (1 symbol) (2 kx)) acyclic) int int)
  ;; `module`: each item what it is (as `e-module`'s), its names, an
  ;; abstract type's variable (else -1), its types, and its expressions.
  (x-module (listof (productof (1 int) (2 k-names) (3 int) (4 k-ids) (5 (listof kx acyclic)))
                    acyclic)
            int int)
  (x-with symbol kx int int))
(define-type kxs (listof kx acyclic))
(define-type k-item (productof (1 int) (2 k-names) (3 int) (4 k-ids) (5 kxs)))
(define-type k-items (listof k-item acyclic))
;; A type and an effect.
(define-type k-te (productof (1 int) (2 k-eff)))
;; What checking a program found, or the first error; and, inside, what a
;; computation whose errors are being rewritten produced.
(define-datatype k-result
  (k-ok (listof string acyclic))
  (k-err string int int)
  (k-done k-te))
;; The variables a test has narrowed, in the branch where it did: each by
;; name and binding, and its type there (the Rust checker's `narrowed`).
(define-type k-narrows (listof (productof (1 symbol) (2 int) (3 int)) acyclic))
;; Unions read with a member not yet known, a recursive type's own name, and
;; where: checked once it is (`k-union-of`).
(define-type k-pendings (listof (productof (1 int) (2 int) (3 int)) acyclic))
;; What `length-is?` has just confirmed: a variable, its binding, the length.
(define-type k-cert-len (productof (1 symbol) (2 int) (3 k-size)))
;; The arrow kinds made so far, newest first: each its parameters' kinds and
;; its result's. Kind 100 + n is the nth; kinds below are the
;; base kinds (0 region, 1 effect, 2 type, 3 place, 4 data, 5 size, 6 conv).
(define-type k-arrow-kind (pairof k-ids int @t))
;; Each bounded region binder's bound: `(r region p)`, a region that won't
;; outlive `p` (`docs/research/places-and-regions.md`).
(define-type k-bounded (listof (pairof int k-region @t) acyclic))
;; The region and place variables bound around each one's binder, which it
;; won't outlive: the order of lifetimes, by nesting.
(define-type k-nesting (listof (pairof int k-ids @t) acyclic))
;; The recursive groups whose lambdas are being checked, a call of which
;; there is recursion; and the standard bindings. (Known procedures are
;; kept with the bindings: `k-known`.)
(define-type k-named (listof (pairof symbol int @t) acyclic))
;; Every `define-generative`, newest first: its name, parameters, their
;; variance (0 covariant, 1 contravariant, 2 invariant), and representation.
(define-type k-gen (productof (1 symbol) (2 k-binders) (3 k-ids) (4 int)))
;; The lemmas proved so far (`src/lemma.rs`), oldest last: binders, the
;; two sides, the hypotheses, and the definition that proves it (none or
;; one); and the one a `proves` type being read states.
(define-type k-hyps (listof (pairof int int @t) acyclic))
(define-type k-lemma (productof (1 k-binders) (2 int) (3 int) (4 k-hyps) (5 k-named)))
(define-type k-regions (listof k-region acyclic))
;; A step of a path from a variable: `car`, `cdr`, a product's field.
(define-datatype k-step (st-car) (st-cdr) (st-field symbol))
(define-type k-steps (listof k-step acyclic))
;; What tests have narrowed paths from variables to (`check.rs`'s
;; `PathFact`), newest first: the variable, its binding's depth, the
;; steps, the regions they read through, the type, the closure depth it
;; was found at, and whether an effect since has ended it.
(define-type k-path-fact
  (productof (1 symbol) (2 int) (3 k-steps) (4 k-regions) (5 int) (6 int) (7 bool)))
(define-type k-path-facts (listof k-path-fact acyclic))

;;; ------------------------------------------------------------ signatures

;; What clients use of `check-types.fx`'s module (`TODO.md` §68): the
;; evaluator's.
(define-type check-types-sig
  (moduleof
   (val k-cat3 (subr pure (string string string) string))
   (val k-cat5 (subr (read @globals) (string string string string string) string))))
