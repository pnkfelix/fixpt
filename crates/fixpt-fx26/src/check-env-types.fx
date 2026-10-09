;;; The types of `check-env.fx`, its `check-env-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-ds (select check-types-types k-ds))
(define-type k-ids (select check-types-types k-ids))
(define-type k-names (select check-types-types k-names))
(define table-types (load-module "fx26:table-types.fx"))
(define-type table (select table-types table))
;; Bindings, as lists of them are passed around.
(define-type k-bindings (listof (pairof symbol int @t) acyclic))
;; Value variables in scope: for each name, the types it is bound to,
;; innermost first; and the names bound, newest first, so that a scope is
;; left by unbinding back to a mark (`k-mark`, `k-unbind-to`). A lookup is
;; a table's, not a walk down every binding in scope.
(define-type k-stack (listof int acyclic))
;; Whether each binding in `k-env` is of a known procedure: one a `define`,
;; `letrec`, `define-rec`, or a `let` of a `lambda` made. A call of one runs
;; code the checker has seen; a call of anything else might run a closure
;; fetched from the store. By binding, in step with `k-env`, not by name and
;; type, so a parameter that shadows one is not taken for it
;; (`docs/research/soundness-findings.md`, F1).
;; For each name, a flag for each of its bindings in `k-env`, innermost
;; first.
(define-type k-flags (ref (table symbol (listof bool acyclic) @t) @t))
;; The type `s` is bound to, or -1.
;; Globals broken by a redefinition (`k-defining`): the name, how many
;; bindings it had then (so which one is broken), and why. A use of a broken
;; binding is an error saying why, until the name is defined again.
(define-type k-break (productof (1 symbol) (2 int) (3 string)))
;; The operator of the application being checked, past any `proj` or
;; `the`, by name and place: where a second-class standard operation may be
;; named (F15, F16).
(define-type k-op-mark (productof (1 symbol) (2 int) (3 int)))
;; Description names in scope, innermost first.
(define-type k-scope (listof (pairof symbol k-ds @t) acyclic))
;; What checking proved that running needs: each `extract`'s field, by
;; position, keyed by where the `extract` is. Only the product's type says.
(define-type k-fact (productof (1 int) (2 int) (3 int)))
(define-type k-facts (listof k-fact acyclic))
;; Each `with` checked, where it is, and its module's values its body names,
;; with their positions in the module, newest first: a `with`'s body sees
;; them, once checking has found them; a re-export, of one value, binds one.
(define-type k-with-noted (productof (1 int) (2 int) (3 k-names) (4 k-ids)))
(define-type k-with-list (listof k-with-noted acyclic))
;; While a module's order is checked (`check-modorder.fx`): each earlier
;; item whose value is a module as written, and its values' names, which a
;; `with` of it not checked yet binds.
(define-type k-hazard-list (listof (productof (1 symbol) (2 k-names)) acyclic))
;; Each module given where a type of fewer values, or the same in another
;; order, is wanted (`k-reshape-at`): where, and for each value that type
;; has, its position in the module given. Made into a module of that layout.
(define-type k-reshaped (productof (1 int) (2 int) (3 k-ids)))
(define-type k-reshape-list (listof k-reshaped acyclic))
;; While a type's `select`s are resolved (`k-resolve-selects`): what each
;; is, `(m t)` and the type; none otherwise.
(define-type k-selected (productof (1 symbol) (2 symbol) (3 int)))
(define-type k-selects (listof k-selected acyclic))
;; While a dependent procedure's parameters are given (`k-instantiate-params`):
;; what each `(select $k n)` is, `(k n)` and the type; none otherwise.
(define-type k-param-given (productof (1 int) (2 symbol) (3 int)))
(define-type k-params-given (listof k-param-given acyclic))

;;; ------------------------------------------------------------ signatures

;; What clients use of `check-env.fx`'s module (`TODO.md` §68): the
;; evaluator's.
;; The types it names, from the files that define them.
(define-type k-eff (select check-types-types k-eff))
(define-type check-env-sig
  (moduleof
   (val k-fx-module? (subr pure (symbol) bool))
   (val k-reshapes (ref k-reshape-list @t))
   (val k-with-vals (ref k-with-list @t))
   (val k-last-latent (ref k-eff @t))
   (val k-broken (ref (listof k-break acyclic) @t))
   (val k-name-depth (subr (maxeff (read @globals) (read @t) spin) (symbol) int))
   (val k-std-dscope (ref k-scope @t))
   (val k-shared-name? (subr (read @globals) (symbol) bool))
   (val k-lookup-raw (subr (maxeff (read @globals) (read @t) spin) (symbol) int))
   (val k-mark (subr (maxeff (read @globals) (read @t)) () int))
   (val k-unbind-to
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin) (int) unit))
   (val k-note-known
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
              (symbol int)
              unit))
   (val k-bind-global
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
              (symbol int)
              unit))
   (val k-dscope (ref k-scope @t))
   (val k-push-desc
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t)) (symbol k-ds) unit))
   (val k-extracts (ref k-facts @t))
   (val k-effect-notes (ref k-facts @t))
   (val k-forget-withs (subr (maxeff (alloc @t) (read @globals) (write @t)) () unit))))
