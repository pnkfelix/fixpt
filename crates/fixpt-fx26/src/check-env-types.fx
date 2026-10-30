;;; The types of `check-env.fx`, its `check-env-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(import check-types-types (type k-ds k-ids k-names k-at k-conv))
(hide (define table-types (load-module "fx26:table-types.fx")))
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
(define-type k-op-mark (productof (1 symbol) (2 k-at)))
;; Description names in scope, innermost first.
(define-type k-scope (listof (pairof symbol k-ds @t) acyclic))
;; What checking found of an expression that running needs, for the
;; compilers and the evaluator (`checked-extracts`):
(hide (define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
(define-type k-datum (select parser-types k-datum))
(define-datatype k-noted
  ;; What an operation needs that only the types say (`k-datum`).
  (n-datum k-datum)
  ;; The expression's effect, summarized (`k-summary`).
  (n-summary int)
  ;; A procedure converted to a convention: what `%fx26-convert` is given.
  (n-conversion int)
  ;; An `apply` whose list is at `acyclic`, which it need not copy.
  (n-apply-shares)
  ;; A definition's value that is a list nothing writes.
  (n-frozen-define)
  ;; A `(with #%fx n)` that is the plain `n`.
  (n-plain-fx)
  ;; A call: its callee's convention, which it is compiled in.
  (n-call k-conv)
  ;; The text a `stage` checks (`docs/research/eval.md`): the module's type,
  ;; the effect and the type it is checked at, printed, which `%fx26-stage`
  ;; is given with it, for the checker that runs then.
  (n-staged string string string))
;; Each keyed by the expression (its identity, `k-at`).
(define-type k-fact (productof (1 k-at) (2 k-noted)))
(define-type k-facts (listof k-fact acyclic))
;; Each `with` checked, its identity, and its module's values its body names,
;; with their positions in the module, newest first: a `with`'s body sees
;; them, once checking has found them; a re-export, of one value, binds one.
(define-type k-with-noted (productof (1 k-at) (2 k-names) (3 k-ids)))
(define-type k-with-list (listof k-with-noted acyclic))
;; While a module's order is checked (`check-modorder.fx`): each earlier
;; item whose value is a module as written, and its values' names, which a
;; `with` of it not checked yet binds.
(define-type k-hazard-list (listof (productof (1 symbol) (2 k-names)) acyclic))
;; Each module given where a type of fewer values, or the same in another
;; order, is wanted (`k-reshape-at`): which, and for each value that type
;; has, its position in the module given. Made into a module of that layout.
;; Where each value is taken from: value `k` of the module given, or value
;; `j` of the module that is its value `k` (`extend`, `include`, `hide`;
;; Rust's `Pick`).
(define-datatype k-pick (pick-value int) (pick-path int int))
(define-type k-picks (listof k-pick acyclic))
(define-type k-reshaped (productof (1 k-at) (2 k-picks)))
(define-type k-reshape-list (listof k-reshaped acyclic))
;; `with`'s `select` nodes and what each falls back to (`k-with-fallbacks`).
(define-type k-fallbacks (listof (productof (1 int) (2 int)) acyclic))
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
;; The types it names, from the files that define them.
(import check-types-types (type k-region kx))
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
   (val k-bound-since? (subr (maxeff (read @globals) (read @t) spin) (symbol int) bool))
   (val k-mark (subr (maxeff (read @globals) (read @t)) () int))
   (val k-rebind
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin) (symbol int) unit))
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
   (val k-forget-withs (subr (maxeff (alloc @t) (read @globals) (write @t)) () unit))
   (val k-lookup (subr (maxeff (read @globals) (read @t) spin) (symbol) int))
   (val k-lookup-used
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin) (symbol) int))
   (val k-bind
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
              (symbol int)
              unit))
   (val k-int int)
   (val k-bool int)
   (val k-unit int)
   (val k-hide-mark (ref int @t))
   (val k-in-built-in (ref int @t))
   (val check-built-in! (subr (maxeff (read @globals) (read @t) (write @t)) (bool) unit))
   (val k-syscalls (ref bool @t))
   (val check-syscalls! (subr (maxeff (read @globals) (write @t)) (bool) unit))
   (val k-syscall-expanding (ref int @t))
   (val k-unbound (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (symbol) string))
   (val k-operator (ref k-op-mark @t))
   (val k-second-class? (subr pure (symbol) bool))
   (val k-operator? (subr (maxeff (read @globals) (read @t)) (symbol int int int) bool))
   (val k-no-operator k-op-mark)
   (val k-named-only (subr pure (symbol) string))
   (val k-fx-name (subr pure (kx) symbol))
   (val k-operator-mark (subr spin (kx) k-op-mark))
   (val k-fresh-region
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t)) (string) k-region))
   (val k-include-free (subr (maxeff (read @t) (read @globals)) (symbol k-names) k-names))
   (val k-note-with
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t)) (k-with-noted) unit))
   (val k-env
        (ref (bloblet (fields (subr pure (symbol) int)
                              (subr pure (symbol symbol) bool)
                              (arrayof (listof (pairof symbol k-stack @t) acyclic) @t)
                              int)
                      @t)
             @t))
   (val k-note-fixed
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin) (symbol) unit))
   (val k-hazard-mods (ref k-hazard-list @t))
   (val k-with-names (subr (maxeff (read @globals) (read @t)) (int int int) k-names))
   (val k-at-is? (subr pure (k-at int int int) bool))
   (val k-summary (subr (read @globals) (k-eff) int))
   (val k-param-map (ref k-params-given @t))
   (val k-param-in
        (subr (maxeff (read @globals) (read @t)) (k-params-given int symbol int) int))
   (val k-known? (subr (maxeff (read @globals) (read @t) spin) (symbol) bool))
   (val k-globals-effects (ref bool @t))
   (val k-global? (subr (maxeff (read @globals) (read @t) spin) (symbol) bool))
   (val k-fixed? (subr (maxeff (read @globals) (read @t) spin) (symbol) bool))
   (val k-module-vars (ref k-ids @t))
   (val k-select-map (ref k-selects @t))
   (val k-string int)
   (val k-char int)
   (val k-f64 int)
   (val k-symbol int)
   (val k-base (ref (listof (pairof symbol int @t) acyclic) @t))
   (val k-basic
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin) (string) unit))
   (val k-trail (ref k-names @t))
   (val k-depth (ref int @t))
   (val k-depths
        (ref (bloblet (fields (subr pure (symbol) int)
                              (subr pure (symbol symbol) bool)
                              (arrayof (listof (pairof symbol k-stack @t) acyclic) @t)
                              int)
                      @t)
             @t))
   (val k-known k-flags)
   (val k-global k-flags)
   (val k-lookup-desc
        (subr (maxeff (alloc @t) (read @globals) (read @t)) (symbol) (listof k-ds acyclic)))
   (val k-fresh (ref int @t))
   (val k-expanding (ref int @t))
   (val k-hazard-names-in (subr (read @globals) (k-hazard-list symbol) k-names))
   (val k-void int)
   (val k-find (subr (maxeff (read @globals) (read @t)) (k-bindings symbol) int))
   (val k-ids-but-last (subr (maxeff (alloc @t) (read @globals) spin) (k-ids) k-ids))
   (val k-ids-last (subr (maxeff (read @globals) spin) (k-ids) int))
   (val k-select-of (subr (maxeff (read @globals) (read @t)) (symbol symbol int) int))
   (val k-param-sel-of (subr (maxeff (read @globals) (read @t)) (int symbol int) int))
   (val k-globals-region? (subr pure (k-region) bool))
   (val k-with-depth (ref int @t))
   (val k-with-mark (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t)) (symbol) unit))
   (val k-with-unmark
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t)) (symbol) unit))
   (val k-withs-over (subr (maxeff (alloc @t) (read @globals) (read @t)) (symbol) k-names))
   (val k-with-fallbacks (ref k-fallbacks @t))
   (val k-with-selected
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
              (k-names symbol int)
              int))
   (val k-with-fallback (subr (maxeff (read @globals) (read @t)) (int) int))
   (val k-with-apps (ref k-fallbacks @t))
   (val k-with-app-of (subr (maxeff (read @globals) (read @t)) (int) int))))
