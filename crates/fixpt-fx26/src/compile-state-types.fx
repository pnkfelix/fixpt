;;; The signature of `compile-state.fx`, its `compile-state-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-inline.fx`, `compile-plan.fx`,
;; `compile-programs.fx`, `compile-twins.fx`, `regcode-core.fx`,
;; `regcode-entry.fx`, `regcode-exps.fx`, `regcode-helpers.fx`, `regcode.fx`).
;; The types it names, from the files that define them.
(define compile-exps-types (load-module "fx26:compile-exps-types.fx"))
(define-type c-closing (select compile-exps-types c-closing))
(define-type c-copy-twin (select compile-exps-types c-copy-twin))
(define-type c-inlinables (select compile-exps-types c-inlinables))
(define-type c-made (select compile-exps-types c-made))
(define-type c-mslots (select compile-exps-types c-mslots))
(define-type c-mvals (select compile-exps-types c-mvals))
(define compile-types (load-module "fx26:compile-types.fx"))
(define-type c-params (select compile-types c-params))
(define-type c-spec (select compile-exps-types c-spec))
(define-type c-twin (select compile-exps-types c-twin))
(define-type c-waits (select compile-exps-types c-waits))
(define-type cenv (select compile-types cenv))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define-type mod-items (select parser-types mod-items))
(define-type patches (select compile-types patches))
(define-type syms (select compile-types syms))
(define-type compile-state-sig
  (moduleof (val c-defining (ref (listof symbol @k) @k))
            (val c-own-now (ref (listof (productof (1 symbol) (2 tword)) @k) @k))
            (val c-word-name (ref (listof string @k) @k))
            (val c-last-word (ref (listof tword @k) @k))
            (val c-prev-word (ref (listof tword @k) @k))
            (val c-module-members (ref (listof c-inlinables @k) @k))
            (val c-module-values
                 (subr (maxeff (alloc @k) (read @globals)) (mod-items) c-mvals))
            (val c-module-slots
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (c-mvals int)
                       c-mslots))
            (val c-names-any?
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (exp c-mslots)
                       bool))
            (val c-module-own
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (symbol cenv c-mslots exp int)
                       cenv))
            (val c-waits-onto
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (c-waits int patches)
                       c-waits))
            (val c-made-now (ref (listof c-made @k) @k))
            (val c-made-reuse (ref (listof c-made @k) @k))
            (val c-form-made (ref (listof c-made @k) @k))
            (val c-own-of
                 (subr (maxeff (alloc @k) (read @globals) (read @k)) (c-params syms) syms))
            (val c-made-word
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (c-params exp cenv syms)
                       (listof c-closing @k)))
            (val c-own-scope
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (syms syms cenv)
                       cenv))
            (val c-spec-now (ref (listof c-spec @k) @k))
            (val c-r-plan-ctx (ref (listof int @k) @k))
            (val c-twins (ref (listof c-twin @k) @k))
            (val c-copy-twin
                 (subr (maxeff (alloc @k) (read @globals) (read @k))
                       (c-twin c-spec int int)
                       c-twin))
            (val c-fx-name (subr (read @globals) (symbol exp) string))
            (val c-standard-name
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin) (exp cenv) string))
            (val c-quote-now
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (exp)
                       (listof wcell @k)))))
