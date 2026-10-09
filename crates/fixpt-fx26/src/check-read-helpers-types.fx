;;; The signature of `check-read-helpers.fx`, its `check-read-helpers-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-dependent.fx`, `check-infer.fx`,
;; `check-kinds.fx`, `check-module-rules.fx`, `check-modules.fx`,
;; `check-rules.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-binders (select check-types-types k-binders))
(define-type k-desc (select check-types-types k-desc))
(define-type k-descs (select check-types-types k-descs))
(define-type k-ids (select check-types-types k-ids))
(define-type k-parts (select check-types-types k-parts))
;; The types it names, from the files that define them.
(define-type k-names (select check-types-types k-names))
(define check-read-types (load-module "fx26:check-read-types.fx"))
(define-type k-params (select check-read-types k-params))
(define check-env-types (load-module "fx26:check-env-types.fx"))
(define-type k-scope (select check-env-types k-scope))
(define-type k-selects (select check-env-types k-selects))
(define-type k-syns (select check-read-types k-syns))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type syn (select parser-types syn))
(define-type check-read-helpers-sig
  (moduleof (val k-lam
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-binders k-desc)
                       int))
            (val k-binders-as-descs
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-binders)
                       k-descs))
            (val k-parts-reversed
                 (subr (maxeff (alloc @t) (read @globals)) (k-parts k-parts) k-parts))
            (val k-part-onto (subr (alloc @t) (symbol int k-parts) k-parts))
            (val k-ids-then (subr (maxeff (alloc @t) (read @globals)) (k-ids int) k-ids))
            (val k-desc-kids (subr (maxeff (alloc @t) (read @globals)) (k-descs) k-ids))
            (val k-ty-kids
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (int) k-ids))
            (val k-dlambda-empty string)
            (val k-moduleof-usage string)
            (val k-abs-usage string)
            (val k-no-name symbol)
            (val k-fresh-named
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-names k-ids)
                       k-binders))
            (val k-binders-as-scope
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-binders)
                       k-scope))
            (val k-params-names (subr (read @globals) (k-params) k-names))
            (val k-params-kinds (subr (read @globals) (k-params) k-ids))
            (val k-fun-bound?
                 (subr (maxeff (alloc @t) (read @globals) (read @t)) (string) bool))
            (val k-parse-select
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn k-syns)
                       int))
            (val k-arity-fail
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int int int syn)
                       void))
            (val k-gives-fail
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int int string syn)
                       void))
            (val k-not-giving
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int string syn)
                       void))
            (val k-gen-eta
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int k-binders)
                       int))
            (val k-ctor-eta
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (string k-params)
                       int))
            (val k-component-names
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn string)
                       k-names))
            (val k-names-once
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-names k-names syn)
                       k-names))
            (val k-abs-bound
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-names int k-parts)
                       k-parts))
            (val k-effect-shaped?
                 (subr (maxeff (alloc @t) (read @globals) (read @s) (read @t) spin)
                       (syn)
                       bool))
            (val k-selects-reversed
                 (subr (maxeff (alloc @t) (read @globals)) (k-selects k-selects) k-selects))
            (val k-param-name
                 (subr (maxeff (alloc @t) (read @globals) (read @s) (read @t) spin)
                       (syn)
                       k-names))
            (val k-param-selects
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-selects k-names)
                       k-selects))
            (val k-all-unnamed? (subr (maxeff (read @globals) spin) (k-names) bool))))
