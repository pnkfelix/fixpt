;;; The signature of `compile-state.fx`, its `compile-state-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-inline.fx`, `compile-plan.fx`,
;; `compile-programs.fx`, `compile-twins.fx`, `regcode-core.fx`,
;; `regcode-entry.fx`, `regcode-exps.fx`, `regcode-helpers.fx`, `regcode.fx`).
;; The types it names, from the files that define them.
(hide (define compile-exps-types (load-module "fx26:compile-exps-types.fx")))
(import compile-exps-types (type c-closing c-copy-twin c-inlinables c-made c-mslots c-mvals))
(hide (define compile-types (load-module "fx26:compile-types.fx")))
(define-type c-params (select compile-types c-params))
(import compile-exps-types (type c-spec c-twin c-waits))
(define-type cenv (select compile-types cenv))
(hide (define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
(import parser-types (type exp mod-items))
(import compile-types (type patches syms))
;; The types it names, from the files that define them.
(import compile-types (type c-this code exps))
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(define-type k-ids (select check-types-types k-ids))
(hide (define check-env-types (load-module "fx26:check-env-types.fx")))
(import check-env-types (type k-pick k-picks k-conv))
(define-type loc (select compile-types loc))
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
                       (listof wcell @k)))
            (val c-push-all
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (syms cenv int int code)
                       patches))
            (val c-self-call?
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (exp exps cenv bool)
                       bool))
            (val c-loop-stores
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (code int int)
                       unit))
            (val c-drops
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (code int)
                       unit))
            (val c-scope-name (ref (listof string @k) @k))
            (val c-bind-name (ref (listof symbol @k) @k))
            (val c-collecting (ref (listof c-inlinables @k) @k))
            (val c-note-member!
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (symbol exp cenv)
                       unit))
            (val c-give-waiting
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (c-waits int code)
                       unit))
            (val c-take
                 (poly ((t type)) (subr (maxeff (read @k) (write @k)) ((ref t @k) t) t)))
            (val c-this-of
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (syms cenv int int)
                       (listof c-this @k)))
            (val c-this-saved (subr (maxeff (read @globals) (read @k)) () c-this))
            (val c-this-enter! (subr (maxeff (read @globals) (write @k)) (c-this int) unit))
            (val c-word-base
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       ((listof string @k) syms (listof symbol @k))
                       string))
            (val c-word-symbol
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (string (listof string @k) exp)
                       symbol))
            (val c-register-twin!
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (tword c-params exp cenv (listof c-this @k) (listof symbol @k))
                       unit))
            (val c-typed-call
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (code int bool)
                       unit))
            (val c-call-in
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (code int bool k-conv)
                       unit))
            (val c-reshape-fields
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (k-picks int code)
                       unit))
            (val c-slots-load
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       ((listof int @k) code)
                       int))
            (val c-with-fields
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (syms k-ids loc cenv int int code)
                       cenv))))
