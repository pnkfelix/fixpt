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
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (int) k-ids))))
