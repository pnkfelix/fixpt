;;; The signature of `check-binders.fx`, its `check-binders-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-facts.fx`, `check-rules.fx`,
;; `check-synth.fx`, `check-test-facts.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-binders (select check-types-types k-binders))
(define check-infer-types (load-module "fx26:check-infer-types.fx"))
(define-type k-bound-body (select check-infer-types k-bound-body))
(define-type k-ids (select check-types-types k-ids))
(define-type k-map (select check-types-types k-map))
(define-type k-named (select check-types-types k-named))
(define-type k-region (select check-types-types k-region))
(define-type k-solved (select check-infer-types k-solved))
(define-type kxs (select check-types-types kxs))
;; The types it names, from the files that define them.
(define-type k-desc (select check-types-types k-desc))
(define-type k-terms (select check-types-types k-terms))
(define-type check-binders-sig
  (moduleof (val k-binders-of
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (int)
                       k-bound-body))
            (val k-default-regions
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-binders k-solved)
                       unit))
            (val k-fin-region (subr (read @globals) (k-region) k-region))
            (val k-finitized
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       int))
            (val k-binding-depth
                 (subr (maxeff (read @globals) (read @t) spin) (symbol) int))
            (val k-certified-has?
                 (subr (maxeff (read @globals) (read @t)) (k-named symbol int) bool))
            (val k-sc-one-arg? (subr (read @t) (kxs) bool))
            (val k-check-bounds
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-binders k-map int int)
                       unit))
            (val k-named-since
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-ids k-ids k-ids)
                       k-ids))
            (val k-forget-nats
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-ids int int int)
                       int))
            (val k-unknown? (subr (maxeff (read @globals) (read @t)) (k-binders int) bool))
            (val k-open?
                 (subr (maxeff (read @globals) (read @t)) (k-binders k-solved int) bool))
            (val k-solve
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-solved int k-desc)
                       unit))
            (val k-one-var? (subr pure (k-terms) bool))
            (val k-finite-size-ok?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int int)
                       bool))))
