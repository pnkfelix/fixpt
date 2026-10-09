;;; The signature of `check-proofs.fx`, its `check-proofs-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-lift.fx`, `compile-plan.fx`,
;; `compile-state.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-lemma (select check-types-types k-lemma))
(define-type k-names (select check-types-types k-names))
(define-type kx (select check-types-types kx))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type syns-a (select parser-types syns-a))
(define-type check-proofs-sig
  (moduleof (val k-syms=?
                 (subr (read @globals)
                       ((listof symbol acyclic) (listof symbol acyclic))
                       bool))
            (val k-standard
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syns-a)
                       unit))
            (val k-bind-signature
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       unit))
            (val k-names-meet?
                 (subr (maxeff (read @globals) (read @t)) (k-names k-names) bool))
            (val k-check-proof
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-lemma symbol kx)
                       unit))))
