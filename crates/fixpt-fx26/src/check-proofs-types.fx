;;; The signature of `check-proofs.fx`, its `check-proofs-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-lift.fx`, `compile-plan.fx`,
;; `compile-state.fx`).
(define-type check-proofs-sig
  (moduleof (val k-syms=?
                 (subr (read @globals)
                       ((listof symbol acyclic) (listof symbol acyclic))
                       bool))))
