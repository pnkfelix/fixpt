;;; The signature of `check-program.fx`, its `check-program-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-plan.fx`).
(define-type check-program-sig
  (moduleof (val k-syms=?
                 (subr (read @globals)
                       ((listof symbol acyclic) (listof symbol acyclic))
                       bool))))
