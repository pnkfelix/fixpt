;;; The signature of `check-kinds.fx`, its `check-kinds-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-infer.fx`).
(define-type check-kinds-sig
  (moduleof (val k-generative-fun
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int int)
                       int))))
