;;; The signature of `check-data.fx`, its `check-data-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
(define-type check-data-sig
  (moduleof (val k-is-data?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       bool))))
