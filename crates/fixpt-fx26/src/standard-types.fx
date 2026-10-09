;;; The signature of `standard.fx`, its `standard-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`regcode.fx`).
(define-type standard-sig
  (moduleof (val standard-primitive (subr pure (string) string))))
