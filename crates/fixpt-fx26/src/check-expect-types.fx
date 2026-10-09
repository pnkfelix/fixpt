;;; The signature of `check-expect.fx`, its `check-expect-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type kx (select check-types-types kx))
(define-type check-expect-sig
  (moduleof (val k-lambda? (subr (read @globals) (kx) bool))))
