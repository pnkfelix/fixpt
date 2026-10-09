;;; The signature of `check-proving.fx`, its `check-proving-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-te (select check-types-types k-te))
(define-type check-proving-sig
  (moduleof (val k-call-te (subr (maxeff (read @globals) (read @t) spin) (k-te) k-te))))
