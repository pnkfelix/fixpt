;;; The signature of `check-sub-env.fx`, its `check-sub-env-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-infer.fx`, `check-proofs.fx`,
;; `check-rules.fx`, `check-synth.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-parts (select check-types-types k-parts))
(define-type check-sub-env-sig
  (moduleof (val k-part-find (subr (maxeff (read @globals) (read @t)) (k-parts symbol) int))))
