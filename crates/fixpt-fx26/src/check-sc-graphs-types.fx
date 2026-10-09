;;; The signature of `check-sc-graphs.fx`, its `check-sc-graphs-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-proofs.fx`, `check-rules.fx`,
;; `check-test-facts.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type kxs (select check-types-types kxs))
(define-type check-sc-graphs-sig
  (moduleof (val k-op-either? (subr pure (string string string) bool))
            (val k-sc-one? (subr (read @t) (kxs) bool))
            (val k-sc-two? (subr (maxeff (read @globals) (read @t)) (kxs) bool))))
