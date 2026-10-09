;;; The signature of `check-facts.fx`, its `test-facts`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-synth.fx`).
;; The types it names, from the files that define them.
(define check-test-facts-types (load-module "fx26:check-test-facts-types.fx"))
(define-type k-branch-facts (select check-test-facts-types k-branch-facts))
(define-type k-fact-list (select check-test-facts-types k-fact-list))
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type kx (select check-types-types kx))
(define-type check-facts-sig
  (moduleof (val k-bool-lit? (subr (read @globals) (kx bool) bool))
            (val k-test-facts
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (kx)
                       k-branch-facts))
            (val k-with-facts (subr (read @globals) (k-fact-list k-fact-list) k-fact-list))))
