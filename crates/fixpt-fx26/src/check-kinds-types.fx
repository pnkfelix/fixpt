;;; The signature of `check-kinds.fx`, its `check-kinds-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-infer.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-desc (select check-types-types k-desc))
(define-type check-kinds-sig
  (moduleof (val k-generative-fun
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int int)
                       int))
            (val k-desc-of-kind?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-desc int)
                       bool))))
