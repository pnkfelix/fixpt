;;; The signature of `check-mask.fx`, its `check-mask-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-eff (select check-types-types k-eff))
(define-type kx (select check-types-types kx))
;; The types it names, from the files that define them.
(define-type k-atom (select check-types-types k-atom))
(define-type check-mask-sig
  (moduleof (val k-mask
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (kx k-eff int)
                       k-eff))
            (val k-frozen-atom? (subr (read @globals) (k-atom) bool))))
