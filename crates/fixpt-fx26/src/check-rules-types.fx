;;; The signature of `check-rules.fx`, its `check-rules-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-eff (select check-types-types k-eff))
(define-type k-te (select check-types-types k-te))
(define-type kx (select check-types-types kx))
(define-type check-rules-sig
  (moduleof (val k-synth
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx)
                       k-te))
            (val k-check-declared
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (symbol int kx)
                       k-eff))
            (val k-star-checked
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (symbol int kx)
                       k-eff))))
