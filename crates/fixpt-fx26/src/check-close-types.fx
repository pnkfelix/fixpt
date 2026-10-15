;;; The signature of `check-close.fx`, its `check-close-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
;; The types it names, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(import check-types-types (type k-eff k-region k-te kx))
(define-type check-close-sig
  (moduleof (val k-close-region
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx string int int k-eff int int)
                       k-te))
            (val k-note-effect
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (kx k-eff)
                       unit))
            (val k-frozen
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t))
                       (kx k-eff)
                       k-eff))
            (val k-frozen-result
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int k-region bool int int int)
                       int))))
