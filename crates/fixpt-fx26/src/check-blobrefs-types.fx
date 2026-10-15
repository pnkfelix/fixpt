;;; The signature of `check-blobrefs.fx`, the `blobref` forms' types,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-synth.fx`).
;; The types it names, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(define-type k-region (select check-types-types k-region))
(define-type check-blobrefs-sig
  (moduleof (val k-blobref-wanted (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin) (int int int int) int))
            (val k-blobref-region (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin) (int int int int int int bool) k-region))
            (val k-blobref-length
                 (subr (maxeff (alloc @t) (goto @z) (read @globals) (read @s) (read @t) (write @t)
                               spin)
                       (int int int int)
                       int))
            (val k-blobref-element (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin) (int int int int) int))))
