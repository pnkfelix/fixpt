;;; The signature of `check-read-descs.fx`, its `check-read-descs-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-eff (select check-types-types k-eff))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type syn (select parser-types syn))
(define-type check-read-descs-sig
  (moduleof (val k-parse-effect
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       k-eff))
            (val k-parse-type
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       int))
            (val k-define-type
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read
                                (globals ds-rec
                                         k-ahead-filled
                                         k-ahead-take
                                         k-grounded
                                         k-note-closed
                                         k-push-desc
                                         k-set-link
                                         k-slot))
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (symbol syn int int)
                       int))
            (val k-parse-fun
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn int)
                       int))))
