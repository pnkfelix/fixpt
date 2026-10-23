;;; The signature of `check-specs.fx`, its `check-specs-module`, as its
;;; clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-read-descs.fx`).
;; The types it names, from the files that define them.
(hide (define check-read-types (load-module "fx26:check-read-types.fx")))
(define-type k-syns (select check-read-types k-syns))
(hide (define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
(define-type syn (select parser-types syn))
(define-type check-specs-sig
  (moduleof (val k-spec-clause? (subr (read @globals) (syn) bool))
            (val k-specified
                 (subr (maxeff (alloc @t) (goto @z) (read @globals) (read @s) (read @t) (write @t)
                               spin)
                       (int syn k-syns)
                       int))))
