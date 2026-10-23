;;; The signature of `check-proving.fx`, its `check-proving-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-read-descs.fx`).
;; The types it names, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(define-type k-sf (select check-types-types k-sf))
;; The types it names, from the files that define them.
(define-type k-names (select check-types-types k-names))
(hide (define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
(define-type syn (select parser-types syn))
(define-type check-proving-sig
  (moduleof (val k-parse-proving
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn int)
                       k-sf))
            (val k-names-snoc
                 (subr (maxeff (alloc @t) (read @globals) spin) (k-names symbol) k-names))))
