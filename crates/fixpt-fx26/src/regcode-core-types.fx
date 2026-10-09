;;; The signature of `regcode-core.fx`, its `regcode-core-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`regcode-entry.fx`).
;; The types it names, from the files that define them.
(define compile-types (load-module "fx26:compile-types.fx"))
(define-type cenv (select compile-types cenv))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define regcode-types (load-module "fx26:regcode-types.fx"))
(define-type renv (select regcode-types renv))
(define-type rgen (select regcode-types rgen))
(define-type regcode-core-sig
  (moduleof (val r-exp
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (rgen exp renv cenv bool)
                       unit))))
