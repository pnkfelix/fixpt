;;; The signature of `check-modules-read.fx`, its `check-modules-read-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`, `check-proofs.fx`,
;; `check-rules.fx`).
;; The types it names, from the files that define them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-binders (select check-types-types k-binders))
(define check-modules-types (load-module "fx26:check-modules-types.fx"))
(define-type k-thunk-unit (select check-modules-types k-thunk-unit))
(define-type kx (select check-types-types kx))
(define-type check-modules-read-sig
  (moduleof (val k-push-binders
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-binders)
                       unit))
            (val k-in-loaded
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-thunk-unit int int int)
                       unit))
            (val k-resolve-exp
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (exp)
                       kx))))
