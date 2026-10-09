;;; The signature of `compile-inline.fx`, its `compile-inline-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-programs.fx`).
;; The types it names, from the files that define them.
(define compile-types (load-module "fx26:compile-types.fx"))
(define-type c-params (select compile-types c-params))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define-type top (select parser-types top))
(define-type compile-inline-sig
  (moduleof (val c-plain-top
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin) (top) top))
            (val c-resolve-extracts
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin) (exp) exp))
            (val c-record-inline
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (symbol c-params exp)
                       unit))
            (val c-last-exp (ref (listof exp @k) @k))))
