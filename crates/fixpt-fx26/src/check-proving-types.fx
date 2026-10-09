;;; The signature of `check-proving.fx`, its `check-proving-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-te (select check-types-types k-te))
;; The types it names, from the files that define them.
(define-type k-props (select check-types-types k-props))
;; The types it names, from the files that define them.
(define-type k-names (select check-types-types k-names))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type syn (select parser-types syn))
(define-type check-proving-sig
  (moduleof (val k-call-te (subr (maxeff (read @globals) (read @t) spin) (k-te) k-te))
            (val k-props-within?
                 (subr (maxeff (read @globals) spin) (k-props k-props) bool))
            (val k-props=? (subr (maxeff (read @globals) spin) (k-props k-props) bool))
            (val k-parse-proving
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn int)
                       int))
            (val k-names-snoc
                 (subr (maxeff (alloc @t) (read @globals) spin) (k-names symbol) k-names))))
