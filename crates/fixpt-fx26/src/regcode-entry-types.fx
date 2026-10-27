;;; The types of `regcode-entry.fx`, its `regcode-entry-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(hide (define regcode-types (load-module "fx26:regcode-types.fx")))
(define-type rgen (select regcode-types rgen))
;; A top-level definition's name and word, in a list (`c-own-now`).
(define-type rowner (listof (productof (1 symbol) (2 tword)) @k))
;; What was made, in a list; none if declined.
(define-type rgens (listof rgen @k))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-twins.fx`).
;; The types it names, from the files that define them.
(hide (define compile-types (load-module "fx26:compile-types.fx")))
(define-type cenv (select compile-types cenv))
(hide (define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
(define-type exp (select parser-types exp))
(hide (define check-subst-types (load-module "fx26:check-subst-types.fx")))
(define-type exp-params (select check-subst-types exp-params))
(import regcode-types (type rthis wcells))
(define-type regcode-entry-sig
  (moduleof (val r-standard-word
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (string int)
                       wcells))
            (val r-register-code
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (exp-params exp cenv rthis)
                       wcells))
            (val r-places (ref (listof int @k) @k))))
