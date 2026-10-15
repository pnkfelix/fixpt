;;; The types of `regcode-modules.fx`, its `regcode-modules-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(hide (define compile-types (load-module "fx26:compile-types.fx")))
(define-type cenv (select compile-types cenv))
(hide (define regcode-types (load-module "fx26:regcode-types.fx")))
(define-type renv (select regcode-types renv))
;; Where names are, to register code and to the cellular compiler.
(define-type r-scopes (pairof renv cenv @k))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`regcode-core.fx`).
;; The types it names, from the files that define them.
(hide (define compile-exps-types (load-module "fx26:compile-exps-types.fx")))
(import compile-exps-types (type c-mslots c-mvals c-waits))
(hide (define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
(define-type exp (select parser-types exp))
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(define-type k-ids (select check-types-types k-ids))
(hide (define check-env-types (load-module "fx26:check-env-types.fx")))
(import check-env-types (type k-pick k-picks))
(import regcode-types (type rargs rgen rints))
(define-type syms (select compile-types syms))
(define-type regcode-modules-sig
  (moduleof (val r-slots-oldest
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (rints rargs)
                       rargs))
            (val r-module-slots
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (rgen c-mvals)
                       c-mslots))
            (val r-module-own
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (symbol r-scopes c-mslots exp int)
                       r-scopes))
            (val r-give-waiting
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (rgen c-waits int)
                       unit))
            (val r-with-fields
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (rgen symbol renv syms k-ids r-scopes)
                       r-scopes))
            (val r-args-reversed
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (rargs rargs)
                       rargs))
            (val r-reshape-fields
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (rgen int k-picks rargs)
                       rargs))))
