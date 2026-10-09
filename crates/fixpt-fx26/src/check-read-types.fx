;;; The types of `check-read.fx`, its `check-read-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type syn (select parser-types syn))
(define-type k-syns (listof syn acyclic))
;; `(=> (k1 … kn) k)` as written: its parameters' kinds and its result's, in
;; a list of one; none if `s` is not of that shape, or takes nothing.
(define-type k-arrow-syns (listof (pairof k-syns syn @t) acyclic))
;; The parameters' names and kinds of a type form that is also a description
;; function written alone, `listof`; none for any other name.
;; A type family's parameters: each one's name and kind.
(define-type k-params (listof (productof (1 symbol) (2 int)) acyclic))
;;; ------------------------------------------------------------ effects selected

;; Each `(select m e)` read as an effect: a variable of kind effect, one for
;; each, which `k-resolve-selects` replaces by module `m`'s effect `e`
;; (`check-modules.fx`), as the Rust checker's `effect_selects`.
(define-type k-effect-sels (listof (productof (1 symbol) (2 symbol) (3 int)) acyclic))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-items (select check-types-types k-items))
;; The types it names, from the files that define them.
(define-type k-binders (select check-types-types k-binders))
(define-type k-eff (select check-types-types k-eff))
(define-type check-read-sig
  (moduleof (val k-sfail
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t))
                       (string syn)
                       void))
            (val k-items
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t))
                       (syn string)
                       k-syns))
            (val k-name-of
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t))
                       (syn string)
                       symbol))
            (val k-effect-selects (ref k-effect-sels @t))
            (val k-subst-keep (ref int @t))
            (val k-keep-at
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       int))
            (val k-keep-set!
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int int)
                       unit))
            (val k-binders-each
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-syns)
                       k-binders))
            (val k-parse-binders
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       k-binders))
            (val k-effect-desc
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-eff)
                       int))
            (val k-parse-kind
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       int))))
