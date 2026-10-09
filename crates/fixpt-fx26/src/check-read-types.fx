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
;; The types it names, from the files that define them.
(define-type k-ids (select check-types-types k-ids))
(define-type k-region (select check-types-types k-region))
;; The types it names, from the files that define them.
(define-type k-atom (select check-types-types k-atom))
(define-type k-regions (select check-types-types k-regions))
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
                       int))
            (val k-head (subr (maxeff (read @globals) (read @s)) (k-syns) string))
            (val k-symbol-head (subr (maxeff (read @globals) (read @s)) (k-syns) string))
            (val k-at-name? (subr pure (string) bool))
            (val k-items-or-nil
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t))
                       (syn string)
                       k-syns))
            (val k-any-typed-kind? (subr (read @globals) (k-ids) bool))
            (val k-arrow-syntax
                 (subr (maxeff (alloc @t) (read @globals) (read @s) (read @t) spin)
                       (syn)
                       k-arrow-syns))
            (val k-not-applied
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (string int)
                       string))
            (val k-ctor-params (subr (read @globals) (string) (listof k-params acyclic)))
            (val k-region-constant
                 (subr (maxeff (alloc @t) (read @globals) (read @t)) (symbol) k-region))
            (val k-frozen-into (subr (read @globals) (k-region bool) k-region))
            (val k-parse-region
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       k-region))
            (val k-parse-place
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       k-region))
            (val k-effect-named
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       k-eff))
            (val k-atom-head? (subr pure (string) bool))
            (val k-effect-selected
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn k-syns)
                       (listof k-eff acyclic)))
            (val k-globals-region
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       (listof k-regions acyclic)))
            (val k-atoms-on
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (bool k-regions)
                       k-eff))
            (val k-atom-of (subr (read @globals) (string k-region) k-atom))))
