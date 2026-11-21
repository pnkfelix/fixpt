;;; The types of `check-subst.fx`, its `check-subst-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(hide (define check-env-types (load-module "fx26:check-env-types.fx")))
(define-type k-params-given (select check-env-types k-params-given))
(hide (define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
(define-type syns-a (select parser-types syns-a))
(hide (define table-types (load-module "fx26:table-types.fx")))
(define-type table (select table-types table))
;; Pairs of integers.
(define-type k-pairs (listof (pairof int int @t) acyclic))
;; The same, of the parser's trees.
(define-type exp-params (listof (productof (1 symbol) (2 syns-a)) acyclic))
;; Looking at the checker's tables (`kreads`), and building more in their
;; region.
(define-effect kmakes (maxeff kreads (alloc @t)))
;; What a substitution has made of each type it met: a table, by the type,
;; since a module's type may be large (the reader's and the parser's are).
(define-type k-smemo (table int int @t))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define-type k-map (select check-types-types k-map))
;; The types it names, from the files that define them.
(define-type k-region (select check-types-types k-region))
;; The types it names, from the files that define them.
(import check-types-types (type k-binders k-desc k-descs k-ids k-parts k-eff))
;; How a dependent module type's member is opened, as a binding of its path
;; or a comparison reads it: its type, and its types by name
;; (`k-members-closed-by`).
(define-type k-member-opener (subr kstate (symbol int) (productof (1 int) (2 k-parts))))
;; What a substitution can change of a type (`k-fv-of`): the description
;; variables in it, sorted; what else it holds that a substitution acts on
;; (`k-fv-select` and the others, or'd); and, while it is walked, the
;; depth of the shallowest type still being walked that it met again.
(define-type k-fv (productof (1 k-ids) (2 int) (3 int)))
(define-type check-subst-sig
  (moduleof (val k-fv-forget (subr (maxeff (alloc @t) (read @globals) spin (write @t)) () unit))
            (val k-note-closed-filled
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       ((listof (productof (1 int) (2 int) (3 int)) acyclic))
                       unit))
            (val k-subst
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-map)
                       int))
            (val k-subst-all
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-parts k-map)
                       k-parts))
            (val k-subst-effect
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-eff k-map)
                       k-eff))
            (val k-subst-region
                 (subr (maxeff (read @globals) spin (read @t)) (k-region k-map) k-region))
            (val k-new-smemo
                 (subr (maxeff (alloc @t) (read (globals make-table))) () k-smemo))
            (val k-subst-memo
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-map k-smemo)
                       int))
            (val k-gen-map
                 (subr (maxeff (alloc @t) (read @globals) spin) (k-binders k-descs) k-map))
            (val k-forget-closed-named
                 (subr (maxeff (alloc @t) (write @t) (read @globals) spin) () unit))
            (val k-binder-desc
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int int)
                       k-desc))
            (val k-note-closed
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       int))
            (val k-apply-fun
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-descs)
                       k-desc))
            (val k-type-parts-onto
                 (subr (maxeff (alloc @t) (read @globals) spin) (k-parts k-ids) k-ids))
            (val k-type-ids-then (subr (maxeff (alloc @t) (read @globals) spin) (k-ids int) k-ids))
            (val k-type-desc-kids (subr (maxeff (alloc @t) (read @globals) spin) (k-descs) k-ids))
            (val k-type-kids (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (int) k-ids))
            (val k-instantiate-members (subr kstate (int k-params-given) int))
            (val k-dependent-vals? (subr kstate (k-parts) bool))
            (val k-members-closed-by (subr kstate (k-parts k-member-opener) k-parts))
            (val k-members-closed (subr kstate (k-parts) k-parts))
            (val k-members-closed-as (subr kstate (k-parts k-parts) k-parts))))
