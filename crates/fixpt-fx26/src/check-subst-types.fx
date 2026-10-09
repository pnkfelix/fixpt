;;; The types of `check-subst.fx`, its `check-subst-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-effect kreads (select check-types-types kreads))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type syns-a (select parser-types syns-a))
(define table-types (load-module "fx26:table-types.fx"))
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
(define-type k-binders (select check-types-types k-binders))
(define-type k-desc (select check-types-types k-desc))
(define-type k-descs (select check-types-types k-descs))
(define-type k-ids (select check-types-types k-ids))
(define-type check-subst-sig
  (moduleof (val k-note-closed-filled
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       ((listof (productof (1 int) (2 int) (3 int)) acyclic))
                       unit))
            (val k-subst
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-map)
                       int))
            (val k-subst-region
                 (subr (maxeff (read @globals) (read @t)) (k-region k-map) k-region))
            (val k-new-smemo
                 (subr (maxeff (alloc @t) (read (globals make-table))) () k-smemo))
            (val k-subst-memo
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-map k-smemo)
                       int))
            (val k-gen-map
                 (subr (maxeff (alloc @t) (read @globals)) (k-binders k-descs) k-map))
            (val k-closed-named (ref k-ids @t))
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
                       k-desc))))
