;;; The types of `check-holds.fx`, its `check-holds-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-region (select check-types-types k-region))
(define table-types (load-module "fx26:table-types.fx"))
(define-type table (select table-types table))
;; Regions storage is kept in, for `k-knot-in`.
(define-type k-kept (listof k-region acyclic))
(define-type k-knot (listof (pairof k-region int @t) acyclic))
;; The types a search for a knot has met, each with what it found kept.
(define-type k-kept-seen (listof (pairof int k-kept @t) acyclic))
;; By type: the kept sets met at it, as the Rust checker's set of pairs.
(define-type k-kseen (table int k-kept-seen @t))
;; The types a walk has met: whether `t` is one, and if not, it is now.
(define-type k-seen (table int bool @t))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
(define-type check-holds-sig
  (moduleof (val k-no-knot
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int int int)
                       unit))
            (val k-id-hash (subr pure (int) int))
            (val k-id=? (subr pure (int int) bool))))
