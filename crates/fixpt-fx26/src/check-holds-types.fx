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
;; The types it names, from the files that define them.
(define-type k-descs (select check-types-types k-descs))
(define-type k-ids (select check-types-types k-ids))
;; The types it names, from the files that define them.
(define-type k-desc (select check-types-types k-desc))
(define-type k-eff (select check-types-types k-eff))
(define-type k-regions (select check-types-types k-regions))
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
            (val k-id=? (subr pure (int int) bool))
            (val k-ds-types
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (k-descs) k-ids))
            (val k-new-seen (subr (maxeff (alloc @t) (read @globals)) () k-seen))
            (val k-seen?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-seen int)
                       bool))
            (val k-fun-kind
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       int))
            (val k-d-types (subr (maxeff (read @globals) (read @t) spin) (k-desc) k-ids))
            (val k-frozen? (subr pure (k-region) bool))
            (val k-flip (subr pure (int) int))
            (val k-reg-is? (subr pure (k-region int) bool))
            (val k-eff-var? (subr (maxeff (read @globals) (read @t)) (k-eff int) bool))
            (val k-eff-region-var?
                 (subr (maxeff (read @globals) (read @t)) (k-eff int) bool))
            (val k-d-regions
                 (subr (maxeff (read @globals) (read @t) spin) (k-desc) k-regions))
            (val k-d-effects
                 (subr (maxeff (read @globals) (read @t) spin)
                       (k-desc)
                       (listof k-eff acyclic)))
            (val k-eff-app-var?
                 (subr (maxeff (read @globals) (read @t) spin) (k-eff int) bool))
            (val k-regions-name? (subr (read @globals) (k-regions int) bool))
            (val k-effs-name?
                 (subr (maxeff (read @globals) (read @t)) ((listof k-eff acyclic) int) bool))))
