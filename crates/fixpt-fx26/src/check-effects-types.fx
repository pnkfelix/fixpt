;;; The signature of `check-effects.fx`, its `check-effects-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-atom (select check-types-types k-atom))
(define-type k-eff (select check-types-types k-eff))
(define-type k-region (select check-types-types k-region))
(define-type check-effects-sig
  (moduleof (val k-atom-region (subr (read @globals) (k-atom) k-region))
            (val k-one (subr (alloc @t) (k-atom) k-eff))
            (val k-insert
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (k-atom k-eff)
                       k-eff))
            (val k-union
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (k-eff k-eff)
                       k-eff))
            (val k-region=? (subr (maxeff (read @globals) spin) (k-region k-region) bool))
            (val k-eff=? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-eff) bool))
            (val k-atom-rank (subr pure (k-atom) int))
            (val k-contains?
                 (subr (maxeff (read @globals) (read @t) spin) (k-eff k-atom) bool))
            (val k-covered?
                 (subr (maxeff (read @globals) (read @t) spin) (k-eff k-atom) bool))
            (val k-within?
                 (subr (maxeff (read @globals) (read @t) spin) (k-eff k-eff) bool))
            (val k-has-region? (subr (read @globals) (k-atom) bool))
            (val k-atom-with (subr (read @globals) (k-atom k-region) k-atom))))
