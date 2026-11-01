;;; The types of `check-reps.fx`, its `check-reps-module`: a module file of
;;; no state, which it loads, and so may its clients (`TODO.md` §68).

;; The types these use, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(import check-types-types (type k-ids k-desc))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-test-facts.fx`, `check-program.fx`).
(define-type check-reps-sig
  (moduleof (val k-ty-rep
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int) (bytevectorof @t)))
            (val k-evidence-rep
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-desc) (bytevectorof @t)))
            (val k-rep-declined? (subr (maxeff (read @globals) (read @t) spin) () bool))
            (val k-rep-making! (subr (maxeff (read @globals) (write @t) spin) (bool) unit))
            (val k-rep-desc
                 (subr (maxeff (alloc @t) (read @globals) (read @s) (read @t) (write @t)
                               (goto @z) spin)
                       ((bytevectorof @t)) k-desc))
            (val k-rep-tys
                 (subr (maxeff (alloc @t) (read @globals) (read @s) (read @t) (write @t)
                               (goto @z) spin)
                       ((bytevectorof @t)) k-ids))
            (val k-rep-holes
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) () k-ids))
            ;; It fails as the checker does (`k-fail`), on a rep it does not take.
            (val k-rep-ty
                 (subr (maxeff (alloc @t) (read @globals) (read @s) (read @t) (write @t)
                               (goto @z) spin)
                       ((bytevectorof @t) k-ids) int))))
