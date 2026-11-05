;; ! one body cannot be each member of this `allof`: checked as a (subr pure ((moduleof
;; One body is compiled once: under these members `with`'s `a` is a value at
;; another place (`docs/research/logical-types.md` §8.5, rule 3).
(define f (allof (subr pure ((moduleof (val a int) (val b int))) int)
                 (subr pure ((moduleof (val b int) (val a int))) int))
  (lambda (m) (with m a)))
