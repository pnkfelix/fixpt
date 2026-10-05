;; => 120
;; A module's typed lambda definition sees its own name, as a typed `define`
;; of a lambda does at the top level (`DONE.md` §37): no `define-rec` of
;; one. Its calls of itself are direct, checked to end as a `define-rec`'s.
(define m (module
  (define fact (subr spin (int) int) (lambda (n) (if (= n 0) 1 (* n (fact (- n 1))))))))
(with m (fact 5))
