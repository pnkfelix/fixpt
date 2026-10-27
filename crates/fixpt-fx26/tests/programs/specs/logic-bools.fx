; Unverified
;;; Logic functions over a list of `bool`s, for the SMT solver: that every
;;; element of what `trues` makes is `#t`, by `all?`'s definition. The
;;; verifier's own prover leaves it open; with the solver, it verifies.
(define-type bools (listof bool acyclic))
(define all? (subr pure (bools) bool)
  (letrec ((a (subr pure (bools) bool) (lambda (xs) (or (null? xs) (and (car xs) (a (cdr xs)))))))
    a))
(define trues (subr (maxeff spin (read (globals trues))) ((n : nat)) bools (ensures r (all? r)))
  (lambda (n) (if (= n 0) nil (cons #t (trues (- n 1))))))
(trues 3)
