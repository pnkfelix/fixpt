; Unverified
;;; `logic-bools.fx`'s `all?`, of a word that does not keep it: its first
;;; element negated. With the SMT solver, false, of a list of `bool`s it
;;; found.
(define-type bools (listof bool acyclic))
(define all? (subr pure (bools) bool)
  (letrec ((a (subr pure (bools) bool) (lambda (xs) (or (null? xs) (and (car xs) (a (cdr xs)))))))
    a))
(define flip (subr pure ((xs : bools)) bools (ensures r (implies (all? xs) (all? r))))
  (lambda (xs) (if (null? xs) xs (cons (not (car xs)) (cdr xs)))))
(flip (list #f #t))
