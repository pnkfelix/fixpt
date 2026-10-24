; Unverified
;;; `logic-nested.fx`'s `strip`, its test of the empty lists left out:
;;; with the SMT solver, false, of a list of lists it found.
(define-type ints (listof int acyclic))
(define-type intss (listof ints acyclic))
(define empties (subr pure (intss) int)
  (letrec ((s (subr pure (intss) int)
             (lambda (xss) (if (null? xss) 0 (+ (if (null? (car xss)) 1 0) (s (cdr xss)))))))
    s))
(define strip (subr (maxeff spin (read (globals strip))) ((xss intss)) intss
                (ensures r (= (empties r) 0)))
  (lambda (xss) (if (null? xss) nil (cons (car xss) (strip (cdr xss))))))
(strip (list (list 1 2) nil (list 3)))
