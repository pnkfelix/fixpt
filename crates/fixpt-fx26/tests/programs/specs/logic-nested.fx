; Unverified
;;; Logic functions over a list of lists of `int`s, for the SMT solver:
;;; that `strip` leaves no empty list among its lists, by the definition
;;; of `empties`, which counts them. With the solver, every word verifies.
(define-type ints (listof int acyclic))
(define-type intss (listof ints acyclic))
(define empties (subr pure (intss) int)
  (letrec ((s (subr pure (intss) int)
             (lambda (xss) (if (null? xss) 0 (+ (if (null? (car xss)) 1 0) (s (cdr xss)))))))
    s))
(define strip (subr (maxeff spin (read (globals strip))) ((xss intss)) intss
                (ensures r (= (empties r) 0)))
  (lambda (xss)
    (if (null? xss)
        nil
        (if (null? (car xss)) (strip (cdr xss)) (cons (car xss) (strip (cdr xss)))))))
(strip (list (list 1 2) nil (list 3)))
