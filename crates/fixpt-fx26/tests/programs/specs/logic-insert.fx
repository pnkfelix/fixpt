; Unverified
;;; `logic-harness.fx`'s `insert`, its `ensures` made inductive, as `fixpt
;;; verify` asks: that the result is sorted is not enough of what the
;;; recursive call gives, so it says too what the result's first element
;;; is (`first`, total, so a function of the logic). The verifier's own
;;; prover leaves it open; with an SMT solver, which unfolds `sorted?` and
;;; `first`, every word verifies.
(define-type ints (listof int acyclic))
(define sorted? (subr pure (ints) bool)
  (letrec ((s (subr pure (ints) bool)
             (lambda (xs)
               (or (null? xs)
                   (or (null? (cdr xs)) (and (<= (car xs) (car (cdr xs))) (s (cdr xs))))))))
    s))
(define first (subr pure (ints) int) (lambda (xs) (if (null? xs) 0 (car xs))))
(define nonempty? (subr pure (ints) bool) (lambda (xs) (pair? xs)))
(define insert (subr (maxeff spin (read (globals insert))) ((e : int) (xs : ints)) ints
                 (ensures r (and (implies (sorted? xs) (sorted? r))
                                 (or (= (first r) e)
                                     (and (nonempty? xs) (= (first r) (first xs)))))))
  (lambda (e xs)
    (if (null? xs)
        (cons e nil)
        (if (<= e (car xs)) (cons e xs) (cons (car xs) (insert e (cdr xs)))))))
(insert 3 (list 1 2 4))
