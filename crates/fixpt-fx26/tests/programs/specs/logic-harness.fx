; Unverified
;;; A specification that calls a procedure of the program's own: `sorted?`,
;;; `pure` (a local `letrec` over lists that are not written, so it ends),
;;; of a `bool`, is a function of the logic's. `insert` ensures it keeps a
;;; sorted list sorted; the harness, given that, is verified: its `assume`
;;; and its `assert` call `sorted?` as the `ensures` names it. `insert`'s
;;; own `ensures` is left open, as the prover knows nothing of `sorted?`
;;; but that it is a function.
(define-type ints (listof int acyclic))
(define sorted? (subr pure (ints) bool)
  (letrec ((s (subr pure (ints) bool)
             (lambda (xs)
               (or (null? xs)
                   (or (null? (cdr xs)) (and (<= (car xs) (car (cdr xs))) (s (cdr xs))))))))
    s))
(define insert (subr (maxeff spin (read (globals insert))) ((e : int) (xs : ints)) ints
                 (ensures r (implies (sorted? xs) (sorted? r))))
  (lambda (e xs)
    (if (null? xs)
        (cons e nil)
        (if (<= e (car xs)) (cons e xs) (cons (car xs) (insert e (cdr xs)))))))
(define insert-keeps-sorted
  (subr (maxeff spin (read (globals sorted? insert))) (int ints) unit)
  (lambda (e xs) (begin (assume (sorted? xs)) (assert (sorted? (insert e xs))))))
(insert-keeps-sorted 3 (list 1 2 4))
