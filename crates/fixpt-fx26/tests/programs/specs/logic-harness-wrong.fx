; Unverified
;;; `logic-harness.fx` with `insert` wrong: it puts `e` first where it is
;;; the larger. The harness is verified still, given `insert`'s `ensures`,
;;; which is false: `fixpt test` shows it so.
(define-type ints (listof int acyclic))
(define sorted? (subr pure (ints) bool)
  (letrec ((s (subr pure (ints) bool)
             (lambda (xs)
               (or (null? xs)
                   (or (null? (cdr xs)) (and (<= (car xs) (car (cdr xs))) (s (cdr xs))))))))
    s))
(define insert (subr (maxeff spin (read (globals insert))) ((e int) (xs ints)) ints
                 (ensures r (implies (sorted? xs) (sorted? r))))
  (lambda (e xs)
    (if (null? xs)
        (cons e nil)
        (if (<= (car xs) e) (cons e xs) (cons (car xs) (insert e (cdr xs)))))))
(define insert-keeps-sorted
  (subr (maxeff spin (read (globals sorted? insert))) (int ints) unit)
  (lambda (e xs) (begin (assume (sorted? xs)) (assert (sorted? (insert e xs))))))
(insert-keeps-sorted 3 (list 1 2 4))
