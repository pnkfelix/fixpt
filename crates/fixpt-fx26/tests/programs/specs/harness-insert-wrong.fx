; Unverified
;;; The same harness, of an `insert` that puts an element first where it is
;;; no less than the head: `fixpt test` finds the input that shows it.
(define-type ints (listof int @heap))
(define sorted? (subr (maxeff spin (read @heap) (read (globals sorted?))) (ints) bool)
  (lambda (xs)
    (or (null? xs)
        (or (null? (cdr xs)) (and (<= (car xs) (car (cdr xs))) (sorted? (cdr xs)))))))
(define insert
  (subr (maxeff spin (read @heap) (alloc @heap) (read (globals insert))) (int ints) ints)
  (lambda (e xs)
    (if (null? xs)
        (cons e nil)
        (if (<= (car xs) e) (cons e xs) (cons (car xs) (insert e (cdr xs)))))))
(define insert-keeps-sorted
  (subr (maxeff spin (read @heap) (alloc @heap) (read (globals sorted? insert))) (int ints) unit)
  (lambda (e xs) (begin (assume (sorted? xs)) (assert (sorted? (insert e xs))))))
(insert-keeps-sorted 3 (list 1 2 4))
