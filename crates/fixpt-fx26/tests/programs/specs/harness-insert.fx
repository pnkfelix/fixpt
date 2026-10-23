; Unverified
;;; A harness: a procedure of `unit` result that `assert`s what it tests,
;;; here that `insert` keeps a sorted list sorted. `fixpt test` runs it on
;;; drawn elements and lists, passing over those its `assume` does not
;;; take, and finds no counterexample. The verifier leaves its `assert`
;;; open: `sorted?` is no term of the logic yet.
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
        (if (<= e (car xs)) (cons e xs) (cons (car xs) (insert e (cdr xs)))))))
(define insert-keeps-sorted
  (subr (maxeff spin (read @heap) (alloc @heap) (read (globals sorted? insert))) (int ints) unit)
  (lambda (e xs) (begin (assume (sorted? xs)) (assert (sorted? (insert e xs))))))
(insert-keeps-sorted 3 (list 1 2 4))
