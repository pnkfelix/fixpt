;;; A map over a lambda: `map1` only calls `f`, or passes it on to itself,
;;; so a call with a lambda there runs a copy of `map1` made for it, the
;;; lambda's body where `f` is called, behind a guard that `map1` is still
;;; what the copy was made from.
(define* map1
  (subr (maxeff (read @l) (alloc @l) spin) ((subr pure (int) int) (listof int @l)) (listof int @l))
  (lambda (f xs) (if (null? xs) nil (cons (f (car xs)) (map1 f (cdr xs))))))
(define* total (subr (maxeff (read @l) spin) ((listof int @l) int) int)
  (lambda (xs acc) (if (null? xs) acc (total (cdr xs) (+ acc (car xs))))))
(define* test (subr (maxeff (alloc @l) (read @l) spin) (int) int)
  ;; cons-chain: map1 takes a list in @l
  (lambda (k) (total (map1 (lambda ((x int)) (+ x k)) (cons 1 (cons 2 (cons 3 nil)))) 0)))
(test 10)
