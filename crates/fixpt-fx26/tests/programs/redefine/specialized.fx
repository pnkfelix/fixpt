;;; A call specialized at a lambda, and then the procedure redefined: the
;;; call's copy of `map1` is guarded, so the redefinition is seen.
(define* map1
  (subr (maxeff (read @l) (alloc @l) spin) ((subr pure (int) int) (listof int @l)) (listof int @l))
  (lambda (f xs) (if (null? xs) nil (cons (f (car xs)) (map1 f (cdr xs))))))
(define* total (subr (maxeff (read @l) spin) ((listof int @l) int) int)
  (lambda (xs acc) (if (null? xs) acc (total (cdr xs) (+ acc (car xs))))))
(define* test (subr (maxeff (alloc @l) (read @l) spin) (int) int)
  (lambda (k) (total (map1 (lambda ((x int)) (+ x k)) (cons 1 (cons 2 (cons 3 nil)))) 0)))
(test 10)
(define* map1
  (subr (maxeff (read @l) (alloc @l) spin) ((subr pure (int) int) (listof int @l)) (listof int @l))
  (lambda (f xs) (if (null? xs) nil (cons (+ 1000 (f (car xs))) (map1 f (cdr xs))))))
(test 10)
