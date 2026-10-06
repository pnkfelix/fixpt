;;; A map over a lambda, as `map-specialized.fx`, where the copy's body and
;;; the lambda's call small globals, inlined in the copy: `inc2`, whose body
;;; inlines `dbl` in turn, and `dbl`.
(define* dbl (subr pure (int) int) (lambda (x) (+ x x)))
(define* inc2 (subr pure (int) int) (lambda (x) (+ (dbl x) 1)))
(define-type step (subr (read (globals dbl)) (int) int))
(define* map2
  (subr (maxeff (read @l) (alloc @l) spin) (step (listof int @l)) (listof int @l))
  (lambda (f xs) (if (null? xs) nil (cons (inc2 (f (car xs))) (map2 f (cdr xs))))))
(define* total (subr (maxeff (read @l) spin) ((listof int @l) int) int)
  (lambda (xs acc) (if (null? xs) acc (total (cdr xs) (+ acc (car xs))))))
(define* test (subr (maxeff (alloc @l) (read @l) spin) (int) int)
  (lambda (k) (total (map2 (lambda ((x int)) (dbl (+ x k))) (list 1 2 3)) 0)))
(test 10)
