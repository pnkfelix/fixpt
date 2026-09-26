;;; An array filled with squares, then summed by a loop.
(define a (arrayof int @a) (make-array 10 0))
(define fill (subr (write @a) (int) unit)
  (lambda (i) (if (= i 10) #u (begin (array-set! a i (* i i)) (fill (+ i 1))))))
(define total (subr (read @a) (int int) int)
  (lambda (i acc) (if (= i (array-length a)) acc (total (+ i 1) (+ acc (array-ref a i))))))
(begin (fill 0) (total 0 0))
