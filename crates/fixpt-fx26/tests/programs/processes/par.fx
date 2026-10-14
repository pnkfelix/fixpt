;; => 1217
;; `par`'s branches may run at once, so they must not interfere: these
;; write arrays at regions of their own, read data no branch writes, and
;; pass a value from one to another through an I-cell, which is dataflow
;; (the one awaiting waits for the one filling).
(define xs (arrayof int @x) (make-array 3 0))
(define ys (arrayof int @y) (make-array 3 0))
(define shared (arrayof int @s) (make-array 1 7))
(define* fill (poly ((r region)) (subr (maxeff (write r) (read @s) spin) ((arrayof int r) int) int))
  (plambda ((r region))
    (lambda (a k)
      (begin (array-set! a 0 (* k (array-ref shared 0))) (array-set! a 1 k) (array-ref shared 0)))))
(define c (icell int @c) (make-icell))
(par ((p ((proj fill @x) xs 100))
      (q ((proj fill @y) ys 50))
      (r (+ 1 (icell-get c)))
      (s (begin (icell-put! c 2) 0)))
  (+ (+ (+ (array-ref xs 0) (array-ref ys 0)) (+ p q))
     (+ (+ r s) (+ (array-ref xs 1) (array-ref ys 1)))))
