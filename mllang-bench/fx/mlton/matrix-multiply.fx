;;; MATRIX-MULTIPLY -- a square matrix of reals times itself.
;;;
;;; From MLton's benchmark suite (benchmark/tests/matrix-multiply.sml, by
;;; Stephen Weeks), ported to FX-26. Sizes (ours): 200 by 200, not 500, 20
;;; runs, (doit 20). Answer: the product's element (0, 0), as an int: the sum
;;; of i^2 for i < 200, 2646700 (the original checks 41541750 at 500).
;;;
;;; SML's `real Array2.array`, row-major, is a flat array of `f64`s here,
;;; raw as MLton's are. `dot`'s fold carries its sum, an `f64`.

(define-type matrix (flatarrayof f64 @heap))
(define dim int 200)

(define* tabulate (subr (maxeff (alloc @heap) (write @heap) spin) (int) matrix)
  (lambda (n)
    (let ((a (the matrix (make-flatarray (f64-flat) (* n n) 0.))))
      (letrec ((fill (subr (maxeff (write @heap) spin) (int) unit)
                 (lambda (k)
                   (if (< k (* n n))
                       (begin (flatarray-set! a k (int->f64 (+ (quotient k n) (modulo k n))))
                              (fill (+ k 1)))
                       #u))))
        (begin (fill 0) a)))))

(define* dot (subr (maxeff (read @heap) spin) (matrix matrix int int int int f64) f64)
  (lambda (a1 a2 n r c i sum)
    (if (= i n)
        sum
        (dot a1 a2 n r c (+ i 1)
             (f64+ sum (f64* (flatarray-ref a1 (+ (* r n) i)) (flatarray-ref a2 (+ (* i n) c))))))))

(define* mult (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin (read (globals dot))) (matrix matrix int) matrix)
  (lambda (a1 a2 n)
    (let ((a (the matrix (make-flatarray (f64-flat) (* n n) 0.))))
      (letrec ((rows (subr (maxeff (read @heap) (write @heap) spin (read (globals dot))) (int) unit)
                 (lambda (r)
                   (if (< r n)
                       (letrec ((cols (subr (maxeff (read @heap) (write @heap) spin (read (globals dot))) (int) unit)
                                  (lambda (c)
                                    (if (< c n)
                                        (begin (flatarray-set! a (+ (* r n) c) (dot a1 a2 n r c 0 0.))
                                               (cols (+ c 1)))
                                        #u))))
                         (begin (cols 0) (rows (+ r 1))))
                       #u))))
        (begin (rows 0) a)))))

(define* doit (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin (read (globals dim tabulate mult dot))) (int) int)
  (lambda (n)
    (letrec ((loop (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin (read (globals dim tabulate mult dot)))
                         (int int) int)
               (lambda (n last)
                 (if (= n 0)
                     last
                     (let ((a (tabulate dim)))
                       (loop (- n 1) (f64->int (flatarray-ref (mult a a dim) 0))))))))
      (loop n 0))))

(doit 20)
