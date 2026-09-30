;;; Flat arrays (`flatarrayof`, Q6): made by a layout, each element kept raw
;;; as its type says; read and written by operations polymorphic in the
;;; element type, since an array says what it holds. `reverse!` is written
;;; once, for any of them. (Integers' flat arrays: `native/flat-ints.fx`,
;;; since the evaluator has no fixed-width integers.)
(define-type f64s (flatarrayof f64 @heap))
(define* reverse! (poly ((t type) (r region))
                    (subr (maxeff (read r) (write r) spin) ((flatarrayof t r) int int) unit))
  (lambda (a i j)
    (if (>= i j)
        #u
        (let ((x (flatarray-ref a i)))
          (begin (flatarray-set! a i (flatarray-ref a j)) (flatarray-set! a j x)
                 (reverse! a (+ i 1) (- j 1)))))))
(define* f64-sum (subr (maxeff (read @heap) spin) (f64s int f64) f64)
  (lambda (a i acc)
    (if (= i (flatarray-length a)) acc (f64-sum a (+ i 1) (f64+ acc (flatarray-ref a i))))))
(define* fill (subr (maxeff (read @heap) (write @heap) spin) (f64s int) unit)
  (lambda (a i)
    (if (= i (flatarray-length a))
        #u
        (begin (flatarray-set! a i (f64/ 1. (int->f64 (+ i 1)))) (fill a (+ i 1))))))
(define* doubles (subr (alloc @heap) (int) f64s) (lambda (n) (make-flatarray (f64-flat) n 0.)))
(define* singles (subr (alloc @heap) () (flatarrayof f32 @heap))
  (lambda () (make-flatarray (f32-flat) 2 (f64->f32 .5))))
(define-type strings (listof string @heap))
(define* flat (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin) (int) strings)
  (lambda (n)
    (let ((d (doubles n)) (s (singles)))
      (begin
        (fill d 0)
        (flatarray-set! s 0 (f64->f32 .25))
        (reverse! s 0 1)
        (reverse! d 0 (- n 1))
        (list (f64->string (f64-sum d 0 0.)) (f64->string (flatarray-ref d 0))
              (f32->string (flatarray-ref s 0)) (f32->string (flatarray-ref s 1))
              (int->string (flatarray-length d)))))))
(flat 100)
