;;; Flat arrays of the fixed-width integers (as `run/flat-arrays.fx` for
;;; floats): `u32` and `i64` elements raw, an `i64` past a fixnum among them;
;;; `reverse!` written once for any element type.
(define* reverse! (poly ((t type) (r region))
                    (subr (maxeff (read r) (write r) spin) ((flatarrayof t r) int int) unit))
  (lambda (a i j)
    (if (>= i j)
        #u
        (let ((x (flatarray-ref a i)))
          (begin (flatarray-set! a i (flatarray-ref a j)) (flatarray-set! a j x)
                 (reverse! a (+ i 1) (- j 1)))))))
(define* words (subr (alloc @heap) () (flatarrayof u32 @heap))
  (lambda () (make-flatarray (u32-flat) 3 (int->u32 7))))
(define* longs (subr (alloc @heap) () (flatarrayof i64 @heap))
  (lambda () (make-flatarray (i64-flat) 2 (int->i64 -1))))
(define-type ints (listof int @heap))
(define* flat-ints (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin) (int) ints)
  (lambda (k)
    (let ((w (words)) (v (longs)))
      (begin
        (flatarray-set! w 1 (int->u32 (- k 1)))
        (reverse! w 0 2)
        (flatarray-set! v 0 (i64* (int->i64 3037000499) (int->i64 3037000499)))
        (list (u32->int (flatarray-ref w 0)) (u32->int (flatarray-ref w 1))
              (i64->int (flatarray-ref v 0)) (i64->int (flatarray-ref v 1)))))))
(flat-ints 0)
