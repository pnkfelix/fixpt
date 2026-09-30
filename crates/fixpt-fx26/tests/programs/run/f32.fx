;;; `f32`, an immediate of its own: arithmetic rounded to binary32 at each
;;; step, not once at the end; conversions; IEEE's special values.
(define* f32-sum (subr spin (int f32) f32)
  (lambda (n acc) (if (= n 0) acc (f32-sum (- n 1) (f32+ acc (f64->f32 .1))))))
(define* f32s (subr (maxeff (alloc @heap) spin) (int) (listof string @heap))
  (lambda (n)
    (let ((third (f32/ (int->f32 1) (int->f32 3))) (big (int->f32 16777217)))
      (list (f32->string (f32-sum n (int->f32 0))) (f32->string third)
            (f64->string (f32->f64 third)) (f32->string big) (int->string (f32->int big))
            (f32->string (f32-sqrt (int->f32 2))) (f32->string (f32-round (f64->f32 2.5)))
            (if (f32< (f32/ (int->f32 0) (int->f32 0)) (int->f32 1)) "lt" "not lt")
            (f32->string (f32/ (int->f32 1) (int->f32 0))) (f32->string (f32-neg (int->f32 0)))))))
(f32s 1000)
