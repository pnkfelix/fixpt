; `array-length`, `%bloblet-fields` in line natively (a bloblet's trailer
; says its count of fields): empty arrays, one, many.
(define-type ints (listof int @heap))
(define* al (subr (alloc @heap) (int) ints)
  (lambda (k) (list (array-length (the (arrayof int @heap) (make-array 0 0)))
                    (array-length (the (arrayof int @heap) (make-array 1 0)))
                    (array-length (the (arrayof int @heap) (make-array 7 0)))
                    (array-length (the (arrayof int @heap) (make-array k 0))))))
(al 300)
