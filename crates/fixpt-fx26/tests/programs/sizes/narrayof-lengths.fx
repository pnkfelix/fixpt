; Accepted: an array's length in its type, `(narrayof T n R)` (TODO.md
; §77, N5c): a `make-array` of a natural's length is an array of that
; length, kept by `the`; `array-length` is a `(nat n)` of it; and one of a
; length not known is given one of its own where it is bound.
(define five (narrayof int 5 @heap) (make-array 5 0))
(define five-again (narrayof int 5 @heap) (the (arrayof int @heap) (make-array 5 1)))
(define len (poly ((n size)) (subr pure ((narrayof int n @heap)) (nat n)))
  (plambda ((n size)) (lambda (a) (array-length a))))
(define fives (nat 5) ((proj len 5) five))
(define any-length (subr (read (globals len)) ((arrayof int @heap)) nat)
  (lambda (a) (let ((b a)) ((proj len finite) b))))
(define total (subr (maxeff (read @heap) spin) ((arrayof int @heap)) int)
  (lambda (a)
    (letrec ((go (subr (maxeff (read @heap) spin) (nat int) int)
               (lambda (i acc)
                 (if (< i (array-length a)) (go (+ i 1) (+ acc (array-ref a i))) acc))))
      (go 0 0))))
(total five-again)
