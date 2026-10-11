;;; `arithmetic-shift` natively: in line for fixnums, left while the result
;;; stays one, right (floor) by fewer than 63; else the primitive's, a
;;; bignum past a fixnum.
(define-type ints (listof int @heap))
(define* sh (subr pure (int int) int) (lambda (x k) (arithmetic-shift x k)))
(define* shifts (subr (alloc @heap) (int) ints)
  (lambda (z)
    (list (sh 1 3) (sh -5 2) (sh 7 -1) (sh -7 -1) (sh 1 60) (sh 1 61) (sh 3 70) (sh -1 -100)
          (sh 12345 -100) (sh 1152921504606846975 1) (sh -1152921504606846976 0) (sh z 0))))
(shifts 5)
