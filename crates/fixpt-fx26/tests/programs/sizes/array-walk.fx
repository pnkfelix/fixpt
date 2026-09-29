;;; An array's length is a `nat`, and never changes: a walk up to it ends,
;;; with no `spin`.
(define total (subr (read @a) ((arrayof int @a)) int)
  (lambda (xs)
    (letrec ((go (subr (read @a) (nat int) int)
                   (lambda (i acc)
                     (if (>= i (array-length xs)) acc (go (+ i 1) (+ acc (array-ref xs i)))))))
      (go 0 0))))
(total (the (arrayof int @a) (make-array 4 5)))
