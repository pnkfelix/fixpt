;;; Bytes read in line natively (TODO.md §84): a bytevector of `n` bytes
;;; filled, summed, its length; and a read past its end, which the primitive
;;; refuses (-1 here, the index checked first by the program itself).
(define* fill! (subr (maxeff (read @b) (write @b) spin) ((bytevectorof @b) int) unit)
  (lambda (bv i)
    (if (>= i (bytevector-length bv))
        #u
        (begin (bytevector-u8-set! bv i (int->u8 (* i 7))) (fill! bv (+ i 1))))))
(define* total (subr (maxeff (read @b) spin) ((bytevectorof @b) int int) int)
  (lambda (bv i acc)
    (if (>= i (bytevector-length bv)) acc (total bv (+ i 1) (+ acc (bytevector-u8-ref bv i))))))
(define* bytevector-sum (subr (maxeff (alloc @b) (read @b) (write @b) spin) (int) int)
  (lambda (n)
    (let ((bv (the (bytevectorof @b) (make-bytevector n (int->u8 0)))))
      (begin (fill! bv 0) (+ (* 1000 (total bv 0 0)) (bytevector-length bv))))))
(bytevector-sum 1000)
