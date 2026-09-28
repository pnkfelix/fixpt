;;; Native code and cellular code calling each other. What the native
;;; compiler declines runs as cellular code: here, a mark in tail position.
;;; `bump`, cellular for its mark, takes a whole continuation and is called
;;; by `sum-map`, native code, which conses in between; and `leave` throws,
;;; from native code, to a continuation that cellular code took.
(define key (mark-key int @k) (make-continuation-mark-key))
(define* bump (subr (maxeff (goto @k) (comefrom @k) (write @k) spin) (int) int)
  (lambda (x) (with-mark key x (lambda () (+ 1 ((proj (proj (proj cwcc @k) int) (goto @k)) (lambda ((k (subr (goto @k) (int) void))) (k x))))))))
(define* sum-map (subr (maxeff (goto @k) (comefrom @k) (alloc @k) (read @k) (write @k) spin) ((subr (maxeff (goto @k) (comefrom @k) (write @k) spin (read (globals bump key))) (int) int) (listof int @k) int) int)
  (lambda (f xs acc) (if (null? xs) acc (sum-map f (cdr xs) (+ acc (car (the (listof int @k) (cons (f (car xs)) nil))))))))
(define* upto (subr (maxeff (alloc @k) spin) (int) (listof int @k))
  (lambda (n) (if (= n 0) nil (cons n (upto (- n 1))))))
(define leave (subr (goto @k) (int (subr (goto @k) (int) void)) int)
  (lambda (n k) (+ 1 (k n))))
(sum-map bump (upto 100) 0)
(with-mark key 0 (lambda () ((proj (proj (proj cwcc @k) int) (maxeff (goto @k) (comefrom @k) (read (globals leave)))) (lambda ((k (subr (goto @k) (int) void))) (leave 42 k)))))
