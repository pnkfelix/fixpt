;;; Native code and cellular code calling each other. A procedure calling
;;; `stay-cellular` runs as cellular code, by design: `bump`, which takes a
;;; whole continuation, is called by `sum-map`, native code, which conses in
;;; between; and `leave` throws, from native code, to a continuation that
;;; cellular code took.
(define* bump (subr (maxeff (goto @k) (comefrom @k) spin) (int) int)
  (lambda (x) (stay-cellular (+ 1 ((proj (proj (proj cwcc @k) int) (goto @k)) (lambda ((k (subr (goto @k) (int) void))) (k x)))))))
(define* sum-map (subr (maxeff (goto @k) (comefrom @k) (alloc @k) (read @k) spin) ((subr (maxeff (goto @k) (comefrom @k) spin (read (globals bump))) (int) int) (listof int @k) int) int)
  (lambda (f xs acc) (if (null? xs) acc (sum-map f (cdr xs) (+ acc (car (the (listof int @k) (cons (f (car xs)) nil))))))))
(define* upto (subr (maxeff (alloc @k) spin) (int) (listof int @k))
  (lambda (n) (if (= n 0) nil (cons n (upto (- n 1))))))
(define leave (subr (goto @k) (int (subr (goto @k) (int) void)) int)
  (lambda (n k) (+ 1 (k n))))
(sum-map bump (upto 100) 0)
(stay-cellular ((proj (proj (proj cwcc @k) int) (maxeff (goto @k) (comefrom @k) (read (globals leave)))) (lambda ((k (subr (goto @k) (int) void))) (leave 42 k))))
