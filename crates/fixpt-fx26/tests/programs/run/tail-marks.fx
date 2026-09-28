;;; A mark in tail position replaces one for the same key on the
;;; continuation it returns to, so a loop that marks each time it goes
;;; round runs in constant space, and sees only the latest mark.
(define key (mark-key int @m) (make-continuation-mark-key))
(define* loop (subr (maxeff (read @m) (write @m) (alloc @m) spin) (int) (listof int @m))
  (lambda (n) (if (= n 0) (current-marks key) (with-mark key n (lambda () (loop (- n 1)))))))
(define* nested (subr (maxeff (read @m) (write @m) (alloc @m) spin) () (listof int @m))
  (lambda () (with-mark key 1 (lambda () (with-mark key 2 (lambda () (current-marks key)))))))
(the (listof int @m) (cons (car (loop 300000)) (nested)))
