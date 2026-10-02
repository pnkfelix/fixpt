;; => 6
;; A transparent type: outside, the type it is defined as.
(define n (module (define-type num int) (define x num 5)))
(with n (+ x 1))
