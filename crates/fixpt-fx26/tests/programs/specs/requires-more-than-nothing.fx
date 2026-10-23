; Refused
;;; What requires something is not a procedure that requires nothing.
(define g (subr pure ((x int)) int (requires (< 0 x))) (lambda (x) x))
(define h (subr pure () (subr pure ((x int)) int)) (lambda () g))
