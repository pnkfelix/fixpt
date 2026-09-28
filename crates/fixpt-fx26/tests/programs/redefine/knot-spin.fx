;;; The same with `spin`: accepted; `h`, typed `pure`, cannot call it, and
;;; is broken.
(define* f (subr pure (int) int) (lambda (n) n))
(define* h (subr pure (int) int) (lambda (n) (f n)))
(define* f (subr spin (int) int) (lambda (n) (h (+ n 1))))
(define* h (subr spin (int) int) (lambda (n) (f n)))
