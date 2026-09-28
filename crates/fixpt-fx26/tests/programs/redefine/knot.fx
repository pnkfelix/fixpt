;;; A redefinition that would reach itself through a global: `f` would call
;;; `h`, which calls `f`. A procedure typed `pure` must end, so it is
;;; refused; with `spin` in its type it would be accepted.
(define* f (subr pure (int) int) (lambda (n) n))
(define* h (subr pure (int) int) (lambda (n) (f n)))
(define* f (subr pure (int) int) (lambda (n) (h (+ n 1))))
(f 1)
