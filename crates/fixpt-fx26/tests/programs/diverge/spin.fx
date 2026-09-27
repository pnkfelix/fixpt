;;; A loop that never ends: run, it must stop at the step limit.
(define spin (subr pure (int) int) (lambda (n) (spin n)))
(spin 1)
