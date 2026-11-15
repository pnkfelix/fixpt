;; ! unbound variable `double`
;; What phase 1 defines is not the program's.
(begin-for-syntax (define double (subr pure (int) int) (lambda (x) (* 2 x))))
(double 3)
