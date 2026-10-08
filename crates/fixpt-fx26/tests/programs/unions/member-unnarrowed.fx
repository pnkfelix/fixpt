; Rejected: a union is not one of its members: where no test has narrowed
; it, `(union int string)` is no `int`.
(define* f (subr pure ((union int string)) int) (lambda (x) (+ x 1)))
