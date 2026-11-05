; Rejected: a union is not one of its members: where no test has narrowed
; it, `(oneof int string)` is no `int`.
(define* f (subr pure ((oneof int string)) int) (lambda (x) (+ x 1)))
