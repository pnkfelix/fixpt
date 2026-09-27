; Rejected: a `mu` whose body is only its own name describes no type.
(define bad (subr pure ((mu t t)) int) (lambda (x) 0))
