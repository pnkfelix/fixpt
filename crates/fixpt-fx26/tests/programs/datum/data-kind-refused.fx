; Rejected: a procedure is not data.
(define same (poly ((t data)) (subr pure (t) t)) (lambda (x) x))
(same (lambda ((x int)) x))
