; Rejected: a generative type is not data (reading one in would be `up`).
(define-generative ty-id int)
(define same (poly ((t data)) (subr pure (t) t)) (lambda (x) x))
(same (up-ty-id 1))
