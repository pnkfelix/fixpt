; Rejected: a generative type is not data (reading one in would be `up`).
(define-generative ty-id int #:seal up-ty-id #:unseal down-ty-id)
(define same (poly ((t data)) (subr pure (t) t)) (lambda (x) x))
(same (up-ty-id 1))
