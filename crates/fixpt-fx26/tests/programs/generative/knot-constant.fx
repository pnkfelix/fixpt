; Rejected: a procedure reading `@c`, kept by the representation at `@c`.
(define-generative (keeper (t type)) (ref t @c) #:seal up-keeper #:unseal down-keeper)
(define k (keeper (subr (read @c) () int)) (up-keeper (new (lambda () 1))))
