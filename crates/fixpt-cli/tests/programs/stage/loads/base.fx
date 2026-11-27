(define-generative id int #:seal up-id #:unseal down-id)
(define make-id (subr pure (int) id) (lambda (n) (up-id n)))
(define id-number (subr pure (id) int) (lambda (i) (down-id i)))
