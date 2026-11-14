; Rejected: a parameter kept in a reference cannot be covariant.
(define-generative (cell (t type +)) (ref t @r) #:seal up-cell #:unseal down-cell)
