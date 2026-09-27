; Rejected: a procedure reading `@r`, given as a parameter kept at `@r`.
(define-generative (cell (t type) (r region)) (ref t r))
(define c (cell (subr (read @r) () int) @r) (up-cell (new (lambda () 1))))
