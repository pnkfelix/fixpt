(define lib (module (define x int 1)))
(import-with-syntax lib)
x
