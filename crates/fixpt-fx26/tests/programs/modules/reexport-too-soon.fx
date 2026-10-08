;; ! `x` uses `m`, defined after it
;; A re-export from a module made after it is still too soon.
(define n (module (define x (with m x)) (define m (module (define x int 1)))))
(with n x)
