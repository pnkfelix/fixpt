;; ! `define*` `f` is a value another item uses as the module is made, at its type as written, and it reads (read (globals x))
;; The same, its body reading a global its type does not say: refused.
(define x 1)
(define mk (lambda () (module (define* f (subr pure () int) (lambda () x))
                              (define g (subr pure () int) f))))
