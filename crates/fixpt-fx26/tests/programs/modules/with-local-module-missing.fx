;; ! `x` uses `y`, defined after it
;; A name the local module does not give is the module's own item.
(define outer (module (define x (let ((m (module (define g int 2)))) (with m y))) (define y int 3)))
