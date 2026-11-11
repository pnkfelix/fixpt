;; => 1
;; `(the (modnames …) e)`: an effect kept, `y` left out.
(define m (module (define-effect touches (maxeff (read @heap))) (define x int 1) (define y int 2)))
(define s (the (modnames x (eff touches)) m))
(with s x)
