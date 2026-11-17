;; => 3
;; A path's effects and transparent types, selected.
(define mid (module (define a (module (define-effect e spin) (define-type n int)))))
(define f (the (subr (select (with mid a) e) () (select (with mid a) n)) (lambda () 3)))
(f)
