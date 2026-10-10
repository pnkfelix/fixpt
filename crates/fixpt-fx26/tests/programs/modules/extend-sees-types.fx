;; => 2
;; `(extend e0 e1)`'s `e1` is `(with e0 e1)`, so it sees `e0`'s types and
;; effects too, as a `with` body does (`with-shadows.fx`).
(define a (module (define-effect touches (read @globals)) (define-type n int) (define x n 2)))
(define b (extend a (module (define f (subr touches () n) (lambda () x)))))
((with b f))
