;; => 3
;; `with` shadows (FX-91 §2.3.19): in `(with m …)`, a type or effect name
;; `m` gives is `m`'s, whatever it was outside; the innermost `with`'s first;
;; and a name bound inside the body is that binding's.
(define-type n bool)
(define-effect touches pure)
(define a (module (define-type n int) (define-effect touches (read @globals))))
(define b (module (define-type n bool)))
(define one (with a (the n 1)))
(define yes (with a (with b (the n #t))))
(define f (with a (the (subr touches () int) (lambda () 2))))
(define g (with a (module (define-type n bool) (define x n #t))))
(+ one (if (and yes (with g x)) (f) 0))
