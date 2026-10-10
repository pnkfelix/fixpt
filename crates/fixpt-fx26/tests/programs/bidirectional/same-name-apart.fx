;; ! a (subr pure (a) a) is expected here, and this is a (subr pure (a') a')
;; Two variables of one name, `sig`'s `a` and the `plambda`'s, told apart
;; where a message shows both: the second is primed, and a line says so.
;; (Before, the two types printed alike.)
(define-type sig (poly ((a type)) (subr pure (a) a)))
(define mk (plambda ((a type)) (the sig (the (subr pure (a) a) (lambda (x) x)))))
