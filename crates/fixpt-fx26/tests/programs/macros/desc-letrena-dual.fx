;; => 3
;; A place a use names (`(rho (A place))`): a description, and the value of
;; it, in the body's scope.
;; As named: ((p dvar) (body (in expr p p-value)))
(define-syntax with-arena
  (dvar (import expr (rho (A place))))
  (syntax-rules ()
    ((_ p body) (letrena p body))))
(with-arena a (car (the (listof int a) (rcons a 3 nil))))
