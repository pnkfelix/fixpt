;; => 4
;; A template's `plambda`: its binder made fresh, in scope in its body.
(define-type a bool)
(define-syntax ident ()
  (syntax-rules ()
    ((_) (plambda ((a type)) (lambda ((x a)) x)))))
((proj (ident) int) 4)
