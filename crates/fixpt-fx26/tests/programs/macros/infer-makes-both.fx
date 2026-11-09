;; ! this template makes an expression, and another of `m`'s definitions
(define-syntax m
  (syntax-rules ()
    ((_ x) (define x 1))
    ((_ x y) (if x y 0))))
1
