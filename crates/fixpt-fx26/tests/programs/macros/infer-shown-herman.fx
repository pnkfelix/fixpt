;; ! inferred: (macro/addressed (bvar . (import (many (expr ...)) (rho ((path #:a) var)))) defn)
;; A refused signature inferred that shapes and facts do not say, an import into a list's tail,
;; shown in Herman's form.
(define-syntax h1
  (syntax-rules
    ((_ x . rest) (begin (define y (let ((x 1)) (list . rest))) (define z (list . rest))))))
(h1 q 1 2)
